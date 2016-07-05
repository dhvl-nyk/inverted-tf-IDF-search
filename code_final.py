# Imports
# -----------------------------------------------------------------------------

import pymongo
import math
import re
import json
import pprint
import ast
import difflib
import itertools
import operator
import snowballstemmer
import collections
from collections import defaultdict
from collections import Counter, OrderedDict
from stemming.porter2 import stem
from flask import Flask, jsonify, url_for, redirect, request
from flask_pymongo import PyMongo
from pymongo import MongoClient

stemmer = snowballstemmer.stemmer('english');
stop = [i.strip() for i in open("stop.txt")]

# Step 1: Constructing TF-idf dictionary of question and answer data present in  "faq_data_map.json".
# ----------------------------------------------------------------------------------------------------
retrieve={}
tfIDFQuestions={}
tfIDFAnswers={}

def tf(word, blob):
    return blob.split().count(word) / len(blob.split())

def n_containing(word, bloblist):
    return sum(1 for blob in bloblist if word in blob.split())

def idf(word, bloblist):
    return math.log(len(bloblist) / (1 + n_containing(word, bloblist)))

def tfidf(word, blob, bloblist):
    return tf(word, blob) * idf(word, bloblist)

# Step 2: preprocessing()  removes stopword and implements "snowballstemmer" for stemming
# ----------------------------------------------------------------------------------------------------

def preprocess(sentence):
    sentence=re.compile("[^\w']").sub(" ",sentence)
    fdist = [stemmer.stemWord(word.lower()) for word in sentence.split() if word not in stop]
    return " ".join(fdist)

# Step 3: tfIDFDict() will generate inverted tf-IDF index files "indexed_file_question.txt"  and
#         "indexed_file_answer.txt" for question and answer data respectively
# ----------------------------------------------------------------------------------------------------

def tfIDFDict(bloblist,check):
    termHash = {}
    if check=="q":
        fw=open("inverted_indexed_file_question.txt","w")
    else:
        fw=open("inverted_indexed_file_answer.txt","w")
    for i, blob in enumerate(bloblist):
        token = {}
        blob=preprocess(blob)
        scores = {word: tfidf(word, blob, bloblist) for word in blob.split()}
        sorted_words = sorted(scores.items(), key=lambda x: x[1], reverse=True)
        for word, score in sorted_words[:]:
            token[word]= round(score, 2)
            if word in termHash.keys():
                termHash[word][i]=token[word]
            else:
                termHash[word] = {}
                termHash[word][i]=token[word]

    for term,occurances in sorted(termHash.items()):
        fw.write(term+ "-")
        for docId,idf in occurances.items():
            fw.write(str(docId)+":"+str(idf)+",")
        fw.write("\n")
    fw.close()
    return termHash

# Step 4: scoreCalc() will compute the similarity score of user input_string match with
#         the "faq_data_map.json" question-data and "faq_data_map.json"  answer-data.
#         It  and gives more  weightage  to question match as compared to anwer match. It will return
#         the top 5 matches
# ----------------------------------------------------------------------------------------------------

def scoreCalc(questions,answers,in_string):
    result={}
    string=preprocess(in_string)
    score=1;
    for query in string.split():
        if query in answers.keys():
            for docId,idf in answers[query].items():
                if docId not in result.keys():
                    result[docId]=round(1/idf,2);
                else:
                    result[docId]=result[docId] * round(1/idf,2)
        else:
            for partialMatchCandidate in answers.keys():
                if query in partialMatchCandidate:
                    for docId,idf in answers[partialMatchCandidate].items():
                        if docId not in result.keys():
                            result[docId]=round(1/idf,2);
                        else:
                            result[docId]=result[docId] * round(1/idf,2)

    for query in string.split():
        if query in questions.keys():
            for docId,idf in questions[query].items():
                if docId not in result.keys():
                    result[docId]=round(4/idf,2);
                else:
                    result[docId]=result[docId] * round(4/idf,2)
        else:
            for partialMatchCandidate in questions.keys():
                if query in partialMatchCandidate:
                    for docId,idf in questions[partialMatchCandidate].items():
                        if docId not in result.keys():
                            result[docId]=round(4/idf,2);
                        else:
                            result[docId]=result[docId] * round(4/idf,2)
    sorted_d = sorted(result.items(), key=operator.itemgetter(1))[::-1]
    return sorted_d[0:5]

# Step 5: preprocessInputData() will read the  input_data file "faq_data_map.json"
#         into a dictionary and  also make calls to generate the tf-IDF dictionaries of
#         all the questions  and answers data present in  the input_data file.
# ----------------------------------------------------------------------------------------------------

def preprocessInputData():
    global retrieve,tfIDFQuestions,tfIDFAnswers
    bloblistQuestion=[];
    bloblistAnswer=[];
    retrieve= collections.OrderedDict()
    with open('faq_data_map.json') as f:
        for line in f:
            line=line.strip()
            d=ast.literal_eval(line)
            totalQuestions=re.compile("[^\w']").sub(" ",d['question']) ;
            bloblistQuestion.append(totalQuestions)
            totalAnswers=re.compile("[^\w']").sub(" ",d['answer']) ;
            bloblistAnswer.append(totalAnswers)
            retrieve[d['id']]={"index":d['id'],"question":d['question'],"answer":d['answer']}
    tfIDFQuestions=tfIDFDict(bloblistQuestion,"q")
    tfIDFAnswers=tfIDFDict(bloblistAnswer,"a")

# Step 6: findTopResultsForQuery() will update the similarity score (generated by calling scoreCalc())
#         into  the final result.
# ----------------------------------------------------------------------------------------------------

def findTopResultsForQuery(in_string):
    global retrieve,tfIDFQuestions,tfIDFAnswers
    result=scoreCalc(tfIDFQuestions,tfIDFAnswers,in_string)
    result_final=[]
    for index_score in result:
        if index_score[0] in retrieve.keys():
            temp = collections.OrderedDict()
            temp=retrieve[index_score[0]]
            temp.update({"score":index_score[1]})
            result_final.append(temp)
    return result_final

# Step 7:  *    getResult() will display result in the browser.
#               Inorder to view result enter search query in browser as
#               http://127.0.0.1:5000/search?q=QUERY
#          *    getResult() connects to mongoDb instance.The user entered query is searched
#               and  later indexed in mongoDb. Thus gradually improving the retrieval response time.
# ----------------------------------------------------------------------------------------------------

user=""
def getResult(temp):
    result_final=[]
    app = Flask(__name__)
    client = MongoClient()
    collection = client.test_database.collection_name
    preprocessInputData()
    db = client.test_database
    posts = db.posts
    @app.route('/',methods=['GET'])
    def test():
        return jsonify({'message': "it works"})

    @app.route('/search',methods=['GET'])
    def returnAll():
        results=[]
        query = request.args.get('q')
        doc=db.test_database.find();
        for eachEntry in doc:
            if query in eachEntry.keys():
                results.append(eachEntry[query])
        if len(results) == 0:
            results=findTopResultsForQuery(query)
            for each in results:
                db["test_database"].insert_one({query:each})
        return jsonify({"results":results})

    @app.errorhandler(404)
    def page_not_found(error):
        return jsonify({'404 err message': "enter query using http://127.0.0.1:5000/search?q=QUERY"})

    if __name__ == '__main__':
        app.run(debug=True)

getResult("")
print("end")
