import re
import pickle

from sklearn import tree
from subprocess import call

def get_decision_tree_classifier(X, Y):
	clf = tree.DecisionTreeClassifier(criterion='gini')
	clf = clf.fit(X, Y)
	return clf

# save decision tree classifier
def save_dtc(classifier, x_names=None, y_names=None, fpath='/tmp/tmp.pickle'):
	print('saving to: %s' % (fpath))
	with open(fpath, 'wb') as fp:
	    pickle.dump([classifier, x_names, y_names], fp)

# load decision tree classifier
def load_dtc(fpath='/tmp/tmp.pickle'):
	print('loading from: %s' % fpath)
	with open(fpath, 'rb') as fp:
		return pickle.load(fp)
