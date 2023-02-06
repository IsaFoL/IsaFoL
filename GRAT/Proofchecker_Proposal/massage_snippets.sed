# TODO: Can be done at isabelle level, look at LaTeXSugar for example!
s/([^a-zA-Z{])(spec|case|while|selectp|return|do|let)([^a-zA-Z}])/\1\\isainnerkeyword{\2}\3/g;
s/\{\\isasymexists\}\\isactrlsub A/{\\isasymexistsA}/g;