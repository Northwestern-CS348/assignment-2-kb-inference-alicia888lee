import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact])
        ####################################################
        # Student code goes here

        if type(fact) == Fact:
            first_list = [self._get_fact(fact)]
            while len(first_list) > 0:
                first_item = first_list[0]
                first_list.remove(first_list[0])

                if first_item in self.facts:
                    self.facts.remove(first_item)
                else:
                    self.rules.remove(first_item)

                #erase A from B and B from A.

                for each_fact in first_item.supports_facts:
                    for each_pair in each_fact.supported_by:
                        if each_pair[0] == first_item or each_pair[1] == first_item:
                            self._get_fact(each_fact).supported_by.remove(each_pair)
                    first_list.append(self._get_fact(each_fact))

                for each_rule in first_item.supports_rules:
                    for each_pair in each_rule.supported_by:
                        if each_pair[0] == first_item or each_pair[1] == first_item:
                            self._get_rule(each_rule).supported_by.remove(each_pair)
                    first_list.append(self._get_rule(each_rule))




class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules
        - compare first statement of rule to first statement of fact (match)
        - if match works, return something
        - instantiate lhs then right hand then add new rule to database
        - once satisfied, "delete"/ make new rule without it

        - get rid of all the links
        - use recursion to go down the links

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here


        if match(fact.statement, rule.lhs[0], None) != False:
            matched_vars = match(fact.statement, rule.lhs[0], None)
            print(matched_vars)
            new_rhs = instantiate(rule.rhs, matched_vars)
            new_lhs=[]

            for statement_loop in rule.lhs:
                new_lhs.append(instantiate(statement_loop, matched_vars))

            new_rule = Rule([new_lhs, new_rhs], [[fact, rule]])
            new_rule.lhs.remove(new_rule.lhs[0])

            if len(new_rule.lhs) == 0:
                new_rule = Fact(new_rhs, [[fact, rule]])

            if type(new_rule) == Fact:
                rule.supports_facts.append(new_rule)
                fact.supports_facts.append(new_rule)
            else:
                rule.supports_rules.append(new_rule)
                fact.supports_rules.append(new_rule)

            kb.kb_assert(new_rule)

            #(on(A, B)) => covered(B)
            #covered(B)





