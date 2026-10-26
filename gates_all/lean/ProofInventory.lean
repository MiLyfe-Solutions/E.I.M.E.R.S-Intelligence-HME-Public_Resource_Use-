import CertifiedChild8388658

set_option pp.proofs false

example : CollatzResearch.ordinaryRun 133 4835732101496250010959899 = 2153706800091972785348135 := CollatzResearch.child_r118140960795_b83_q8388658_exact_endpoint

example : ∀ u : Nat, ∃ endpoint, CollatzResearch.ordinaryRun 133 (4835732101496250010959899 + u * 2^83) = endpoint ∧ endpoint < 4835732101496250010959899 + u * 2^83 := CollatzResearch.child_r118140960795_b83_q8388658_ordinary_descent

#print CollatzResearch.child_r118140960795_b83_q8388658_representative
#print axioms CollatzResearch.child_r118140960795_b83_q8388658_representative

#print CollatzResearch.child_r118140960795_b83_q8388658_exact_trace
#print axioms CollatzResearch.child_r118140960795_b83_q8388658_exact_trace

#print CollatzResearch.child_r118140960795_b83_q8388658_arithmetic
#print axioms CollatzResearch.child_r118140960795_b83_q8388658_arithmetic

#print CollatzResearch.child_r118140960795_b83_q8388658_exact_endpoint
#print axioms CollatzResearch.child_r118140960795_b83_q8388658_exact_endpoint

#print CollatzResearch.child_r118140960795_b83_q8388658_ordinary_descent
#print axioms CollatzResearch.child_r118140960795_b83_q8388658_ordinary_descent
