import V185TrunkScan23Chunk0801

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4743862 : List Nat := [5, 1, 3, 1, 3, 1, 2, 2, 1, 2, 2]
def baseStart_4743862 : Nat := 118140960795 + 4743862 * 2 ^ 59
def prefixEnd_4743862 : Nat := 4983230072969 + 3 ^ 40 * 4743862 * 2
def baseEnd_4743862 : Nat := 2435881364599223851808383

theorem tailTrace_4743862 : CollatzResearch.WordTrace tailWord_4743862 prefixEnd_4743862 2435881364599223851808383 := by
  unfold tailWord_4743862
  simp only [CollatzResearch.WordTrace]
  refine ⟨10813928846237852248276115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115348574359870423981611893 10813928846237852248276115)
  ·
    refine ⟨16220893269356778372414173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10813928846237852248276115 16220893269356778372414173)
    ·
      refine ⟨6082834976008791889655315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16220893269356778372414173 6082834976008791889655315)
      ·
        refine ⟨9124252464013187834482973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6082834976008791889655315 9124252464013187834482973)
        ·
          refine ⟨3421594674004945437931115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9124252464013187834482973 3421594674004945437931115)
          ·
            refine ⟨5132392011007418156896673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3421594674004945437931115 5132392011007418156896673)
            ·
              refine ⟨3849294008255563617672505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5132392011007418156896673 3849294008255563617672505)
              ·
                refine ⟨2886970506191672713254379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3849294008255563617672505 2886970506191672713254379)
                ·
                  refine ⟨4330455759287509069881569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2886970506191672713254379 4330455759287509069881569)
                  ·
                    refine ⟨3247841819465631802411177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4330455759287509069881569 3247841819465631802411177)
                    ·
                      refine ⟨2435881364599223851808383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3247841819465631802411177 2435881364599223851808383)
                      ·
                        rfl

theorem cell23_4743862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_4743862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743862 prefixEnd_4743862 := by exact prefixLift 4743862
  have htrace : WordTrace (prefixWord ++ tailWord_4743862) baseStart_4743862 baseEnd_4743862 := by
    simpa [prefixWord, tailWord_4743862, baseEnd_4743862] using wordTrace_append hprefix tailTrace_4743862
  have hstable : (prefixWord ++ tailWord_4743862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743862).length < 2 ^ (prefixWord ++ tailWord_4743862).sum := by decide
  have hdescent : baseEnd_4743862 < baseStart_4743862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743884 : List Nat := [2, 2, 1, 5, 1, 1, 2, 3, 2, 2, 2]
def baseStart_4743884 : Nat := 118140960795 + 4743884 * 2 ^ 59
def prefixEnd_4743884 : Nat := 4983230072969 + 3 ^ 40 * 4743884 * 2
def baseEnd_4743884 : Nat := 2435892661173622765733281

theorem tailTrace_4743884 : CollatzResearch.WordTrace tailWord_4743884 prefixEnd_4743884 2435892661173622765733281 := by
  unfold tailWord_4743884
  simp only [CollatzResearch.WordTrace]
  refine ⟨86511831972862966864859353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115349109297150622486479137 86511831972862966864859353)
  ·
    refine ⟨64883873979647225148644515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86511831972862966864859353 64883873979647225148644515)
    ·
      refine ⟨97325810969470837722966773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64883873979647225148644515 97325810969470837722966773)
      ·
        refine ⟨9124294778387891036528135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97325810969470837722966773 9124294778387891036528135)
        ·
          refine ⟨13686442167581836554792203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9124294778387891036528135 13686442167581836554792203)
          ·
            refine ⟨20529663251372754832188305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13686442167581836554792203 20529663251372754832188305)
            ·
              refine ⟨15397247438529566124141229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20529663251372754832188305 15397247438529566124141229)
              ·
                refine ⟨5773967789448587296552961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15397247438529566124141229 5773967789448587296552961)
                ·
                  refine ⟨4330475842086440472414721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5773967789448587296552961 4330475842086440472414721)
                  ·
                    refine ⟨3247856881564830354311041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4330475842086440472414721 3247856881564830354311041)
                    ·
                      refine ⟨2435892661173622765733281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3247856881564830354311041 2435892661173622765733281)
                      ·
                        rfl

theorem cell23_4743884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_4743884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743884 prefixEnd_4743884 := by exact prefixLift 4743884
  have htrace : WordTrace (prefixWord ++ tailWord_4743884) baseStart_4743884 baseEnd_4743884 := by
    simpa [prefixWord, tailWord_4743884, baseEnd_4743884] using wordTrace_append hprefix tailTrace_4743884
  have hstable : (prefixWord ++ tailWord_4743884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743884).length < 2 ^ (prefixWord ++ tailWord_4743884).sum := by decide
  have hdescent : baseEnd_4743884 < baseStart_4743884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743890 : List Nat := [3, 2, 2, 2, 3, 1, 1, 2, 7]
def baseStart_4743890 : Nat := 118140960795 + 4743890 * 2 ^ 59
def prefixEnd_4743890 : Nat := 4983230072969 + 3 ^ 40 * 4743890 * 2
def baseEnd_4743890 : Nat := 270655082450838860250917

theorem tailTrace_4743890 : CollatzResearch.WordTrace tailWord_4743890 prefixEnd_4743890 270655082450838860250917 := by
  unfold tailWord_4743890
  simp only [CollatzResearch.WordTrace]
  refine ⟨43255970695926049188609281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115349255189136131169624749 43255970695926049188609281)
  ·
    refine ⟨32441978021944536891456961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43255970695926049188609281 32441978021944536891456961)
    ·
      refine ⟨24331483516458402668592721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32441978021944536891456961 24331483516458402668592721)
      ·
        refine ⟨18248612637343802001444541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24331483516458402668592721 18248612637343802001444541)
        ·
          refine ⟨6843229739003925750541703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18248612637343802001444541 6843229739003925750541703)
          ·
            refine ⟨10264844608505888625812555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6843229739003925750541703 10264844608505888625812555)
            ·
              refine ⟨15397266912758832938718833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10264844608505888625812555 15397266912758832938718833)
              ·
                refine ⟨11547950184569124704039125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15397266912758832938718833 11547950184569124704039125)
                ·
                  refine ⟨270655082450838860250917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11547950184569124704039125 270655082450838860250917)
                  ·
                    rfl

theorem cell23_4743890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 7].length) (baseStart_4743890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743890 prefixEnd_4743890 := by exact prefixLift 4743890
  have htrace : WordTrace (prefixWord ++ tailWord_4743890) baseStart_4743890 baseEnd_4743890 := by
    simpa [prefixWord, tailWord_4743890, baseEnd_4743890] using wordTrace_append hprefix tailTrace_4743890
  have hstable : (prefixWord ++ tailWord_4743890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743890).length < 2 ^ (prefixWord ++ tailWord_4743890).sum := by decide
  have hdescent : baseEnd_4743890 < baseStart_4743890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743903 : List Nat := [1, 1, 2, 3, 2, 4, 1, 1, 1, 7]
def baseStart_4743903 : Nat := 118140960795 + 4743903 * 2 ^ 59
def prefixEnd_4743903 : Nat := 4983230072969 + 3 ^ 40 * 4743903 * 2
def baseEnd_4743903 : Nat := 811967472435352730465231

theorem tailTrace_4743903 : CollatzResearch.WordTrace tailWord_4743903 prefixEnd_4743903 811967472435352730465231 := by
  unfold tailWord_4743903
  simp only [CollatzResearch.WordTrace]
  refine ⟨173024356932657099974660363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115349571288438066649773575 173024356932657099974660363)
  ·
    refine ⟨259536535398985649961990545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173024356932657099974660363 259536535398985649961990545)
    ·
      refine ⟨194652401549239237471492909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259536535398985649961990545 194652401549239237471492909)
      ·
        refine ⟨72994650580964714051809841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194652401549239237471492909 72994650580964714051809841)
        ·
          refine ⟨54745987935723535538857381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72994650580964714051809841 54745987935723535538857381)
          ·
            refine ⟨10264872737948162913535759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54745987935723535538857381 10264872737948162913535759)
            ·
              refine ⟨15397309106922244370303639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10264872737948162913535759 15397309106922244370303639)
              ·
                refine ⟨23095963660383366555455459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15397309106922244370303639 23095963660383366555455459)
                ·
                  refine ⟨34643945490575049833183189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23095963660383366555455459 34643945490575049833183189)
                  ·
                    refine ⟨811967472435352730465231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34643945490575049833183189 811967472435352730465231)
                    ·
                      rfl

theorem cell23_4743903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 7].length) (baseStart_4743903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743903 prefixEnd_4743903 := by exact prefixLift 4743903
  have htrace : WordTrace (prefixWord ++ tailWord_4743903) baseStart_4743903 baseEnd_4743903 := by
    simpa [prefixWord, tailWord_4743903, baseEnd_4743903] using wordTrace_append hprefix tailTrace_4743903
  have hstable : (prefixWord ++ tailWord_4743903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743903).length < 2 ^ (prefixWord ++ tailWord_4743903).sum := by decide
  have hdescent : baseEnd_4743903 < baseStart_4743903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743907 : List Nat := [1, 1, 1, 7, 1, 2, 2, 3, 5]
def baseStart_4743907 : Nat := 118140960795 + 4743907 * 2 ^ 59
def prefixEnd_4743907 : Nat := 4983230072969 + 3 ^ 40 * 4743907 * 2
def baseEnd_4743907 : Nat := 270656052358741797305075

theorem tailTrace_4743907 : CollatzResearch.WordTrace tailWord_4743907 prefixEnd_4743907 270656052358741797305075 := by
  unfold tailWord_4743907
  simp only [CollatzResearch.WordTrace]
  refine ⟨173024502824642608657805975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115349668549761739105203983 173024502824642608657805975)
  ·
    refine ⟨259536754236963912986708963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173024502824642608657805975 259536754236963912986708963)
    ·
      refine ⟨389305131355445869480063445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259536754236963912986708963 389305131355445869480063445)
      ·
        refine ⟨9124339016143262565938987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 389305131355445869480063445 9124339016143262565938987)
        ·
          refine ⟨13686508524214893848908481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9124339016143262565938987 13686508524214893848908481)
          ·
            refine ⟨10264881393161170386681361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13686508524214893848908481 10264881393161170386681361)
            ·
              refine ⟨7698661044870877790011021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10264881393161170386681361 7698661044870877790011021)
              ·
                refine ⟨2886997891826579171254133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7698661044870877790011021 2886997891826579171254133)
                ·
                  refine ⟨270656052358741797305075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2886997891826579171254133 270656052358741797305075)
                  ·
                    rfl

theorem cell23_4743907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3, 5].length) (baseStart_4743907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743907 prefixEnd_4743907 := by exact prefixLift 4743907
  have htrace : WordTrace (prefixWord ++ tailWord_4743907) baseStart_4743907 baseEnd_4743907 := by
    simpa [prefixWord, tailWord_4743907, baseEnd_4743907] using wordTrace_append hprefix tailTrace_4743907
  have hstable : (prefixWord ++ tailWord_4743907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743907).length < 2 ^ (prefixWord ++ tailWord_4743907).sum := by decide
  have hdescent : baseEnd_4743907 < baseStart_4743907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743923 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 4]
def baseStart_4743923 : Nat := 118140960795 + 4743923 * 2 ^ 59
def prefixEnd_4743923 : Nat := 4983230072969 + 3 ^ 40 * 4743923 * 2
def baseEnd_4743923 : Nat := 2435912686919148113145601

theorem tailTrace_4743923 : CollatzResearch.WordTrace tailWord_4743923 prefixEnd_4743923 2435912686919148113145601 := by
  unfold tailWord_4743923
  simp only [CollatzResearch.WordTrace]
  refine ⟨173025086392584643390388423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115350057595056428926925615 173025086392584643390388423)
  ·
    refine ⟨259537629588876965085582635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173025086392584643390388423 259537629588876965085582635)
    ·
      refine ⟨389306444383315447628373953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259537629588876965085582635 389306444383315447628373953)
      ·
        refine ⟨291979833287486585721280465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 389306444383315447628373953 291979833287486585721280465)
        ·
          refine ⟨218984874965614939290960349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291979833287486585721280465 218984874965614939290960349)
          ·
            refine ⟨82119328112105602234110131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 218984874965614939290960349 82119328112105602234110131)
            ·
              refine ⟨123178992168158403351165197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82119328112105602234110131 123178992168158403351165197)
              ·
                refine ⟨46192122063059401256686949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123178992168158403351165197 46192122063059401256686949)
                ·
                  refine ⟨8661022886823637735628803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46192122063059401256686949 8661022886823637735628803)
                  ·
                    refine ⟨12991534330235456603443205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8661022886823637735628803 12991534330235456603443205)
                    ·
                      refine ⟨2435912686919148113145601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12991534330235456603443205 2435912686919148113145601)
                      ·
                        rfl

theorem cell23_4743923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 4].length) (baseStart_4743923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743923 prefixEnd_4743923 := by exact prefixLift 4743923
  have htrace : WordTrace (prefixWord ++ tailWord_4743923) baseStart_4743923 baseEnd_4743923 := by
    simpa [prefixWord, tailWord_4743923, baseEnd_4743923] using wordTrace_append hprefix tailTrace_4743923
  have hstable : (prefixWord ++ tailWord_4743923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743923).length < 2 ^ (prefixWord ++ tailWord_4743923).sum := by decide
  have hdescent : baseEnd_4743923 < baseStart_4743923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743924 : List Nat := [2, 6, 1, 1, 2, 1, 2, 1, 7]
def baseStart_4743924 : Nat := 118140960795 + 4743924 * 2 ^ 59
def prefixEnd_4743924 : Nat := 4983230072969 + 3 ^ 40 * 4743924 * 2
def baseEnd_4743924 : Nat := 270657022266644734359233

theorem tailTrace_4743924 : CollatzResearch.WordTrace tailWord_4743924 prefixEnd_4743924 270657022266644734359233 := by
  unfold tailWord_4743924
  simp only [CollatzResearch.WordTrace]
  refine ⟨86512561432790510280587413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115350081910387347040783217 86512561432790510280587413)
  ·
    refine ⟨4055276317162055169402535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 86512561432790510280587413 4055276317162055169402535)
    ·
      refine ⟨6082914475743082754103803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4055276317162055169402535 6082914475743082754103803)
      ·
        refine ⟨9124371713614624131155705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6082914475743082754103803 9124371713614624131155705)
        ·
          refine ⟨6843278785210968098366779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9124371713614624131155705 6843278785210968098366779)
          ·
            refine ⟨10264918177816452147550169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6843278785210968098366779 10264918177816452147550169)
            ·
              refine ⟨7698688633362339110662627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10264918177816452147550169 7698688633362339110662627)
              ·
                refine ⟨11548032950043508665993941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7698688633362339110662627 11548032950043508665993941)
                ·
                  refine ⟨270657022266644734359233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11548032950043508665993941 270657022266644734359233)
                  ·
                    rfl

theorem cell23_4743924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_4743924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743924 prefixEnd_4743924 := by exact prefixLift 4743924
  have htrace : WordTrace (prefixWord ++ tailWord_4743924) baseStart_4743924 baseEnd_4743924 := by
    simpa [prefixWord, tailWord_4743924, baseEnd_4743924] using wordTrace_append hprefix tailTrace_4743924
  have hstable : (prefixWord ++ tailWord_4743924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743924).length < 2 ^ (prefixWord ++ tailWord_4743924).sum := by decide
  have hdescent : baseEnd_4743924 < baseStart_4743924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743960 : List Nat := [2, 1, 2, 3, 1, 1, 1, 5, 2, 2, 3]
def baseStart_4743960 : Nat := 118140960795 + 4743960 * 2 ^ 59
def prefixEnd_4743960 : Nat := 4983230072969 + 3 ^ 40 * 4743960 * 2
def baseEnd_4743960 : Nat := 2435931685703364468382931

theorem tailTrace_4743960 : CollatzResearch.WordTrace tailWord_4743960 prefixEnd_4743960 2435931685703364468382931 := by
  unfold tailWord_4743960
  simp only [CollatzResearch.WordTrace]
  refine ⟨86513217946725299354742667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115350957262300399139656889 86513217946725299354742667)
  ·
    refine ⟨129769826920087949032114001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86513217946725299354742667 129769826920087949032114001)
    ·
      refine ⟨97327370190065961774085501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129769826920087949032114001 97327370190065961774085501)
      ·
        refine ⟨36497763821274735665282063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97327370190065961774085501 36497763821274735665282063)
        ·
          refine ⟨54746645731912103497923095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36497763821274735665282063 54746645731912103497923095)
          ·
            refine ⟨82119968597868155246884643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54746645731912103497923095 82119968597868155246884643)
            ·
              refine ⟨123179952896802232870326965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82119968597868155246884643 123179952896802232870326965)
              ·
                refine ⟨11548120584075209331593153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 123179952896802232870326965 11548120584075209331593153)
                ·
                  refine ⟨8661090438056406998694865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11548120584075209331593153 8661090438056406998694865)
                  ·
                    refine ⟨6495817828542305249021149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8661090438056406998694865 6495817828542305249021149)
                    ·
                      refine ⟨2435931685703364468382931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6495817828542305249021149 2435931685703364468382931)
                      ·
                        rfl

theorem cell23_4743960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_4743960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743960 prefixEnd_4743960 := by exact prefixLift 4743960
  have htrace : WordTrace (prefixWord ++ tailWord_4743960) baseStart_4743960 baseEnd_4743960 := by
    simpa [prefixWord, tailWord_4743960, baseEnd_4743960] using wordTrace_append hprefix tailTrace_4743960
  have hstable : (prefixWord ++ tailWord_4743960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743960).length < 2 ^ (prefixWord ++ tailWord_4743960).sum := by decide
  have hdescent : baseEnd_4743960 < baseStart_4743960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4743997 : List Nat := [1, 4, 1, 4, 2, 1, 1, 3, 6]
def baseStart_4743997 : Nat := 118140960795 + 4743997 * 2 ^ 59
def prefixEnd_4743997 : Nat := 4983230072969 + 3 ^ 40 * 4743997 * 2
def baseEnd_4743997 : Nat := 270661187165286758180029

theorem tailTrace_4743997 : CollatzResearch.WordTrace tailWord_4743997 prefixEnd_4743997 270661187165286758180029 := by
  unfold tailWord_4743997
  simp only [CollatzResearch.WordTrace]
  refine ⟨173027785394316554028582245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115351856929544369352388163 173027785394316554028582245)
  ·
    refine ⟨32442709761434353880359171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173027785394316554028582245 32442709761434353880359171)
    ·
      refine ⟨48664064642151530820538757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32442709761434353880359171 48664064642151530820538757)
      ·
        refine ⟨9124512120403412028851017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48664064642151530820538757 9124512120403412028851017)
        ·
          refine ⟨6843384090302559021638263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9124512120403412028851017 6843384090302559021638263)
          ·
            refine ⟨10265076135453838532457395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6843384090302559021638263 10265076135453838532457395)
            ·
              refine ⟨15397614203180757798686093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10265076135453838532457395 15397614203180757798686093)
              ·
                refine ⟨5774105326192784174507285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15397614203180757798686093 5774105326192784174507285)
                ·
                  refine ⟨270661187165286758180029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5774105326192784174507285 270661187165286758180029)
                  ·
                    rfl

theorem cell23_4743997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 6].length) (baseStart_4743997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4743997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4743997 prefixEnd_4743997 := by exact prefixLift 4743997
  have htrace : WordTrace (prefixWord ++ tailWord_4743997) baseStart_4743997 baseEnd_4743997 := by
    simpa [prefixWord, tailWord_4743997, baseEnd_4743997] using wordTrace_append hprefix tailTrace_4743997
  have hstable : (prefixWord ++ tailWord_4743997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4743997).length < 2 ^ (prefixWord ++ tailWord_4743997).sum := by decide
  have hdescent : baseEnd_4743997 < baseStart_4743997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4743997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744000 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 3, 5, 2]
def baseStart_4744000 : Nat := 118140960795 + 4744000 * 2 ^ 59
def prefixEnd_4744000 : Nat := 4983230072969 + 3 ^ 40 * 4744000 * 2
def baseEnd_4744000 : Nat := 2435952224929544311882747

theorem tailTrace_4744000 : CollatzResearch.WordTrace tailWord_4744000 prefixEnd_4744000 2435952224929544311882747 := by
  unfold tailWord_4744000
  simp only [CollatzResearch.WordTrace]
  refine ⟨86513947406652842770470727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115351929875537123693960969 86513947406652842770470727)
  ·
    refine ⟨129770921109979264155706091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86513947406652842770470727 129770921109979264155706091)
    ·
      refine ⟨194656381664968896233559137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129770921109979264155706091 194656381664968896233559137)
      ·
        refine ⟨145992286248726672175169353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194656381664968896233559137 145992286248726672175169353)
        ·
          refine ⟨109494214686545004131377015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145992286248726672175169353 109494214686545004131377015)
          ·
            refine ⟨164241322029817506197065523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109494214686545004131377015 164241322029817506197065523)
            ·
              refine ⟨246361983044726259295598285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164241322029817506197065523 246361983044726259295598285)
              ·
                refine ⟨92385743641772347235849357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 246361983044726259295598285 92385743641772347235849357)
                ·
                  refine ⟨34644653865664630213443509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92385743641772347235849357 34644653865664630213443509)
                  ·
                    refine ⟨3247936299906059082510329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34644653865664630213443509 3247936299906059082510329)
                    ·
                      refine ⟨2435952224929544311882747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3247936299906059082510329 2435952224929544311882747)
                      ·
                        rfl

theorem cell23_4744000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 3, 5, 2].length) (baseStart_4744000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744000 prefixEnd_4744000 := by exact prefixLift 4744000
  have htrace : WordTrace (prefixWord ++ tailWord_4744000) baseStart_4744000 baseEnd_4744000 := by
    simpa [prefixWord, tailWord_4744000, baseEnd_4744000] using wordTrace_append hprefix tailTrace_4744000
  have hstable : (prefixWord ++ tailWord_4744000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744000).length < 2 ^ (prefixWord ++ tailWord_4744000).sum := by decide
  have hdescent : baseEnd_4744000 < baseStart_4744000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744010 : List Nat := [3, 1, 2, 1, 1, 1, 2, 6, 1, 5]
def baseStart_4744010 : Nat := 118140960795 + 4744010 * 2 ^ 59
def prefixEnd_4744010 : Nat := 4983230072969 + 3 ^ 40 * 4744010 * 2
def baseEnd_4744010 : Nat := 811985786578696424252567

theorem tailTrace_4744010 : CollatzResearch.WordTrace tailWord_4744010 prefixEnd_4744010 811985786578696424252567 := by
  unfold tailWord_4744010
  simp only [CollatzResearch.WordTrace]
  refine ⟨43257064885817364312201371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115352173028846304832536989 43257064885817364312201371)
  ·
    refine ⟨64885597328726046468302057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43257064885817364312201371 64885597328726046468302057)
    ·
      refine ⟨48664197996544534851226543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64885597328726046468302057 48664197996544534851226543)
      ·
        refine ⟨72996296994816802276839815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48664197996544534851226543 72996296994816802276839815)
        ·
          refine ⟨109494445492225203415259723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72996296994816802276839815 109494445492225203415259723)
          ·
            refine ⟨164241668238337805122889585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109494445492225203415259723 164241668238337805122889585)
            ·
              refine ⟨123181251178753353842167189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164241668238337805122889585 123181251178753353842167189)
              ·
                refine ⟨5774121149004063461351587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 123181251178753353842167189 5774121149004063461351587)
                ·
                  refine ⟨8661181723506095192027381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5774121149004063461351587 8661181723506095192027381)
                  ·
                    refine ⟨811985786578696424252567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8661181723506095192027381 811985786578696424252567)
                    ·
                      rfl

theorem cell23_4744010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_4744010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744010 prefixEnd_4744010 := by exact prefixLift 4744010
  have htrace : WordTrace (prefixWord ++ tailWord_4744010) baseStart_4744010 baseEnd_4744010 := by
    simpa [prefixWord, tailWord_4744010, baseEnd_4744010] using wordTrace_append hprefix tailTrace_4744010
  have hstable : (prefixWord ++ tailWord_4744010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744010).length < 2 ^ (prefixWord ++ tailWord_4744010).sum := by decide
  have hdescent : baseEnd_4744010 < baseStart_4744010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744043 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 6]
def baseStart_4744043 : Nat := 118140960795 + 4744043 * 2 ^ 59
def prefixEnd_4744043 : Nat := 4983230072969 + 3 ^ 40 * 4744043 * 2
def baseEnd_4744043 : Nat := 2435974304597687643645049

theorem tailTrace_4744043 : CollatzResearch.WordTrace tailWord_4744043 prefixEnd_4744043 2435974304597687643645049 := by
  unfold tailWord_4744043
  simp only [CollatzResearch.WordTrace]
  refine ⟨173029463152149903884756783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115352975434766602589837855 173029463152149903884756783)
  ·
    refine ⟨259544194728224855827135175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173029463152149903884756783 259544194728224855827135175)
    ·
      refine ⟨389316292092337283740702763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259544194728224855827135175 389316292092337283740702763)
      ·
        refine ⟨583974438138505925611054145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389316292092337283740702763 583974438138505925611054145)
        ·
          refine ⟨437980828603879444208290609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 583974438138505925611054145 437980828603879444208290609)
          ·
            refine ⟨328485621452909583156217957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 437980828603879444208290609 328485621452909583156217957)
            ·
              refine ⟨61591054022420546841790867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 328485621452909583156217957 61591054022420546841790867)
              ·
                refine ⟨92386581033630820262686301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61591054022420546841790867 92386581033630820262686301)
                ·
                  refine ⟨34644967887611557598507363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92386581033630820262686301 34644967887611557598507363)
                  ·
                    refine ⟨51967451831417336397761045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34644967887611557598507363 51967451831417336397761045)
                    ·
                      refine ⟨2435974304597687643645049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51967451831417336397761045 2435974304597687643645049)
                      ·
                        rfl

theorem cell23_4744043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 6].length) (baseStart_4744043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744043 prefixEnd_4744043 := by exact prefixLift 4744043
  have htrace : WordTrace (prefixWord ++ tailWord_4744043) baseStart_4744043 baseEnd_4744043 := by
    simpa [prefixWord, tailWord_4744043, baseEnd_4744043] using wordTrace_append hprefix tailTrace_4744043
  have hstable : (prefixWord ++ tailWord_4744043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744043).length < 2 ^ (prefixWord ++ tailWord_4744043).sum := by decide
  have hdescent : baseEnd_4744043 < baseStart_4744043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744047 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 7, 2, 2]
def baseStart_4744047 : Nat := 118140960795 + 4744047 * 2 ^ 59
def prefixEnd_4744047 : Nat := 4983230072969 + 3 ^ 40 * 4744047 * 2
def baseEnd_4744047 : Nat := 2435976358520305627995031

theorem tailTrace_4744047 : CollatzResearch.WordTrace tailWord_4744047 prefixEnd_4744047 2435976358520305627995031 := by
  unfold tailWord_4744047
  simp only [CollatzResearch.WordTrace]
  refine ⟨173029609044135412567902395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115353072696090275045268263 173029609044135412567902395)
  ·
    refine ⟨259544413566203118851853593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173029609044135412567902395 259544413566203118851853593)
    ·
      refine ⟨194658310174652339138890195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259544413566203118851853593 194658310174652339138890195)
      ·
        refine ⟨291987465261978508708335293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194658310174652339138890195 291987465261978508708335293)
        ·
          refine ⟨109495299473241940765625735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 291987465261978508708335293 109495299473241940765625735)
          ·
            refine ⟨164242949209862911148438603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109495299473241940765625735 164242949209862911148438603)
            ·
              refine ⟨246364423814794366722657905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164242949209862911148438603 246364423814794366722657905)
              ·
                refine ⟨184773317861095775041993429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246364423814794366722657905 184773317861095775041993429)
                ·
                  refine ⟨4330624637369432227546721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 184773317861095775041993429 4330624637369432227546721)
                  ·
                    refine ⟨3247968478027074170660041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4330624637369432227546721 3247968478027074170660041)
                    ·
                      refine ⟨2435976358520305627995031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3247968478027074170660041 2435976358520305627995031)
                      ·
                        rfl

theorem cell23_4744047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7, 2, 2].length) (baseStart_4744047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744047 prefixEnd_4744047 := by exact prefixLift 4744047
  have htrace : WordTrace (prefixWord ++ tailWord_4744047) baseStart_4744047 baseEnd_4744047 := by
    simpa [prefixWord, tailWord_4744047, baseEnd_4744047] using wordTrace_append hprefix tailTrace_4744047
  have hstable : (prefixWord ++ tailWord_4744047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744047).length < 2 ^ (prefixWord ++ tailWord_4744047).sum := by decide
  have hdescent : baseEnd_4744047 < baseStart_4744047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744050 : List Nat := [3, 2, 1, 2, 1, 1, 2, 4, 1, 1, 5]
def baseStart_4744050 : Nat := 118140960795 + 4744050 * 2 ^ 59
def prefixEnd_4744050 : Nat := 4983230072969 + 3 ^ 40 * 4744050 * 2
def baseEnd_4744050 : Nat := 2435977898962269116257517

theorem tailTrace_4744050 : CollatzResearch.WordTrace tailWord_4744050 prefixEnd_4744050 2435977898962269116257517 := by
  unfold tailWord_4744050
  simp only [CollatzResearch.WordTrace]
  refine ⟨43257429615781136020065401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115353145642083029386841069 43257429615781136020065401)
  ·
    refine ⟨32443072211835852015049051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43257429615781136020065401 32443072211835852015049051)
    ·
      refine ⟨48664608317753778022573577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32443072211835852015049051 48664608317753778022573577)
      ·
        refine ⟨36498456238315333516930183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48664608317753778022573577 36498456238315333516930183)
        ·
          refine ⟨54747684357473000275395275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36498456238315333516930183 54747684357473000275395275)
          ·
            refine ⟨82121526536209500413092913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54747684357473000275395275 82121526536209500413092913)
            ·
              refine ⟨61591144902157125309819685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82121526536209500413092913 61591144902157125309819685)
              ·
                refine ⟨11548339669154460995591191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61591144902157125309819685 11548339669154460995591191)
                ·
                  refine ⟨17322509503731691493386787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11548339669154460995591191 17322509503731691493386787)
                  ·
                    refine ⟨25983764255597537240080181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17322509503731691493386787 25983764255597537240080181)
                    ·
                      refine ⟨2435977898962269116257517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25983764255597537240080181 2435977898962269116257517)
                      ·
                        rfl

theorem cell23_4744050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_4744050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744050 prefixEnd_4744050 := by exact prefixLift 4744050
  have htrace : WordTrace (prefixWord ++ tailWord_4744050) baseStart_4744050 baseEnd_4744050 := by
    simpa [prefixWord, tailWord_4744050, baseEnd_4744050] using wordTrace_append hprefix tailTrace_4744050
  have hstable : (prefixWord ++ tailWord_4744050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744050).length < 2 ^ (prefixWord ++ tailWord_4744050).sum := by decide
  have hdescent : baseEnd_4744050 < baseStart_4744050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744057 : List Nat := [1, 2, 1, 3, 2, 3, 2, 3, 2, 4]
def baseStart_4744057 : Nat := 118140960795 + 4744057 * 2 ^ 59
def prefixEnd_4744057 : Nat := 4983230072969 + 3 ^ 40 * 4744057 * 2
def baseEnd_4744057 : Nat := 811993831108950196289995

theorem tailTrace_4744057 : CollatzResearch.WordTrace tailWord_4744057 prefixEnd_4744057 811993831108950196289995 := by
  unfold tailWord_4744057
  simp only [CollatzResearch.WordTrace]
  refine ⟨173029973774099184275766425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115353315849399456183844283 173029973774099184275766425)
  ·
    refine ⟨129772480330574388206824819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173029973774099184275766425 129772480330574388206824819)
    ·
      refine ⟨194658720495861582310237229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129772480330574388206824819 194658720495861582310237229)
      ·
        refine ⟨72997020185948093366338961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194658720495861582310237229 72997020185948093366338961)
        ·
          refine ⟨54747765139461070024754221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72997020185948093366338961 54747765139461070024754221)
          ·
            refine ⟨20530411927297901259282833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54747765139461070024754221 20530411927297901259282833)
            ·
              refine ⟨15397808945473425944462125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20530411927297901259282833 15397808945473425944462125)
              ·
                refine ⟨5774178354552534729173297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15397808945473425944462125 5774178354552534729173297)
                ·
                  refine ⟨4330633765914401046879973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5774178354552534729173297 4330633765914401046879973)
                  ·
                    refine ⟨811993831108950196289995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4330633765914401046879973 811993831108950196289995)
                    ·
                      rfl

theorem cell23_4744057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2, 4].length) (baseStart_4744057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744057 prefixEnd_4744057 := by exact prefixLift 4744057
  have htrace : WordTrace (prefixWord ++ tailWord_4744057) baseStart_4744057 baseEnd_4744057 := by
    simpa [prefixWord, tailWord_4744057, baseEnd_4744057] using wordTrace_append hprefix tailTrace_4744057
  have hstable : (prefixWord ++ tailWord_4744057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744057).length < 2 ^ (prefixWord ++ tailWord_4744057).sum := by decide
  have hdescent : baseEnd_4744057 < baseStart_4744057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744067 : List Nat := [1, 1, 1, 3, 4, 1, 2, 4, 1, 2, 3]
def baseStart_4744067 : Nat := 118140960795 + 4744067 * 2 ^ 59
def prefixEnd_4744067 : Nat := 4983230072969 + 3 ^ 40 * 4744067 * 2
def baseEnd_4744067 : Nat := 2435986628133395549744939

theorem tailTrace_4744067 : CollatzResearch.WordTrace tailWord_4744067 prefixEnd_4744067 2435986628133395549744939 := by
  unfold tailWord_4744067
  simp only [CollatzResearch.WordTrace]
  refine ⟨173030338504062955983630455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115353559002708637322420303 173030338504062955983630455)
  ·
    refine ⟨259545507756094433975445683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173030338504062955983630455 259545507756094433975445683)
    ·
      refine ⟨389318261634141650963168525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259545507756094433975445683 389318261634141650963168525)
      ·
        refine ⟨145994348112803119111188197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 389318261634141650963168525 145994348112803119111188197)
        ·
          refine ⟨27373940271150584833347787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145994348112803119111188197 27373940271150584833347787)
          ·
            refine ⟨41060910406725877250021681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27373940271150584833347787 41060910406725877250021681)
            ·
              refine ⟨30795682805044407937516261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41060910406725877250021681 30795682805044407937516261)
              ·
                refine ⟨5774190525945826488284299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30795682805044407937516261 5774190525945826488284299)
                ·
                  refine ⟨8661285788918739732426449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5774190525945826488284299 8661285788918739732426449)
                  ·
                    refine ⟨6495964341689054799319837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8661285788918739732426449 6495964341689054799319837)
                    ·
                      refine ⟨2435986628133395549744939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6495964341689054799319837 2435986628133395549744939)
                      ·
                        rfl

theorem cell23_4744067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 2, 3].length) (baseStart_4744067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744067 prefixEnd_4744067 := by exact prefixLift 4744067
  have htrace : WordTrace (prefixWord ++ tailWord_4744067) baseStart_4744067 baseEnd_4744067 := by
    simpa [prefixWord, tailWord_4744067, baseEnd_4744067] using wordTrace_append hprefix tailTrace_4744067
  have hstable : (prefixWord ++ tailWord_4744067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744067).length < 2 ^ (prefixWord ++ tailWord_4744067).sum := by decide
  have hdescent : baseEnd_4744067 < baseStart_4744067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744083 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 1, 9]
def baseStart_4744083 : Nat := 118140960795 + 4744083 * 2 ^ 59
def prefixEnd_4744083 : Nat := 4983230072969 + 3 ^ 40 * 4744083 * 2
def baseEnd_4744083 : Nat := 811998281274622495714955

theorem tailTrace_4744083 : CollatzResearch.WordTrace tailWord_4744083 prefixEnd_4744083 811998281274622495714955 := by
  unfold tailWord_4744083
  simp only [CollatzResearch.WordTrace]
  refine ⟨173030922072004990716212903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115353948048003327144141935 173030922072004990716212903)
  ·
    refine ⟨259546383108007486074319355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173030922072004990716212903 259546383108007486074319355)
    ·
      refine ⟨389319574662011229111479033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259546383108007486074319355 389319574662011229111479033)
      ·
        refine ⟨291989680996508421833609275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 389319574662011229111479033 291989680996508421833609275)
        ·
          refine ⟨437984521494762632750413913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291989680996508421833609275 437984521494762632750413913)
          ·
            refine ⟨328488391121071974562810435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 437984521494762632750413913 328488391121071974562810435)
            ·
              refine ⟨492732586681607961844215653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328488391121071974562810435 492732586681607961844215653)
              ·
                refine ⟨92387360002801492845790435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 492732586681607961844215653 92387360002801492845790435)
                ·
                  refine ⟨138581040004202239268685653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92387360002801492845790435 138581040004202239268685653)
                  ·
                    refine ⟨811998281274622495714955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 138581040004202239268685653 811998281274622495714955)
                    ·
                      rfl

theorem cell23_4744083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 9].length) (baseStart_4744083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744083 prefixEnd_4744083 := by exact prefixLift 4744083
  have htrace : WordTrace (prefixWord ++ tailWord_4744083) baseStart_4744083 baseEnd_4744083 := by
    simpa [prefixWord, tailWord_4744083, baseEnd_4744083] using wordTrace_append hprefix tailTrace_4744083
  have hstable : (prefixWord ++ tailWord_4744083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744083).length < 2 ^ (prefixWord ++ tailWord_4744083).sum := by decide
  have hdescent : baseEnd_4744083 < baseStart_4744083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744084 : List Nat := [2, 4, 2, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_4744084 : Nat := 118140960795 + 4744084 * 2 ^ 59
def prefixEnd_4744084 : Nat := 4983230072969 + 3 ^ 40 * 4744084 * 2
def baseEnd_4744084 : Nat := 2435995357304521983232361

theorem tailTrace_4744084 : CollatzResearch.WordTrace tailWord_4744084 prefixEnd_4744084 2435995357304521983232361 := by
  unfold tailWord_4744084
  simp only [CollatzResearch.WordTrace]
  refine ⟨86515479272500683943499653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115353972363334245257999537 86515479272500683943499653)
  ·
    refine ⟨16221652363593878239406185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86515479272500683943499653 16221652363593878239406185)
    ·
      refine ⟨12166239272695408679554639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16221652363593878239406185 12166239272695408679554639)
      ·
        refine ⟨18249358909043113019331959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12166239272695408679554639 18249358909043113019331959)
        ·
          refine ⟨27374038363564669528997939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18249358909043113019331959 27374038363564669528997939)
          ·
            refine ⟨41061057545347004293496909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27374038363564669528997939 41061057545347004293496909)
            ·
              refine ⟨15397896579505126610061341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41061057545347004293496909 15397896579505126610061341)
              ·
                refine ⟨5774211217314422478773003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15397896579505126610061341 5774211217314422478773003)
                ·
                  refine ⟨8661316825971633718159505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5774211217314422478773003 8661316825971633718159505)
                  ·
                    refine ⟨6495987619478725288619629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8661316825971633718159505 6495987619478725288619629)
                    ·
                      refine ⟨2435995357304521983232361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6495987619478725288619629 2435995357304521983232361)
                      ·
                        rfl

theorem cell23_4744084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_4744084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744084 prefixEnd_4744084 := by exact prefixLift 4744084
  have htrace : WordTrace (prefixWord ++ tailWord_4744084) baseStart_4744084 baseEnd_4744084 := by
    simpa [prefixWord, tailWord_4744084, baseEnd_4744084] using wordTrace_append hprefix tailTrace_4744084
  have hstable : (prefixWord ++ tailWord_4744084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744084).length < 2 ^ (prefixWord ++ tailWord_4744084).sum := by decide
  have hdescent : baseEnd_4744084 < baseStart_4744084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744098 : List Nat := [3, 3, 1, 2, 2, 1, 2, 4, 1, 2, 2]
def baseStart_4744098 : Nat := 118140960795 + 4744098 * 2 ^ 59
def prefixEnd_4744098 : Nat := 4983230072969 + 3 ^ 40 * 4744098 * 2
def baseEnd_4744098 : Nat := 2436002546033684928457297

theorem tailTrace_4744098 : CollatzResearch.WordTrace tailWord_4744098 prefixEnd_4744098 2436002546033684928457297 := by
  unfold tailWord_4744098
  simp only [CollatzResearch.WordTrace]
  refine ⟨43257867291737662069502237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115354312777967098852005965 43257867291737662069502237)
  ·
    refine ⟨16221700234401623276063339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43257867291737662069502237 16221700234401623276063339)
    ·
      refine ⟨24332550351602434914095009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16221700234401623276063339 24332550351602434914095009)
      ·
        refine ⟨18249412763701826185571257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24332550351602434914095009 18249412763701826185571257)
        ·
          refine ⟨13687059572776369639178443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18249412763701826185571257 13687059572776369639178443)
          ·
            refine ⟨20530589359164554458767665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13687059572776369639178443 20530589359164554458767665)
            ·
              refine ⟨15397942019373415844075749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20530589359164554458767665 15397942019373415844075749)
              ·
                refine ⟨2887114128632515470764203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15397942019373415844075749 2887114128632515470764203)
                ·
                  refine ⟨4330671192948773206146305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2887114128632515470764203 4330671192948773206146305)
                  ·
                    refine ⟨3248003394711579904609729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4330671192948773206146305 3248003394711579904609729)
                    ·
                      refine ⟨2436002546033684928457297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3248003394711579904609729 2436002546033684928457297)
                      ·
                        rfl

theorem cell23_4744098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_4744098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744098 prefixEnd_4744098 := by exact prefixLift 4744098
  have htrace : WordTrace (prefixWord ++ tailWord_4744098) baseStart_4744098 baseEnd_4744098 := by
    simpa [prefixWord, tailWord_4744098, baseEnd_4744098] using wordTrace_append hprefix tailTrace_4744098
  have hstable : (prefixWord ++ tailWord_4744098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744098).length < 2 ^ (prefixWord ++ tailWord_4744098).sum := by decide
  have hdescent : baseEnd_4744098 < baseStart_4744098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744132 : List Nat := [2, 3, 3, 3, 1, 2, 1, 3, 1, 2, 2]
def baseStart_4744132 : Nat := 118140960795 + 4744132 * 2 ^ 59
def prefixEnd_4744132 : Nat := 4983230072969 + 3 ^ 40 * 4744132 * 2
def baseEnd_4744132 : Nat := 2436020004375937795432141

theorem tailTrace_4744132 : CollatzResearch.WordTrace tailWord_4744132 prefixEnd_4744132 2436020004375937795432141 := by
  unfold tailWord_4744132
  simp only [CollatzResearch.WordTrace]
  refine ⟨86516354624413736042373325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115355139499218314723164433 86516354624413736042373325)
  ·
    refine ⟨32443632984155151015889997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86516354624413736042373325 32443632984155151015889997)
    ·
      refine ⟨12166362369058181630958749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32443632984155151015889997 12166362369058181630958749)
      ·
        refine ⟨4562385888396818111609531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12166362369058181630958749 4562385888396818111609531)
        ·
          refine ⟨6843578832595227167414297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4562385888396818111609531 6843578832595227167414297)
          ·
            refine ⟨5132684124446420375560723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6843578832595227167414297 5132684124446420375560723)
            ·
              refine ⟨7699026186669630563341085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5132684124446420375560723 7699026186669630563341085)
              ·
                refine ⟨2887134820001111461252907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7699026186669630563341085 2887134820001111461252907)
                ·
                  refine ⟨4330702230001667191879361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2887134820001111461252907 4330702230001667191879361)
                  ·
                    refine ⟨3248026672501250393909521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4330702230001667191879361 3248026672501250393909521)
                    ·
                      refine ⟨2436020004375937795432141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3248026672501250393909521 2436020004375937795432141)
                      ·
                        rfl

theorem cell23_4744132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_4744132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744132 prefixEnd_4744132 := by exact prefixLift 4744132
  have htrace : WordTrace (prefixWord ++ tailWord_4744132) baseStart_4744132 baseEnd_4744132 := by
    simpa [prefixWord, tailWord_4744132, baseEnd_4744132] using wordTrace_append hprefix tailTrace_4744132
  have hstable : (prefixWord ++ tailWord_4744132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744132).length < 2 ^ (prefixWord ++ tailWord_4744132).sum := by decide
  have hdescent : baseEnd_4744132 < baseStart_4744132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744165 : List Nat := [1, 3, 1, 6, 1, 2, 2, 1, 2, 1, 3]
def baseStart_4744165 : Nat := 118140960795 + 4744165 * 2 ^ 59
def prefixEnd_4744165 : Nat := 4983230072969 + 3 ^ 40 * 4744165 * 2
def baseEnd_4744165 : Nat := 2436036949237536166319489

theorem tailTrace_4744165 : CollatzResearch.WordTrace tailWord_4744165 prefixEnd_4744165 2436036949237536166319489 := by
  unfold tailWord_4744165
  simp only [CollatzResearch.WordTrace]
  refine ⟨173033912857707918720697949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115355941905138612480465299 173033912857707918720697949)
  ·
    refine ⟨64887717321640469520261731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173033912857707918720697949 64887717321640469520261731)
    ·
      refine ⟨97331575982460704280392597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64887717321640469520261731 97331575982460704280392597)
      ·
        refine ⟨4562417624177845513143403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 97331575982460704280392597 4562417624177845513143403)
        ·
          refine ⟨6843626436266768269715105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4562417624177845513143403 6843626436266768269715105)
          ·
            refine ⟨5132719827200076202286329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6843626436266768269715105 5132719827200076202286329)
            ·
              refine ⟨3849539870400057151714747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5132719827200076202286329 3849539870400057151714747)
              ·
                refine ⟨5774309805600085727572121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3849539870400057151714747 5774309805600085727572121)
                ·
                  refine ⟨4330732354200064295679091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5774309805600085727572121 4330732354200064295679091)
                  ·
                    refine ⟨6496098531300096443518637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4330732354200064295679091 6496098531300096443518637)
                    ·
                      refine ⟨2436036949237536166319489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6496098531300096443518637 2436036949237536166319489)
                      ·
                        rfl

theorem cell23_4744165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_4744165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744165 prefixEnd_4744165 := by exact prefixLift 4744165
  have htrace : WordTrace (prefixWord ++ tailWord_4744165) baseStart_4744165 baseEnd_4744165 := by
    simpa [prefixWord, tailWord_4744165, baseEnd_4744165] using wordTrace_append hprefix tailTrace_4744165
  have hstable : (prefixWord ++ tailWord_4744165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744165).length < 2 ^ (prefixWord ++ tailWord_4744165).sum := by decide
  have hdescent : baseEnd_4744165 < baseStart_4744165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744304 : List Nat := [2, 1, 1, 1, 5, 1, 1, 3, 1, 5, 2]
def baseStart_4744304 : Nat := 118140960795 + 4744304 * 2 ^ 59
def prefixEnd_4744304 : Nat := 4983230072969 + 3 ^ 40 * 4744304 * 2
def baseEnd_4744304 : Nat := 2436108323048511122481349

theorem tailTrace_4744304 : CollatzResearch.WordTrace tailWord_4744304 prefixEnd_4744304 2436108323048511122481349 := by
  unfold tailWord_4744304
  simp only [CollatzResearch.WordTrace]
  refine ⟨86519491302102172730003983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115359321736136230306671977 86519491302102172730003983)
  ·
    refine ⟨129779236953153259095005975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86519491302102172730003983 129779236953153259095005975)
    ·
      refine ⟨194668855429729888642508963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129779236953153259095005975 194668855429729888642508963)
      ·
        refine ⟨292003283144594832963763445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194668855429729888642508963 292003283144594832963763445)
        ·
          refine ⟨27375307794805765590352823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 292003283144594832963763445 27375307794805765590352823)
          ·
            refine ⟨41062961692208648385529235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27375307794805765590352823 41062961692208648385529235)
            ·
              refine ⟨61594442538312972578293853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41062961692208648385529235 61594442538312972578293853)
              ·
                refine ⟨23097915951867364716860195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61594442538312972578293853 23097915951867364716860195)
                ·
                  refine ⟨34646873927801047075290293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23097915951867364716860195 34646873927801047075290293)
                  ·
                    refine ⟨3248144430731348163308465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34646873927801047075290293 3248144430731348163308465)
                    ·
                      refine ⟨2436108323048511122481349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3248144430731348163308465 2436108323048511122481349)
                      ·
                        rfl

theorem cell23_4744304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 1, 5, 2].length) (baseStart_4744304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744304 prefixEnd_4744304 := by exact prefixLift 4744304
  have htrace : WordTrace (prefixWord ++ tailWord_4744304) baseStart_4744304 baseEnd_4744304 := by
    simpa [prefixWord, tailWord_4744304, baseEnd_4744304] using wordTrace_append hprefix tailTrace_4744304
  have hstable : (prefixWord ++ tailWord_4744304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744304).length < 2 ^ (prefixWord ++ tailWord_4744304).sum := by decide
  have hdescent : baseEnd_4744304 < baseStart_4744304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744321 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 4, 3, 2]
def baseStart_4744321 : Nat := 118140960795 + 4744321 * 2 ^ 59
def prefixEnd_4744321 : Nat := 4983230072969 + 3 ^ 40 * 4744321 * 2
def baseEnd_4744321 : Nat := 2436117052219637555968771

theorem tailTrace_4744321 : CollatzResearch.WordTrace tailWord_4744321 prefixEnd_4744321 2436117052219637555968771 := by
  unfold tailWord_4744321
  simp only [CollatzResearch.WordTrace]
  refine ⟨173039602645142757363376817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115359735096761838242251211 173039602645142757363376817)
  ·
    refine ⟨129779701983857068022532613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173039602645142757363376817 129779701983857068022532613)
    ·
      refine ⟨24333694121973200254224865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129779701983857068022532613 24333694121973200254224865)
      ·
        refine ⟨18250270591479900190668649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24333694121973200254224865 18250270591479900190668649)
        ·
          refine ⟨13687702943609925143001487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18250270591479900190668649 13687702943609925143001487)
          ·
            refine ⟨20531554415414887714502231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13687702943609925143001487 20531554415414887714502231)
            ·
              refine ⟨30797331623122331571753347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20531554415414887714502231 30797331623122331571753347)
              ·
                refine ⟨46195997434683497357630021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30797331623122331571753347 46195997434683497357630021)
                ·
                  refine ⟨8661749519003155754555629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46195997434683497357630021 8661749519003155754555629)
                  ·
                    refine ⟨3248156069626183407958361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8661749519003155754555629 3248156069626183407958361)
                    ·
                      refine ⟨2436117052219637555968771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3248156069626183407958361 2436117052219637555968771)
                      ·
                        rfl

theorem cell23_4744321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_4744321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744321 prefixEnd_4744321 := by exact prefixLift 4744321
  have htrace : WordTrace (prefixWord ++ tailWord_4744321) baseStart_4744321 baseEnd_4744321 := by
    simpa [prefixWord, tailWord_4744321, baseEnd_4744321] using wordTrace_append hprefix tailTrace_4744321
  have hstable : (prefixWord ++ tailWord_4744321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744321).length < 2 ^ (prefixWord ++ tailWord_4744321).sum := by decide
  have hdescent : baseEnd_4744321 < baseStart_4744321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744351 : List Nat := [1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 4]
def baseStart_4744351 : Nat := 118140960795 + 4744351 * 2 ^ 59
def prefixEnd_4744351 : Nat := 4983230072969 + 3 ^ 40 * 4744351 * 2
def baseEnd_4744351 : Nat := 2436132456639272438593633

theorem tailTrace_4744351 : CollatzResearch.WordTrace tailWord_4744351 prefixEnd_4744351 2436132456639272438593633 := by
  unfold tailWord_4744351
  simp only [CollatzResearch.WordTrace]
  refine ⟨173040696835034072486968907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115360464556689381657979271 173040696835034072486968907)
  ·
    refine ⟨259561045252551108730453361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173040696835034072486968907 259561045252551108730453361)
    ·
      refine ⟨194670783939413331547840021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259561045252551108730453361 194670783939413331547840021)
      ·
        refine ⟨9125192997159999916305001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 194670783939413331547840021 9125192997159999916305001)
        ·
          refine ⟨6843894747869999937228751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9125192997159999916305001 6843894747869999937228751)
          ·
            refine ⟨10265842121804999905843127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6843894747869999937228751 10265842121804999905843127)
            ·
              refine ⟨15398763182707499858764691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10265842121804999905843127 15398763182707499858764691)
              ·
                refine ⟨23098144774061249788147037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15398763182707499858764691 23098144774061249788147037)
                ·
                  refine ⟨8661804290272968670555139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23098144774061249788147037 8661804290272968670555139)
                  ·
                    refine ⟨12992706435409453005832709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8661804290272968670555139 12992706435409453005832709)
                    ·
                      refine ⟨2436132456639272438593633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12992706435409453005832709 2436132456639272438593633)
                      ·
                        rfl

theorem cell23_4744351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_4744351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744351 prefixEnd_4744351 := by exact prefixLift 4744351
  have htrace : WordTrace (prefixWord ++ tailWord_4744351) baseStart_4744351 baseEnd_4744351 := by
    simpa [prefixWord, tailWord_4744351, baseEnd_4744351] using wordTrace_append hprefix tailTrace_4744351
  have hstable : (prefixWord ++ tailWord_4744351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744351).length < 2 ^ (prefixWord ++ tailWord_4744351).sum := by decide
  have hdescent : baseEnd_4744351 < baseStart_4744351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744357 : List Nat := [1, 3, 1, 2, 1, 4, 2, 9]
def baseStart_4744357 : Nat := 118140960795 + 4744357 * 2 ^ 59
def prefixEnd_4744357 : Nat := 4983230072969 + 3 ^ 40 * 4744357 * 2
def baseEnd_4744357 : Nat := 90227242130488867226615

theorem tailTrace_4744357 : CollatzResearch.WordTrace tailWord_4744357 prefixEnd_4744357 90227242130488867226615 := by
  unfold tailWord_4744357
  simp only [CollatzResearch.WordTrace]
  refine ⟨173040915673012335511687325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115360610448674890341124883 173040915673012335511687325)
  ·
    refine ⟨64890343377379625816882747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173040915673012335511687325 64890343377379625816882747)
    ·
      refine ⟨97335515066069438725324121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64890343377379625816882747 97335515066069438725324121)
      ·
        refine ⟨73001636299552079043993091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97335515066069438725324121 73001636299552079043993091)
        ·
          refine ⟨109502454449328118565989637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73001636299552079043993091 109502454449328118565989637)
          ·
            refine ⟨20531710209249022231123057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109502454449328118565989637 20531710209249022231123057)
            ·
              refine ⟨15398782656936766673342293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20531710209249022231123057 15398782656936766673342293)
              ·
                refine ⟨90227242130488867226615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15398782656936766673342293 90227242130488867226615)
                ·
                  rfl

theorem cell23_4744357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 9].length) (baseStart_4744357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744357 prefixEnd_4744357 := by exact prefixLift 4744357
  have htrace : WordTrace (prefixWord ++ tailWord_4744357) baseStart_4744357 baseEnd_4744357 := by
    simpa [prefixWord, tailWord_4744357, baseEnd_4744357] using wordTrace_append hprefix tailTrace_4744357
  have hstable : (prefixWord ++ tailWord_4744357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744357).length < 2 ^ (prefixWord ++ tailWord_4744357).sum := by decide
  have hdescent : baseEnd_4744357 < baseStart_4744357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744428 : List Nat := [2, 2, 1, 1, 2, 5, 1, 3, 1, 3, 2]
def baseStart_4744428 : Nat := 118140960795 + 4744428 * 2 ^ 59
def prefixEnd_4744428 : Nat := 4983230072969 + 3 ^ 40 * 4744428 * 2
def baseEnd_4744428 : Nat := 2436171994649668637330779

theorem tailTrace_4744428 : CollatzResearch.WordTrace tailWord_4744428 prefixEnd_4744428 2436171994649668637330779 := by
  unfold tailWord_4744428
  simp only [CollatzResearch.WordTrace]
  refine ⟨86521752627877557318760969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115362336837170076425014625 86521752627877557318760969)
  ·
    refine ⟨64891314470908167989070727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86521752627877557318760969 64891314470908167989070727)
    ·
      refine ⟨97336971706362251983606091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64891314470908167989070727 97336971706362251983606091)
      ·
        refine ⟨146005457559543377975409137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97336971706362251983606091 146005457559543377975409137)
        ·
          refine ⟨109504093169657533481556853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146005457559543377975409137 109504093169657533481556853)
          ·
            refine ⟨10266008734655393763895955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 109504093169657533481556853 10266008734655393763895955)
            ·
              refine ⟨15399013101983090645843933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10266008734655393763895955 15399013101983090645843933)
              ·
                refine ⟨5774629913243658992191475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15399013101983090645843933 5774629913243658992191475)
                ·
                  refine ⟨8661944869865488488287213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5774629913243658992191475 8661944869865488488287213)
                  ·
                    refine ⟨3248229326199558183107705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8661944869865488488287213 3248229326199558183107705)
                    ·
                      refine ⟨2436171994649668637330779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3248229326199558183107705 2436171994649668637330779)
                      ·
                        rfl

theorem cell23_4744428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 3, 2].length) (baseStart_4744428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744428 prefixEnd_4744428 := by exact prefixLift 4744428
  have htrace : WordTrace (prefixWord ++ tailWord_4744428) baseStart_4744428 baseEnd_4744428 := by
    simpa [prefixWord, tailWord_4744428, baseEnd_4744428] using wordTrace_append hprefix tailTrace_4744428
  have hstable : (prefixWord ++ tailWord_4744428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744428).length < 2 ^ (prefixWord ++ tailWord_4744428).sum := by decide
  have hdescent : baseEnd_4744428 < baseStart_4744428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744531 : List Nat := [1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 4]
def baseStart_4744531 : Nat := 118140960795 + 4744531 * 2 ^ 59
def prefixEnd_4744531 : Nat := 4983230072969 + 3 ^ 40 * 4744531 * 2
def baseEnd_4744531 : Nat := 2436224883157081734342805

theorem tailTrace_4744531 : CollatzResearch.WordTrace tailWord_4744531 prefixEnd_4744531 2436224883157081734342805 := by
  unfold tailWord_4744531
  simp only [CollatzResearch.WordTrace]
  refine ⟨173047261974381963228521447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115364841316254642152347631 173047261974381963228521447)
  ·
    refine ⟨259570892961572944842782171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173047261974381963228521447 259570892961572944842782171)
    ·
      refine ⟨389356339442359417264173257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259570892961572944842782171 389356339442359417264173257)
      ·
        refine ⟨292017254581769562948129943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 389356339442359417264173257 292017254581769562948129943)
        ·
          refine ⟨438025881872654344422194915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292017254581769562948129943 438025881872654344422194915)
          ·
            refine ⟨657038822808981516633292373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438025881872654344422194915 657038822808981516633292373)
            ·
              refine ⟨7699673704792752148046395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 657038822808981516633292373 7699673704792752148046395)
              ·
                refine ⟨11549510557189128222069593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7699673704792752148046395 11549510557189128222069593)
                ·
                  refine ⟨8662132917891846166552195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11549510557189128222069593 8662132917891846166552195)
                  ·
                    refine ⟨12993199376837769249828293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8662132917891846166552195 12993199376837769249828293)
                    ·
                      refine ⟨2436224883157081734342805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12993199376837769249828293 2436224883157081734342805)
                      ·
                        rfl

theorem cell23_4744531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 4].length) (baseStart_4744531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744531 prefixEnd_4744531 := by exact prefixLift 4744531
  have htrace : WordTrace (prefixWord ++ tailWord_4744531) baseStart_4744531 baseEnd_4744531 := by
    simpa [prefixWord, tailWord_4744531, baseEnd_4744531] using wordTrace_append hprefix tailTrace_4744531
  have hstable : (prefixWord ++ tailWord_4744531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744531).length < 2 ^ (prefixWord ++ tailWord_4744531).sum := by decide
  have hdescent : baseEnd_4744531 < baseStart_4744531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744565 : List Nat := [1, 3, 4, 1, 3, 1, 1, 1, 2, 4, 2]
def baseStart_4744565 : Nat := 118140960795 + 4744565 * 2 ^ 59
def prefixEnd_4744565 : Nat := 4983230072969 + 3 ^ 40 * 4744565 * 2
def baseEnd_4744565 : Nat := 2436242341499334601317649

theorem tailTrace_4744565 : CollatzResearch.WordTrace tailWord_4744565 prefixEnd_4744565 2436242341499334601317649 := by
  unfold tailWord_4744565
  simp only [CollatzResearch.WordTrace]
  refine ⟨173048502056258787035259149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115365668037505858023506099 173048502056258787035259149)
  ·
    refine ⟨64893188271097045138222181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173048502056258787035259149 64893188271097045138222181)
    ·
      refine ⟨12167472800830695963416659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64893188271097045138222181 12167472800830695963416659)
      ·
        refine ⟨18251209201246043945124989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12167472800830695963416659 18251209201246043945124989)
        ·
          refine ⟨6844203450467266479421871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18251209201246043945124989 6844203450467266479421871)
          ·
            refine ⟨10266305175700899719132807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6844203450467266479421871 10266305175700899719132807)
            ·
              refine ⟨15399457763551349578699211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10266305175700899719132807 15399457763551349578699211)
              ·
                refine ⟨23099186645327024368048817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15399457763551349578699211 23099186645327024368048817)
                ·
                  refine ⟨17324389983995268276036613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23099186645327024368048817 17324389983995268276036613)
                  ·
                    refine ⟨3248323121999112801756865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17324389983995268276036613 3248323121999112801756865)
                    ·
                      refine ⟨2436242341499334601317649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3248323121999112801756865 2436242341499334601317649)
                      ·
                        rfl

theorem cell23_4744565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_4744565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744565 prefixEnd_4744565 := by exact prefixLift 4744565
  have htrace : WordTrace (prefixWord ++ tailWord_4744565) baseStart_4744565 baseEnd_4744565 := by
    simpa [prefixWord, tailWord_4744565, baseEnd_4744565] using wordTrace_append hprefix tailTrace_4744565
  have hstable : (prefixWord ++ tailWord_4744565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744565).length < 2 ^ (prefixWord ++ tailWord_4744565).sum := by decide
  have hdescent : baseEnd_4744565 < baseStart_4744565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744585 : List Nat := [1, 2, 1, 1, 7, 2, 1, 1, 2, 2, 3]
def baseStart_4744585 : Nat := 118140960795 + 4744585 * 2 ^ 59
def prefixEnd_4744585 : Nat := 4983230072969 + 3 ^ 40 * 4744585 * 2
def baseEnd_4744585 : Nat := 2436252611112424523067557

theorem tailTrace_4744585 : CollatzResearch.WordTrace tailWord_4744585 prefixEnd_4744585 2436252611112424523067557 := by
  unfold tailWord_4744585
  simp only [CollatzResearch.WordTrace]
  refine ⟨173049231516186330450987209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115366154344124220300658139 173049231516186330450987209)
  ·
    refine ⟨129786923637139747838240407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173049231516186330450987209 129786923637139747838240407)
    ·
      refine ⟨194680385455709621757360611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129786923637139747838240407 194680385455709621757360611)
      ·
        refine ⟨292020578183564432636040917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194680385455709621757360611 292020578183564432636040917)
        ·
          refine ⟨6844232301177291389907209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 292020578183564432636040917 6844232301177291389907209)
          ·
            refine ⟨5133174225882968542430407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6844232301177291389907209 5133174225882968542430407)
            ·
              refine ⟨7699761338824452813645611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5133174225882968542430407 7699761338824452813645611)
              ·
                refine ⟨11549642008236679220468417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7699761338824452813645611 11549642008236679220468417)
                ·
                  refine ⟨8662231506177509415351313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11549642008236679220468417 8662231506177509415351313)
                  ·
                    refine ⟨6496673629633132061513485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8662231506177509415351313 6496673629633132061513485)
                    ·
                      refine ⟨2436252611112424523067557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6496673629633132061513485 2436252611112424523067557)
                      ·
                        rfl

theorem cell23_4744585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 2, 3].length) (baseStart_4744585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744585 prefixEnd_4744585 := by exact prefixLift 4744585
  have htrace : WordTrace (prefixWord ++ tailWord_4744585) baseStart_4744585 baseEnd_4744585 := by
    simpa [prefixWord, tailWord_4744585, baseEnd_4744585] using wordTrace_append hprefix tailTrace_4744585
  have hstable : (prefixWord ++ tailWord_4744585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744585).length < 2 ^ (prefixWord ++ tailWord_4744585).sum := by decide
  have hdescent : baseEnd_4744585 < baseStart_4744585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744608 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 4, 3, 2]
def baseStart_4744608 : Nat := 118140960795 + 4744608 * 2 ^ 59
def prefixEnd_4744608 : Nat := 4983230072969 + 3 ^ 40 * 4744608 * 2
def baseEnd_4744608 : Nat := 2436264421167477933079951

theorem tailTrace_4744608 : CollatzResearch.WordTrace tailWord_4744608 prefixEnd_4744608 2436264421167477933079951 := by
  unfold tailWord_4744608
  simp only [CollatzResearch.WordTrace]
  refine ⟨86525035197551502689537239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115366713596735336919382985 86525035197551502689537239)
  ·
    refine ⟨129787552796327254034305859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86525035197551502689537239 129787552796327254034305859)
    ·
      refine ⟨194681329194490881051458789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129787552796327254034305859 194681329194490881051458789)
      ·
        refine ⟨36502749223967040197148523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 194681329194490881051458789 36502749223967040197148523)
        ·
          refine ⟨54754123835950560295722785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36502749223967040197148523 54754123835950560295722785)
          ·
            refine ⟨41065592876962920221792089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54754123835950560295722785 41065592876962920221792089)
            ·
              refine ⟨30799194657722190166344067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41065592876962920221792089 30799194657722190166344067)
              ·
                refine ⟨46198791986583285249516101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30799194657722190166344067 46198791986583285249516101)
                ·
                  refine ⟨8662273497484365984284269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46198791986583285249516101 8662273497484365984284269)
                  ·
                    refine ⟨3248352561556637244106601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8662273497484365984284269 3248352561556637244106601)
                    ·
                      refine ⟨2436264421167477933079951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3248352561556637244106601 2436264421167477933079951)
                      ·
                        rfl

theorem cell23_4744608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_4744608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744608 prefixEnd_4744608 := by exact prefixLift 4744608
  have htrace : WordTrace (prefixWord ++ tailWord_4744608) baseStart_4744608 baseEnd_4744608 := by
    simpa [prefixWord, tailWord_4744608, baseEnd_4744608] using wordTrace_append hprefix tailTrace_4744608
  have hstable : (prefixWord ++ tailWord_4744608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744608).length < 2 ^ (prefixWord ++ tailWord_4744608).sum := by decide
  have hdescent : baseEnd_4744608 < baseStart_4744608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744615 : List Nat := [1, 1, 6, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_4744615 : Nat := 118140960795 + 4744615 * 2 ^ 59
def prefixEnd_4744615 : Nat := 4983230072969 + 3 ^ 40 * 4744615 * 2
def baseEnd_4744615 : Nat := 2436268015532059405692419

theorem tailTrace_4744615 : CollatzResearch.WordTrace tailWord_4744615 prefixEnd_4744615 2436268015532059405692419 := by
  unfold tailWord_4744615
  simp only [CollatzResearch.WordTrace]
  refine ⟨173050325706077645574579299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115366883804051763716386199 173050325706077645574579299)
  ·
    refine ⟨259575488559116468361868949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173050325706077645574579299 259575488559116468361868949)
    ·
      refine ⟨12167601026208584454462607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 259575488559116468361868949 12167601026208584454462607)
      ·
        refine ⟨18251401539312876681693911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12167601026208584454462607 18251401539312876681693911)
        ·
          refine ⟨27377102308969315022540867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18251401539312876681693911 27377102308969315022540867)
          ·
            refine ⟨41065653463453972533811301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27377102308969315022540867 41065653463453972533811301)
            ·
              refine ⟨7699810024397619850089619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41065653463453972533811301 7699810024397619850089619)
              ·
                refine ⟨11549715036596429775134429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7699810024397619850089619 11549715036596429775134429)
                ·
                  refine ⟨4331143138723661165675411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11549715036596429775134429 4331143138723661165675411)
                  ·
                    refine ⟨6496714708085491748513117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4331143138723661165675411 6496714708085491748513117)
                    ·
                      refine ⟨2436268015532059405692419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6496714708085491748513117 2436268015532059405692419)
                      ·
                        rfl

theorem cell23_4744615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_4744615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744615 prefixEnd_4744615 := by exact prefixLift 4744615
  have htrace : WordTrace (prefixWord ++ tailWord_4744615) baseStart_4744615 baseEnd_4744615 := by
    simpa [prefixWord, tailWord_4744615, baseEnd_4744615] using wordTrace_append hprefix tailTrace_4744615
  have hstable : (prefixWord ++ tailWord_4744615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744615).length < 2 ^ (prefixWord ++ tailWord_4744615).sum := by decide
  have hdescent : baseEnd_4744615 < baseStart_4744615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744638 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2]
def baseStart_4744638 : Nat := 118140960795 + 4744638 * 2 ^ 59
def prefixEnd_4744638 : Nat := 4983230072969 + 3 ^ 40 * 4744638 * 2
def baseEnd_4744638 : Nat := 2436279825587112815704813

theorem tailTrace_4744638 : CollatzResearch.WordTrace tailWord_4744638 prefixEnd_4744638 2436279825587112815704813 := by
  unfold tailWord_4744638
  simp only [CollatzResearch.WordTrace]
  refine ⟨21631395573124290062833321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115367443056662880335111045 21631395573124290062833321)
  ·
    refine ⟨16223546679843217547124991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21631395573124290062833321 16223546679843217547124991)
    ·
      refine ⟨24335320019764826320687487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16223546679843217547124991 24335320019764826320687487)
      ·
        refine ⟨36502980029647239481031231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24335320019764826320687487 36502980029647239481031231)
        ·
          refine ⟨54754470044470859221546847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36502980029647239481031231 54754470044470859221546847)
          ·
            refine ⟨82131705066706288832320271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54754470044470859221546847 82131705066706288832320271)
            ·
              refine ⟨123197557600059433248480407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82131705066706288832320271 123197557600059433248480407)
              ·
                refine ⟨184796336400089149872720611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123197557600059433248480407 184796336400089149872720611)
                ·
                  refine ⟨277194504600133724809080917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184796336400089149872720611 277194504600133724809080917)
                  ·
                    refine ⟨3248373100782817087606417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 277194504600133724809080917 3248373100782817087606417)
                    ·
                      refine ⟨2436279825587112815704813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3248373100782817087606417 2436279825587112815704813)
                      ·
                        rfl

theorem cell23_4744638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_4744638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744638 prefixEnd_4744638 := by exact prefixLift 4744638
  have htrace : WordTrace (prefixWord ++ tailWord_4744638) baseStart_4744638 baseEnd_4744638 := by
    simpa [prefixWord, tailWord_4744638, baseEnd_4744638] using wordTrace_append hprefix tailTrace_4744638
  have hstable : (prefixWord ++ tailWord_4744638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744638).length < 2 ^ (prefixWord ++ tailWord_4744638).sum := by decide
  have hdescent : baseEnd_4744638 < baseStart_4744638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744651 : List Nat := [1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 4]
def baseStart_4744651 : Nat := 118140960795 + 4744651 * 2 ^ 59
def prefixEnd_4744651 : Nat := 4983230072969 + 3 ^ 40 * 4744651 * 2
def baseEnd_4744651 : Nat := 2436286500835621264842253

theorem tailTrace_4744651 : CollatzResearch.WordTrace tailWord_4744651 prefixEnd_4744651 2436286500835621264842253 := by
  unfold tailWord_4744651
  simp only [CollatzResearch.WordTrace]
  refine ⟨173051638733947223722889807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115367759155964815815259871 173051638733947223722889807)
  ·
    refine ⟨259577458100920835584334711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173051638733947223722889807 259577458100920835584334711)
    ·
      refine ⟨389366187151381253376502067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259577458100920835584334711 389366187151381253376502067)
      ·
        refine ⟨584049280727071880064753101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389366187151381253376502067 584049280727071880064753101)
        ·
          refine ⟨219018480272651955024282413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 584049280727071880064753101 219018480272651955024282413)
          ·
            refine ⟨82131930102244483134105905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 219018480272651955024282413 82131930102244483134105905)
            ·
              refine ⟨61598947576683362350579429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82131930102244483134105905 61598947576683362350579429)
              ·
                refine ⟨11549802670628130440733643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61598947576683362350579429 11549802670628130440733643)
                ·
                  refine ⟨17324704005942195661100465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11549802670628130440733643 17324704005942195661100465)
                  ·
                    refine ⟨12993528004456646745825349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17324704005942195661100465 12993528004456646745825349)
                    ·
                      refine ⟨2436286500835621264842253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12993528004456646745825349 2436286500835621264842253)
                      ·
                        rfl

theorem cell23_4744651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 4].length) (baseStart_4744651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744651 prefixEnd_4744651 := by exact prefixLift 4744651
  have htrace : WordTrace (prefixWord ++ tailWord_4744651) baseStart_4744651 baseEnd_4744651 := by
    simpa [prefixWord, tailWord_4744651, baseEnd_4744651] using wordTrace_append hprefix tailTrace_4744651
  have hstable : (prefixWord ++ tailWord_4744651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744651).length < 2 ^ (prefixWord ++ tailWord_4744651).sum := by decide
  have hdescent : baseEnd_4744651 < baseStart_4744651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744702 : List Nat := [4, 2, 2, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_4744702 : Nat := 118140960795 + 4744702 * 2 ^ 59
def prefixEnd_4744702 : Nat := 4983230072969 + 3 ^ 40 * 4744702 * 2
def baseEnd_4744702 : Nat := 2436312688349000565304519

theorem tailTrace_4744702 : CollatzResearch.WordTrace tailWord_4744702 prefixEnd_4744702 2436312688349000565304519 := by
  unfold tailWord_4744702
  simp only [CollatzResearch.WordTrace]
  refine ⟨21631687357095307429124545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115368999237841639621997573 21631687357095307429124545)
  ·
    refine ⟨16223765517821480571843409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21631687357095307429124545 16223765517821480571843409)
    ·
      refine ⟨12167824138366110428882557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16223765517821480571843409 12167824138366110428882557)
      ·
        refine ⟨4562934051887291410830959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12167824138366110428882557 4562934051887291410830959)
        ·
          refine ⟨6844401077830937116246439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4562934051887291410830959 6844401077830937116246439)
          ·
            refine ⟨10266601616746405674369659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6844401077830937116246439 10266601616746405674369659)
            ·
              refine ⟨15399902425119608511554489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10266601616746405674369659 15399902425119608511554489)
              ·
                refine ⟨11549926818839706383665867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15399902425119608511554489 11549926818839706383665867)
                ·
                  refine ⟨17324890228259559575498801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11549926818839706383665867 17324890228259559575498801)
                  ·
                    refine ⟨12993667671194669681624101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17324890228259559575498801 12993667671194669681624101)
                    ·
                      refine ⟨2436312688349000565304519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12993667671194669681624101 2436312688349000565304519)
                      ·
                        rfl

theorem cell23_4744702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_4744702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744702 prefixEnd_4744702 := by exact prefixLift 4744702
  have htrace : WordTrace (prefixWord ++ tailWord_4744702) baseStart_4744702 baseEnd_4744702 := by
    simpa [prefixWord, tailWord_4744702, baseEnd_4744702] using wordTrace_append hprefix tailTrace_4744702
  have hstable : (prefixWord ++ tailWord_4744702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744702).length < 2 ^ (prefixWord ++ tailWord_4744702).sum := by decide
  have hdescent : baseEnd_4744702 < baseStart_4744702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744705 : List Nat := [1, 2, 4, 1, 4, 1, 1, 2, 1, 3, 3]
def baseStart_4744705 : Nat := 118140960795 + 4744705 * 2 ^ 59
def prefixEnd_4744705 : Nat := 4983230072969 + 3 ^ 40 * 4744705 * 2
def baseEnd_4744705 : Nat := 2436314228790964053567005

theorem tailTrace_4744705 : CollatzResearch.WordTrace tailWord_4744705 prefixEnd_4744705 2436314228790964053567005 := by
  unfold tailWord_4744705
  simp only [CollatzResearch.WordTrace]
  refine ⟨173053608275751590945355569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115369072183834393963570379 173053608275751590945355569)
  ·
    refine ⟨129790206206813693209016677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173053608275751590945355569 129790206206813693209016677)
    ·
      refine ⟨24335663663777567476690627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129790206206813693209016677 24335663663777567476690627)
      ·
        refine ⟨36503495495666351215035941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24335663663777567476690627 36503495495666351215035941)
        ·
          refine ⟨6844405405437440852819239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36503495495666351215035941 6844405405437440852819239)
          ·
            refine ⟨10266608108156161279228859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6844405405437440852819239 10266608108156161279228859)
            ·
              refine ⟨15399912162234241918843289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10266608108156161279228859 15399912162234241918843289)
              ·
                refine ⟨11549934121675681439132467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15399912162234241918843289 11549934121675681439132467)
                ·
                  refine ⟨17324901182513522158698701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11549934121675681439132467 17324901182513522158698701)
                  ·
                    refine ⟨6496837943442570809512013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17324901182513522158698701 6496837943442570809512013)
                    ·
                      refine ⟨2436314228790964053567005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6496837943442570809512013 2436314228790964053567005)
                      ·
                        rfl

theorem cell23_4744705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_4744705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744705 prefixEnd_4744705 := by exact prefixLift 4744705
  have htrace : WordTrace (prefixWord ++ tailWord_4744705) baseStart_4744705 baseEnd_4744705 := by
    simpa [prefixWord, tailWord_4744705, baseEnd_4744705] using wordTrace_append hprefix tailTrace_4744705
  have hstable : (prefixWord ++ tailWord_4744705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744705).length < 2 ^ (prefixWord ++ tailWord_4744705).sum := by decide
  have hdescent : baseEnd_4744705 < baseStart_4744705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744721 : List Nat := [1, 2, 2, 1, 1, 2, 4, 2, 2, 6]
def baseStart_4744721 : Nat := 118140960795 + 4744721 * 2 ^ 59
def prefixEnd_4744721 : Nat := 4983230072969 + 3 ^ 40 * 4744721 * 2
def baseEnd_4744721 : Nat := 812107481493811996988977

theorem tailTrace_4744721 : CollatzResearch.WordTrace tailWord_4744721 prefixEnd_4744721 812107481493811996988977 := by
  unfold tailWord_4744721
  simp only [CollatzResearch.WordTrace]
  refine ⟨173054191843693625677938017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115369461229129083785292011 173054191843693625677938017)
  ·
    refine ⟨129790643882770219258453513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173054191843693625677938017 129790643882770219258453513)
    ·
      refine ⟨97342982912077664443840135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129790643882770219258453513 97342982912077664443840135)
      ·
        refine ⟨146014474368116496665760203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97342982912077664443840135 146014474368116496665760203)
        ·
          refine ⟨219021711552174744998640305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146014474368116496665760203 219021711552174744998640305)
          ·
            refine ⟨164266283664131058748980229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219021711552174744998640305 164266283664131058748980229)
            ·
              refine ⟨30799928187024573515433793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 164266283664131058748980229 30799928187024573515433793)
              ·
                refine ⟨23099946140268430136575345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30799928187024573515433793 23099946140268430136575345)
                ·
                  refine ⟨17324959605201322602431509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23099946140268430136575345 17324959605201322602431509)
                  ·
                    refine ⟨812107481493811996988977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17324959605201322602431509 812107481493811996988977)
                    ·
                      rfl

theorem cell23_4744721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 6].length) (baseStart_4744721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744721 prefixEnd_4744721 := by exact prefixLift 4744721
  have htrace : WordTrace (prefixWord ++ tailWord_4744721) baseStart_4744721 baseEnd_4744721 := by
    simpa [prefixWord, tailWord_4744721, baseEnd_4744721] using wordTrace_append hprefix tailTrace_4744721
  have hstable : (prefixWord ++ tailWord_4744721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744721).length < 2 ^ (prefixWord ++ tailWord_4744721).sum := by decide
  have hdescent : baseEnd_4744721 < baseStart_4744721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744778 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 4, 3, 3]
def baseStart_4744778 : Nat := 118140960795 + 4744778 * 2 ^ 59
def prefixEnd_4744778 : Nat := 4983230072969 + 3 ^ 40 * 4744778 * 2
def baseEnd_4744778 : Nat := 2436351712878742267954169

theorem tailTrace_4744778 : CollatzResearch.WordTrace tailWord_4744778 prefixEnd_4744778 2436351712878742267954169 := by
  unfold tailWord_4744778
  simp only [CollatzResearch.WordTrace]
  refine ⟨43264067701121781103190747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115370847202991416275175325 43264067701121781103190747)
  ·
    refine ⟨64896101551682671654786121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43264067701121781103190747 64896101551682671654786121)
    ·
      refine ⟨48672076163762003741089591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64896101551682671654786121 48672076163762003741089591)
      ·
        refine ⟨73008114245643005611634387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48672076163762003741089591 73008114245643005611634387)
        ·
          refine ⟨109512171368464508417451581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73008114245643005611634387 109512171368464508417451581)
          ·
            refine ⟨41067064263174190656544343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109512171368464508417451581 41067064263174190656544343)
            ·
              refine ⟨61600596394761285984816515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41067064263174190656544343 61600596394761285984816515)
              ·
                refine ⟨92400894592141928977224773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61600596394761285984816515 92400894592141928977224773)
                ·
                  refine ⟨17325167736026611683229645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92400894592141928977224773 17325167736026611683229645)
                  ·
                    refine ⟨6496937901009979381211117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17325167736026611683229645 6496937901009979381211117)
                    ·
                      refine ⟨2436351712878742267954169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6496937901009979381211117 2436351712878742267954169)
                      ·
                        rfl

theorem cell23_4744778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_4744778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744778 prefixEnd_4744778 := by exact prefixLift 4744778
  have htrace : WordTrace (prefixWord ++ tailWord_4744778) baseStart_4744778 baseEnd_4744778 := by
    simpa [prefixWord, tailWord_4744778, baseEnd_4744778] using wordTrace_append hprefix tailTrace_4744778
  have hstable : (prefixWord ++ tailWord_4744778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744778).length < 2 ^ (prefixWord ++ tailWord_4744778).sum := by decide
  have hdescent : baseEnd_4744778 < baseStart_4744778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744796 : List Nat := [2, 2, 4, 1, 2, 2, 3, 1, 2, 2, 2]
def baseStart_4744796 : Nat := 118140960795 + 4744796 * 2 ^ 59
def prefixEnd_4744796 : Nat := 4983230072969 + 3 ^ 40 * 4744796 * 2
def baseEnd_4744796 : Nat := 2436360955530523197529087

theorem tailTrace_4744796 : CollatzResearch.WordTrace tailWord_4744796 prefixEnd_4744796 2436360955530523197529087 := by
  unfold tailWord_4744796
  simp only [CollatzResearch.WordTrace]
  refine ⟨86528463659210956743459121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115371284878947942324612161 86528463659210956743459121)
  ·
    refine ⟨64896347744408217557594341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86528463659210956743459121 64896347744408217557594341)
    ·
      refine ⟨12168065202076540792048939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64896347744408217557594341 12168065202076540792048939)
      ·
        refine ⟨18252097803114811188073409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12168065202076540792048939 18252097803114811188073409)
        ·
          refine ⟨13689073352336108391055057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18252097803114811188073409 13689073352336108391055057)
          ·
            refine ⟨10266805014252081293291293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13689073352336108391055057 10266805014252081293291293)
            ·
              refine ⟨3850051880344530484984235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10266805014252081293291293 3850051880344530484984235)
              ·
                refine ⟨5775077820516795727476353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3850051880344530484984235 5775077820516795727476353)
                ·
                  refine ⟨4331308365387596795607265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5775077820516795727476353 4331308365387596795607265)
                  ·
                    refine ⟨3248481274040697596705449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4331308365387596795607265 3248481274040697596705449)
                    ·
                      refine ⟨2436360955530523197529087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3248481274040697596705449 2436360955530523197529087)
                      ·
                        rfl

theorem cell23_4744796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_4744796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744796 prefixEnd_4744796 := by exact prefixLift 4744796
  have htrace : WordTrace (prefixWord ++ tailWord_4744796) baseStart_4744796 baseEnd_4744796 := by
    simpa [prefixWord, tailWord_4744796, baseEnd_4744796] using wordTrace_append hprefix tailTrace_4744796
  have hstable : (prefixWord ++ tailWord_4744796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744796).length < 2 ^ (prefixWord ++ tailWord_4744796).sum := by decide
  have hdescent : baseEnd_4744796 < baseStart_4744796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744936 : List Nat := [2, 1, 4, 1, 3, 2, 2, 3, 1, 1, 3]
def baseStart_4744936 : Nat := 118140960795 + 4744936 * 2 ^ 59
def prefixEnd_4744936 : Nat := 4983230072969 + 3 ^ 40 * 4744936 * 2
def baseEnd_4744936 : Nat := 2436432842822152649778443

theorem tailTrace_4744936 : CollatzResearch.WordTrace tailWord_4744936 prefixEnd_4744936 2436432842822152649778443 := by
  unfold tailWord_4744936
  simp only [CollatzResearch.WordTrace]
  refine ⟨86531016768957358698507331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115374689025276478264676441 86531016768957358698507331)
  ·
    refine ⟨129796525153436038047760997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86531016768957358698507331 129796525153436038047760997)
    ·
      refine ⟨24336848466269257133955187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129796525153436038047760997 24336848466269257133955187)
      ·
        refine ⟨36505272699403885700932781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24336848466269257133955187 36505272699403885700932781)
        ·
          refine ⟨13689477262276457137849793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36505272699403885700932781 13689477262276457137849793)
          ·
            refine ⟨10267107946707342853387345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13689477262276457137849793 10267107946707342853387345)
            ·
              refine ⟨7700330960030507140040509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10267107946707342853387345 7700330960030507140040509)
              ·
                refine ⟨2887624110011440177515191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7700330960030507140040509 2887624110011440177515191)
                ·
                  refine ⟨4331436165017160266272787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2887624110011440177515191 4331436165017160266272787)
                  ·
                    refine ⟨6497154247525740399409181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4331436165017160266272787 6497154247525740399409181)
                    ·
                      refine ⟨2436432842822152649778443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6497154247525740399409181 2436432842822152649778443)
                      ·
                        rfl

theorem cell23_4744936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_4744936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744936 prefixEnd_4744936 := by exact prefixLift 4744936
  have htrace : WordTrace (prefixWord ++ tailWord_4744936) baseStart_4744936 baseEnd_4744936 := by
    simpa [prefixWord, tailWord_4744936, baseEnd_4744936] using wordTrace_append hprefix tailTrace_4744936
  have hstable : (prefixWord ++ tailWord_4744936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744936).length < 2 ^ (prefixWord ++ tailWord_4744936).sum := by decide
  have hdescent : baseEnd_4744936 < baseStart_4744936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744942 : List Nat := [4, 1, 2, 1, 1, 2, 3, 3, 1, 1, 4]
def baseStart_4744942 : Nat := 118140960795 + 4744942 * 2 ^ 59
def prefixEnd_4744942 : Nat := 4983230072969 + 3 ^ 40 * 4744942 * 2
def baseEnd_4744942 : Nat := 2436435923706079626303415

theorem tailTrace_4744942 : CollatzResearch.WordTrace tailWord_4744942 prefixEnd_4744942 2436435923706079626303415 := by
  unfold tailWord_4744942
  simp only [CollatzResearch.WordTrace]
  refine ⟨21632781546986622552716635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115374834917261986947822053 21632781546986622552716635)
  ·
    refine ⟨32449172320479933829074953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21632781546986622552716635 32449172320479933829074953)
    ·
      refine ⟨24336879240359950371806215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32449172320479933829074953 24336879240359950371806215)
      ·
        refine ⟨36505318860539925557709323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24336879240359950371806215 36505318860539925557709323)
        ·
          refine ⟨54757978290809888336563985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36505318860539925557709323 54757978290809888336563985)
          ·
            refine ⟨41068483718107416252422989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54757978290809888336563985 41068483718107416252422989)
            ·
              refine ⟨15400681394290281094658621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41068483718107416252422989 15400681394290281094658621)
              ·
                refine ⟨5775255522858855410496983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15400681394290281094658621 5775255522858855410496983)
                ·
                  refine ⟨8662883284288283115745475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5775255522858855410496983 8662883284288283115745475)
                  ·
                    refine ⟨12994324926432424673618213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8662883284288283115745475 12994324926432424673618213)
                    ·
                      refine ⟨2436435923706079626303415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12994324926432424673618213 2436435923706079626303415)
                      ·
                        rfl

theorem cell23_4744942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_4744942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744942 prefixEnd_4744942 := by exact prefixLift 4744942
  have htrace : WordTrace (prefixWord ++ tailWord_4744942) baseStart_4744942 baseEnd_4744942 := by
    simpa [prefixWord, tailWord_4744942, baseEnd_4744942] using wordTrace_append hprefix tailTrace_4744942
  have hstable : (prefixWord ++ tailWord_4744942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744942).length < 2 ^ (prefixWord ++ tailWord_4744942).sum := by decide
  have hdescent : baseEnd_4744942 < baseStart_4744942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744962 : List Nat := [3, 4, 1, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_4744962 : Nat := 118140960795 + 4744962 * 2 ^ 59
def prefixEnd_4744962 : Nat := 4983230072969 + 3 ^ 40 * 4744962 * 2
def baseEnd_4744962 : Nat := 2436446193319169548053323

theorem tailTrace_4744962 : CollatzResearch.WordTrace tailWord_4744962 prefixEnd_4744962 2436446193319169548053323 := by
  unfold tailWord_4744962
  simp only [CollatzResearch.WordTrace]
  refine ⟨43265745458955130959365285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115375321223880349224974093 43265745458955130959365285)
  ·
    refine ⟨8112327273554087054880991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43265745458955130959365285 8112327273554087054880991)
    ·
      refine ⟨12168490910331130582321487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8112327273554087054880991 12168490910331130582321487)
      ·
        refine ⟨18252736365496695873482231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12168490910331130582321487 18252736365496695873482231)
        ·
          refine ⟨27379104548245043810223347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18252736365496695873482231 27379104548245043810223347)
          ·
            refine ⟨41068656822367565715335021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27379104548245043810223347 41068656822367565715335021)
            ·
              refine ⟨15400746308387837143250633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41068656822367565715335021 15400746308387837143250633)
              ·
                refine ⟨11550559731290877857437975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15400746308387837143250633 11550559731290877857437975)
                ·
                  refine ⟨17325839596936316786156963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11550559731290877857437975 17325839596936316786156963)
                  ·
                    refine ⟨25988759395404475179235445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17325839596936316786156963 25988759395404475179235445)
                    ·
                      refine ⟨2436446193319169548053323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25988759395404475179235445 2436446193319169548053323)
                      ·
                        rfl

theorem cell23_4744962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_4744962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744962 prefixEnd_4744962 := by exact prefixLift 4744962
  have htrace : WordTrace (prefixWord ++ tailWord_4744962) baseStart_4744962 baseEnd_4744962 := by
    simpa [prefixWord, tailWord_4744962, baseEnd_4744962] using wordTrace_append hprefix tailTrace_4744962
  have hstable : (prefixWord ++ tailWord_4744962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744962).length < 2 ^ (prefixWord ++ tailWord_4744962).sum := by decide
  have hdescent : baseEnd_4744962 < baseStart_4744962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744975 : List Nat := [1, 1, 2, 1, 1, 1, 4, 5, 1, 3, 3]
def baseStart_4744975 : Nat := 118140960795 + 4744975 * 2 ^ 59
def prefixEnd_4744975 : Nat := 4983230072969 + 3 ^ 40 * 4744975 * 2
def baseEnd_4744975 : Nat := 2436452868567677997190763

theorem tailTrace_4744975 : CollatzResearch.WordTrace tailWord_4744975 prefixEnd_4744975 2436452868567677997190763 := by
  unfold tailWord_4744975
  simp only [CollatzResearch.WordTrace]
  refine ⟨173063455984773427057684379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115375637323182284705122919 173063455984773427057684379)
  ·
    refine ⟨259595183977160140586526569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173063455984773427057684379 259595183977160140586526569)
    ·
      refine ⟨194696387982870105439894927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259595183977160140586526569 194696387982870105439894927)
      ·
        refine ⟨292044581974305158159842391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194696387982870105439894927 292044581974305158159842391)
        ·
          refine ⟨438066872961457737239763587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292044581974305158159842391 438066872961457737239763587)
          ·
            refine ⟨657100309442186605859645381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438066872961457737239763587 657100309442186605859645381)
            ·
              refine ⟨123206308020409988598683509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 657100309442186605859645381 123206308020409988598683509)
              ·
                refine ⟨11550591376913436431126579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 123206308020409988598683509 11550591376913436431126579)
                ·
                  refine ⟨17325887065370154646689869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11550591376913436431126579 17325887065370154646689869)
                  ·
                    refine ⟨6497207649513807992508701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17325887065370154646689869 6497207649513807992508701)
                    ·
                      refine ⟨2436452868567677997190763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6497207649513807992508701 2436452868567677997190763)
                      ·
                        rfl

theorem cell23_4744975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3, 3].length) (baseStart_4744975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744975 prefixEnd_4744975 := by exact prefixLift 4744975
  have htrace : WordTrace (prefixWord ++ tailWord_4744975) baseStart_4744975 baseEnd_4744975 := by
    simpa [prefixWord, tailWord_4744975, baseEnd_4744975] using wordTrace_append hprefix tailTrace_4744975
  have hstable : (prefixWord ++ tailWord_4744975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744975).length < 2 ^ (prefixWord ++ tailWord_4744975).sum := by decide
  have hdescent : baseEnd_4744975 < baseStart_4744975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744992 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 6, 1, 3]
def baseStart_4744992 : Nat := 118140960795 + 4744992 * 2 ^ 59
def prefixEnd_4744992 : Nat := 4983230072969 + 3 ^ 40 * 4744992 * 2
def baseEnd_4744992 : Nat := 2436461597738804430678185

theorem tailTrace_4744992 : CollatzResearch.WordTrace tailWord_4744992 prefixEnd_4744992 2436461597738804430678185 := by
  unfold tailWord_4744992
  simp only [CollatzResearch.WordTrace]
  refine ⟨86532038012855919480526615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115376050683807892640702153 86532038012855919480526615)
  ·
    refine ⟨129798057019283879220789923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86532038012855919480526615 129798057019283879220789923)
    ·
      refine ⟨194697085528925818831184885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129798057019283879220789923 194697085528925818831184885)
      ·
        refine ⟨18252851768336795515423583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 194697085528925818831184885 18252851768336795515423583)
        ·
          refine ⟨27379277652505193273135375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18252851768336795515423583 27379277652505193273135375)
          ·
            refine ⟨41068916478757789909703063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27379277652505193273135375 41068916478757789909703063)
            ·
              refine ⟨61603374718136684864554595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41068916478757789909703063 61603374718136684864554595)
              ·
                refine ⟨92405062077205027296831893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61603374718136684864554595 92405062077205027296831893)
                ·
                  refine ⟨4331487284868985654538995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 92405062077205027296831893 4331487284868985654538995)
                  ·
                    refine ⟨6497230927303478481808493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4331487284868985654538995 6497230927303478481808493)
                    ·
                      refine ⟨2436461597738804430678185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6497230927303478481808493 2436461597738804430678185)
                      ·
                        rfl

theorem cell23_4744992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_4744992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744992 prefixEnd_4744992 := by exact prefixLift 4744992
  have htrace : WordTrace (prefixWord ++ tailWord_4744992) baseStart_4744992 baseEnd_4744992 := by
    simpa [prefixWord, tailWord_4744992, baseEnd_4744992] using wordTrace_append hprefix tailTrace_4744992
  have hstable : (prefixWord ++ tailWord_4744992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744992).length < 2 ^ (prefixWord ++ tailWord_4744992).sum := by decide
  have hdescent : baseEnd_4744992 < baseStart_4744992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4744993 : List Nat := [1, 2, 3, 2, 1, 5, 1, 3, 1, 2, 2]
def baseStart_4744993 : Nat := 118140960795 + 4744993 * 2 ^ 59
def prefixEnd_4744993 : Nat := 4983230072969 + 3 ^ 40 * 4744993 * 2
def baseEnd_4744993 : Nat := 2436462111219458926765681

theorem tailTrace_4744993 : CollatzResearch.WordTrace tailWord_4744993 prefixEnd_4744993 2436462111219458926765681 := by
  unfold tailWord_4744993
  simp only [CollatzResearch.WordTrace]
  refine ⟨173064112498708216131839633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115376074999138810754559755 173064112498708216131839633)
  ·
    refine ⟨129798084374031162098879725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173064112498708216131839633 129798084374031162098879725)
    ·
      refine ⟨48674281640261685787079897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129798084374031162098879725 48674281640261685787079897)
      ·
        refine ⟨36505711230196264340309923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48674281640261685787079897 36505711230196264340309923)
        ·
          refine ⟨54758566845294396510464885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36505711230196264340309923 54758566845294396510464885)
          ·
            refine ⟨5133615641746349672856083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54758566845294396510464885 5133615641746349672856083)
            ·
              refine ⟨7700423462619524509284125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5133615641746349672856083 7700423462619524509284125)
              ·
                refine ⟨2887658798482321690981547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7700423462619524509284125 2887658798482321690981547)
                ·
                  refine ⟨4331488197723482536472321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2887658798482321690981547 4331488197723482536472321)
                  ·
                    refine ⟨3248616148292611902354241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4331488197723482536472321 3248616148292611902354241)
                    ·
                      refine ⟨2436462111219458926765681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3248616148292611902354241 2436462111219458926765681)
                      ·
                        rfl

theorem cell23_4744993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_4744993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4744993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4744993 prefixEnd_4744993 := by exact prefixLift 4744993
  have htrace : WordTrace (prefixWord ++ tailWord_4744993) baseStart_4744993 baseEnd_4744993 := by
    simpa [prefixWord, tailWord_4744993, baseEnd_4744993] using wordTrace_append hprefix tailTrace_4744993
  have hstable : (prefixWord ++ tailWord_4744993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4744993).length < 2 ^ (prefixWord ++ tailWord_4744993).sum := by decide
  have hdescent : baseEnd_4744993 < baseStart_4744993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4744993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745065 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 3, 5, 3]
def baseStart_4745065 : Nat := 118140960795 + 4745065 * 2 ^ 59
def prefixEnd_4745065 : Nat := 4983230072969 + 3 ^ 40 * 4745065 * 2
def baseEnd_4745065 : Nat := 2436499081826582645065349

theorem tailTrace_4745065 : CollatzResearch.WordTrace tailWord_4745065 prefixEnd_4745065 2436499081826582645065349 := by
  unfold tailWord_4745065
  simp only [CollatzResearch.WordTrace]
  refine ⟨173066738554447372428460649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115377825702964914952307099 173066738554447372428460649)
  ·
    refine ⟨129800053915835529321345487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173066738554447372428460649 129800053915835529321345487)
    ·
      refine ⟨194700080873753293982018231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129800053915835529321345487 194700080873753293982018231)
      ·
        refine ⟨292050121310629940973027347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194700080873753293982018231 292050121310629940973027347)
        ·
          refine ⟨438075181965944911459541021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292050121310629940973027347 438075181965944911459541021)
          ·
            refine ⟨164278193237229341797327883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 438075181965944911459541021 164278193237229341797327883)
            ·
              refine ⟨246417289855844012695991825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164278193237229341797327883 246417289855844012695991825)
              ·
                refine ⟨184812967391883009521993869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246417289855844012695991825 184812967391883009521993869)
                ·
                  refine ⟨69304862771956128570747701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 184812967391883009521993869 69304862771956128570747701)
                  ·
                    refine ⟨6497330884870887053507597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69304862771956128570747701 6497330884870887053507597)
                    ·
                      refine ⟨2436499081826582645065349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6497330884870887053507597 2436499081826582645065349)
                      ·
                        rfl

theorem cell23_4745065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 5, 3].length) (baseStart_4745065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745065 prefixEnd_4745065 := by exact prefixLift 4745065
  have htrace : WordTrace (prefixWord ++ tailWord_4745065) baseStart_4745065 baseEnd_4745065 := by
    simpa [prefixWord, tailWord_4745065, baseEnd_4745065] using wordTrace_append hprefix tailTrace_4745065
  have hstable : (prefixWord ++ tailWord_4745065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745065).length < 2 ^ (prefixWord ++ tailWord_4745065).sum := by decide
  have hdescent : baseEnd_4745065 < baseStart_4745065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745085 : List Nat := [1, 4, 1, 1, 2, 1, 1, 4, 1, 7]
def baseStart_4745085 : Nat := 118140960795 + 4745085 * 2 ^ 59
def prefixEnd_4745085 : Nat := 4983230072969 + 3 ^ 40 * 4745085 * 2
def baseEnd_4745085 : Nat := 812169783813224188938419

theorem tailTrace_4745085 : CollatzResearch.WordTrace tailWord_4745085 prefixEnd_4745085 812169783813224188938419 := by
  unfold tailWord_4745085
  simp only [CollatzResearch.WordTrace]
  refine ⟨173067468014374915844188709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115378312009583277229459139 173067468014374915844188709)
  ·
    refine ⟨32450150252695296720785383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173067468014374915844188709 32450150252695296720785383)
    ·
      refine ⟨48675225379042945081178075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32450150252695296720785383 48675225379042945081178075)
      ·
        refine ⟨73012838068564417621767113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48675225379042945081178075 73012838068564417621767113)
        ·
          refine ⟨54759628551423313216325335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73012838068564417621767113 54759628551423313216325335)
          ·
            refine ⟨82139442827134969824488003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54759628551423313216325335 82139442827134969824488003)
            ·
              refine ⟨123209164240702454736732005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82139442827134969824488003 123209164240702454736732005)
              ·
                refine ⟨23101718295131710263137251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123209164240702454736732005 23101718295131710263137251)
                ·
                  refine ⟨34652577442697565394705877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23101718295131710263137251 34652577442697565394705877)
                  ·
                    refine ⟨812169783813224188938419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34652577442697565394705877 812169783813224188938419)
                    ·
                      rfl

theorem cell23_4745085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_4745085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745085 prefixEnd_4745085 := by exact prefixLift 4745085
  have htrace : WordTrace (prefixWord ++ tailWord_4745085) baseStart_4745085 baseEnd_4745085 := by
    simpa [prefixWord, tailWord_4745085, baseEnd_4745085] using wordTrace_append hprefix tailTrace_4745085
  have hstable : (prefixWord ++ tailWord_4745085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745085).length < 2 ^ (prefixWord ++ tailWord_4745085).sum := by decide
  have hdescent : baseEnd_4745085 < baseStart_4745085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745089 : List Nat := [1, 2, 4, 4, 1, 1, 1, 2, 7]
def baseStart_4745089 : Nat := 118140960795 + 4745089 * 2 ^ 59
def prefixEnd_4745089 : Nat := 4983230072969 + 3 ^ 40 * 4745089 * 2
def baseEnd_4745089 : Nat := 270723489484698950129471

theorem tailTrace_4745089 : CollatzResearch.WordTrace tailWord_4745089 prefixEnd_4745089 270723489484698950129471 := by
  unfold tailWord_4745089
  simp only [CollatzResearch.WordTrace]
  refine ⟨173067613906360424527334321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115378409270906949684889547 173067613906360424527334321)
  ·
    refine ⟨129800710429770318395500741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173067613906360424527334321 129800710429770318395500741)
    ·
      refine ⟨24337633205581934699156389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129800710429770318395500741 24337633205581934699156389)
      ·
        refine ⟨4563306226046612756091823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24337633205581934699156389 4563306226046612756091823)
        ·
          refine ⟨6844959339069919134137735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4563306226046612756091823 6844959339069919134137735)
          ·
            refine ⟨10267439008604878701206603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6844959339069919134137735 10267439008604878701206603)
            ·
              refine ⟨15401158512907318051809905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10267439008604878701206603 15401158512907318051809905)
              ·
                refine ⟨11550868884680488538857429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15401158512907318051809905 11550868884680488538857429)
                ·
                  refine ⟨270723489484698950129471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11550868884680488538857429 270723489484698950129471)
                  ·
                    rfl

theorem cell23_4745089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 7].length) (baseStart_4745089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745089 prefixEnd_4745089 := by exact prefixLift 4745089
  have htrace : WordTrace (prefixWord ++ tailWord_4745089) baseStart_4745089 baseEnd_4745089 := by
    simpa [prefixWord, tailWord_4745089, baseEnd_4745089] using wordTrace_append hprefix tailTrace_4745089
  have hstable : (prefixWord ++ tailWord_4745089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745089).length < 2 ^ (prefixWord ++ tailWord_4745089).sum := by decide
  have hdescent : baseEnd_4745089 < baseStart_4745089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745106 : List Nat := [3, 2, 3, 2, 1, 2, 2, 3, 5]
def baseStart_4745106 : Nat := 118140960795 + 4745106 * 2 ^ 59
def prefixEnd_4745106 : Nat := 4983230072969 + 3 ^ 40 * 4745106 * 2
def baseEnd_4745106 : Nat := 270724459392601887183629

theorem tailTrace_4745106 : CollatzResearch.WordTrace tailWord_4745106 prefixEnd_4745106 270724459392601887183629 := by
  unfold tailWord_4745106
  simp only [CollatzResearch.WordTrace]
  refine ⟨43267058486824709107675793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115378822631532557620468781 43267058486824709107675793)
  ·
    refine ⟨32450293865118531830756845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43267058486824709107675793 32450293865118531830756845)
    ·
      refine ⟨12168860199419449436533817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32450293865118531830756845 12168860199419449436533817)
      ·
        refine ⟨9126645149564587077400363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12168860199419449436533817 9126645149564587077400363)
        ·
          refine ⟨13689967724346880616100545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9126645149564587077400363 13689967724346880616100545)
          ·
            refine ⟨10267475793260160462075409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13689967724346880616100545 10267475793260160462075409)
            ·
              refine ⟨7700606844945120346556557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10267475793260160462075409 7700606844945120346556557)
              ·
                refine ⟨2887727566854420129958709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7700606844945120346556557 2887727566854420129958709)
                ·
                  refine ⟨270724459392601887183629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2887727566854420129958709 270724459392601887183629)
                  ·
                    rfl

theorem cell23_4745106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3, 5].length) (baseStart_4745106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745106 prefixEnd_4745106 := by exact prefixLift 4745106
  have htrace : WordTrace (prefixWord ++ tailWord_4745106) baseStart_4745106 baseEnd_4745106 := by
    simpa [prefixWord, tailWord_4745106, baseEnd_4745106] using wordTrace_append hprefix tailTrace_4745106
  have hstable : (prefixWord ++ tailWord_4745106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745106).length < 2 ^ (prefixWord ++ tailWord_4745106).sum := by decide
  have hdescent : baseEnd_4745106 < baseStart_4745106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745125 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 2, 3, 5]
def baseStart_4745125 : Nat := 118140960795 + 4745125 * 2 ^ 59
def prefixEnd_4745125 : Nat := 4983230072969 + 3 ^ 40 * 4745125 * 2
def baseEnd_4745125 : Nat := 2436529890665852410315073

theorem tailTrace_4745125 : CollatzResearch.WordTrace tailWord_4745125 prefixEnd_4745125 2436529890665852410315073 := by
  unfold tailWord_4745125
  simp only [CollatzResearch.WordTrace]
  refine ⟨173068926934230002675644829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115379284622820001783763219 173068926934230002675644829)
  ·
    refine ⟨64900847600336251003366811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173068926934230002675644829 64900847600336251003366811)
    ·
      refine ⟨97351271400504376505050217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64900847600336251003366811 97351271400504376505050217)
      ·
        refine ⟨73013453550378282378787663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97351271400504376505050217 73013453550378282378787663)
        ·
          refine ⟨109520180325567423568181495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73013453550378282378787663 109520180325567423568181495)
          ·
            refine ⟨164280270488351135352272243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109520180325567423568181495 164280270488351135352272243)
            ·
              refine ⟨246420405732526703028408365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164280270488351135352272243 246420405732526703028408365)
              ·
                refine ⟨92407652149697513635653137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 246420405732526703028408365 92407652149697513635653137)
                ·
                  refine ⟨69305739112273135226739853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92407652149697513635653137 69305739112273135226739853)
                  ·
                    refine ⟨25989652167102425710027445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69305739112273135226739853 25989652167102425710027445)
                    ·
                      refine ⟨2436529890665852410315073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25989652167102425710027445 2436529890665852410315073)
                      ·
                        rfl

theorem cell23_4745125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_4745125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745125 prefixEnd_4745125 := by exact prefixLift 4745125
  have htrace : WordTrace (prefixWord ++ tailWord_4745125) baseStart_4745125 baseEnd_4745125 := by
    simpa [prefixWord, tailWord_4745125, baseEnd_4745125] using wordTrace_append hprefix tailTrace_4745125
  have hstable : (prefixWord ++ tailWord_4745125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745125).length < 2 ^ (prefixWord ++ tailWord_4745125).sum := by decide
  have hdescent : baseEnd_4745125 < baseStart_4745125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745134 : List Nat := [4, 1, 5, 1, 1, 1, 3, 1, 2, 2, 2]
def baseStart_4745134 : Nat := 118140960795 + 4745134 * 2 ^ 59
def prefixEnd_4745134 : Nat := 4983230072969 + 3 ^ 40 * 4745134 * 2
def baseEnd_4745134 : Nat := 2436534511991742875102533

theorem tailTrace_4745134 : CollatzResearch.WordTrace tailWord_4745134 prefixEnd_4745134 2436534511991742875102533 := by
  unfold tailWord_4745134
  simp only [CollatzResearch.WordTrace]
  refine ⟨21633656898899674651590307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115379503460798264808481637 21633656898899674651590307)
  ·
    refine ⟨32450485348349511977385461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21633656898899674651590307 32450485348349511977385461)
    ·
      refine ⟨3042233001407766747879887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32450485348349511977385461 3042233001407766747879887)
      ·
        refine ⟨4563349502111650121819831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3042233001407766747879887 4563349502111650121819831)
        ·
          refine ⟨6845024253167475182729747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4563349502111650121819831 6845024253167475182729747)
          ·
            refine ⟨10267536379751212774094621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6845024253167475182729747 10267536379751212774094621)
            ·
              refine ⟨3850326142406704790285483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10267536379751212774094621 3850326142406704790285483)
              ·
                refine ⟨5775489213610057185428225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3850326142406704790285483 5775489213610057185428225)
                ·
                  refine ⟨4331616910207542889071169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5775489213610057185428225 4331616910207542889071169)
                  ·
                    refine ⟨3248712682655657166803377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4331616910207542889071169 3248712682655657166803377)
                    ·
                      refine ⟨2436534511991742875102533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3248712682655657166803377 2436534511991742875102533)
                      ·
                        rfl

theorem cell23_4745134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_4745134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745134 prefixEnd_4745134 := by exact prefixLift 4745134
  have htrace : WordTrace (prefixWord ++ tailWord_4745134) baseStart_4745134 baseEnd_4745134 := by
    simpa [prefixWord, tailWord_4745134, baseEnd_4745134] using wordTrace_append hprefix tailTrace_4745134
  have hstable : (prefixWord ++ tailWord_4745134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745134).length < 2 ^ (prefixWord ++ tailWord_4745134).sum := by decide
  have hdescent : baseEnd_4745134 < baseStart_4745134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745135 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 6]
def baseStart_4745135 : Nat := 118140960795 + 4745135 * 2 ^ 59
def prefixEnd_4745135 : Nat := 4983230072969 + 3 ^ 40 * 4745135 * 2
def baseEnd_4745135 : Nat := 2436535025472397371190027

theorem tailTrace_4745135 : CollatzResearch.WordTrace tailWord_4745135 prefixEnd_4745135 2436535025472397371190027 := by
  unfold tailWord_4745135
  simp only [CollatzResearch.WordTrace]
  refine ⟨173069291664193774383508859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115379527776129182922339239 173069291664193774383508859)
  ·
    refine ⟨259603937496290661575263289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173069291664193774383508859 259603937496290661575263289)
    ·
      refine ⟨194702953122217996181447467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259603937496290661575263289 194702953122217996181447467)
      ·
        refine ⟨292054429683326994272171201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194702953122217996181447467 292054429683326994272171201)
        ·
          refine ⟨219040822262495245704128401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292054429683326994272171201 219040822262495245704128401)
          ·
            refine ⟨164280616696871434278096301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219040822262495245704128401 164280616696871434278096301)
            ·
              refine ⟨61605231261326787854286113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164280616696871434278096301 61605231261326787854286113)
              ·
                refine ⟨46203923445995090890714585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61605231261326787854286113 46203923445995090890714585)
                ·
                  refine ⟨34652942584496318168035939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46203923445995090890714585 34652942584496318168035939)
                  ·
                    refine ⟨51979413876744477252053909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34652942584496318168035939 51979413876744477252053909)
                    ·
                      refine ⟨2436535025472397371190027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51979413876744477252053909 2436535025472397371190027)
                      ·
                        rfl

theorem cell23_4745135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 6].length) (baseStart_4745135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745135 prefixEnd_4745135 := by exact prefixLift 4745135
  have htrace : WordTrace (prefixWord ++ tailWord_4745135) baseStart_4745135 baseEnd_4745135 := by
    simpa [prefixWord, tailWord_4745135, baseEnd_4745135] using wordTrace_append hprefix tailTrace_4745135
  have hstable : (prefixWord ++ tailWord_4745135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745135).length < 2 ^ (prefixWord ++ tailWord_4745135).sum := by decide
  have hdescent : baseEnd_4745135 < baseStart_4745135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745149 : List Nat := [1, 4, 1, 2, 3, 1, 2, 2, 3, 4]
def baseStart_4745149 : Nat := 118140960795 + 4745149 * 2 ^ 59
def prefixEnd_4745149 : Nat := 4983230072969 + 3 ^ 40 * 4745149 * 2
def baseEnd_4745149 : Nat := 812180738067186772138321

theorem tailTrace_4745149 : CollatzResearch.WordTrace tailWord_4745149 prefixEnd_4745149 812180738067186772138321 := by
  unfold tailWord_4745149
  simp only [CollatzResearch.WordTrace]
  refine ⟨173069802286143054774518501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115379868190762036516345667 173069802286143054774518501)
  ·
    refine ⟨32450587928651822770222219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173069802286143054774518501 32450587928651822770222219)
    ·
      refine ⟨48675881892977734155333329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32450587928651822770222219 48675881892977734155333329)
      ·
        refine ⟨36506911419733300616499997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48675881892977734155333329 36506911419733300616499997)
        ·
          refine ⟨13690091782399987731187499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36506911419733300616499997 13690091782399987731187499)
          ·
            refine ⟨20535137673599981596781249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13690091782399987731187499 20535137673599981596781249)
            ·
              refine ⟨15401353255199986197585937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20535137673599981596781249 15401353255199986197585937)
              ·
                refine ⟨11551014941399989648189453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15401353255199986197585937 11551014941399989648189453)
                ·
                  refine ⟨4331630603024996118071045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11551014941399989648189453 4331630603024996118071045)
                  ·
                    refine ⟨812180738067186772138321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4331630603024996118071045 812180738067186772138321)
                    ·
                      rfl

theorem cell23_4745149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_4745149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745149 prefixEnd_4745149 := by exact prefixLift 4745149
  have htrace : WordTrace (prefixWord ++ tailWord_4745149) baseStart_4745149 baseEnd_4745149 := by
    simpa [prefixWord, tailWord_4745149, baseEnd_4745149] using wordTrace_append hprefix tailTrace_4745149
  have hstable : (prefixWord ++ tailWord_4745149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745149).length < 2 ^ (prefixWord ++ tailWord_4745149).sum := by decide
  have hdescent : baseEnd_4745149 < baseStart_4745149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745183 : List Nat := [1, 1, 2, 3, 4, 2, 3, 2, 1, 4]
def baseStart_4745183 : Nat := 118140960795 + 4745183 * 2 ^ 59
def prefixEnd_4745183 : Nat := 4983230072969 + 3 ^ 40 * 4745183 * 2
def baseEnd_4745183 : Nat := 812186557514604394463269

theorem tailTrace_4745183 : CollatzResearch.WordTrace tailWord_4745183 prefixEnd_4745183 812186557514604394463269 := by
  unfold tailWord_4745183
  simp only [CollatzResearch.WordTrace]
  refine ⟨173071042368019878581256203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115380694912013252387504135 173071042368019878581256203)
  ·
    refine ⟨259606563552029817871884305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173071042368019878581256203 259606563552029817871884305)
    ·
      refine ⟨194704922664022363403913229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259606563552029817871884305 194704922664022363403913229)
      ·
        refine ⟨73014345999008386276467461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194704922664022363403913229 73014345999008386276467461)
        ·
          refine ⟨13690189874814072426837649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73014345999008386276467461 13690189874814072426837649)
          ·
            refine ⟨10267642406110554320128237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13690189874814072426837649 10267642406110554320128237)
            ·
              refine ⟨3850365902291457870048089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10267642406110554320128237 3850365902291457870048089)
              ·
                refine ⟨2887774426718593402536067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3850365902291457870048089 2887774426718593402536067)
                ·
                  refine ⟨4331661640077890103804101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2887774426718593402536067 4331661640077890103804101)
                  ·
                    refine ⟨812186557514604394463269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4331661640077890103804101 812186557514604394463269)
                    ·
                      rfl

theorem cell23_4745183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2, 1, 4].length) (baseStart_4745183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745183 prefixEnd_4745183 := by exact prefixLift 4745183
  have htrace : WordTrace (prefixWord ++ tailWord_4745183) baseStart_4745183 baseEnd_4745183 := by
    simpa [prefixWord, tailWord_4745183, baseEnd_4745183] using wordTrace_append hprefix tailTrace_4745183
  have hstable : (prefixWord ++ tailWord_4745183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745183).length < 2 ^ (prefixWord ++ tailWord_4745183).sum := by decide
  have hdescent : baseEnd_4745183 < baseStart_4745183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745192 : List Nat := [2, 1, 4, 1, 1, 1, 1, 4, 3, 5]
def baseStart_4745192 : Nat := 118140960795 + 4745192 * 2 ^ 59
def prefixEnd_4745192 : Nat := 4983230072969 + 3 ^ 40 * 4745192 * 2
def baseEnd_4745192 : Nat := 812188097956567882725755

theorem tailTrace_4745192 : CollatzResearch.WordTrace tailWord_4745192 prefixEnd_4745192 812188097956567882725755 := by
  unfold tailWord_4745192
  simp only [CollatzResearch.WordTrace]
  refine ⟨86535685312493636559166915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115380913749991515412222553 86535685312493636559166915)
  ·
    refine ⟨129803527968740454838750373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86535685312493636559166915 129803527968740454838750373)
    ·
      refine ⟨24338161494138835282265695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129803527968740454838750373 24338161494138835282265695)
      ·
        refine ⟨36507242241208252923398543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24338161494138835282265695 36507242241208252923398543)
        ·
          refine ⟨54760863361812379385097815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36507242241208252923398543 54760863361812379385097815)
          ·
            refine ⟨82141295042718569077646723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54760863361812379385097815 82141295042718569077646723)
            ·
              refine ⟨123211942564077853616470085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82141295042718569077646723 123211942564077853616470085)
              ·
                refine ⟨23102239230764597553088141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123211942564077853616470085 23102239230764597553088141)
                ·
                  refine ⟨8663339711536724082408053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23102239230764597553088141 8663339711536724082408053)
                  ·
                    refine ⟨812188097956567882725755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8663339711536724082408053 812188097956567882725755)
                    ·
                      rfl

theorem cell23_4745192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_4745192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745192 prefixEnd_4745192 := by exact prefixLift 4745192
  have htrace : WordTrace (prefixWord ++ tailWord_4745192) baseStart_4745192 baseEnd_4745192 := by
    simpa [prefixWord, tailWord_4745192, baseEnd_4745192] using wordTrace_append hprefix tailTrace_4745192
  have hstable : (prefixWord ++ tailWord_4745192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745192).length < 2 ^ (prefixWord ++ tailWord_4745192).sum := by decide
  have hdescent : baseEnd_4745192 < baseStart_4745192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745199 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 4, 3, 2]
def baseStart_4745199 : Nat := 118140960795 + 4745199 * 2 ^ 59
def prefixEnd_4745199 : Nat := 4983230072969 + 3 ^ 40 * 4745199 * 2
def baseEnd_4745199 : Nat := 2436567888234285120789733

theorem tailTrace_4745199 : CollatzResearch.WordTrace tailWord_4745199 prefixEnd_4745199 2436567888234285120789733 := by
  unfold tailWord_4745199
  simp only [CollatzResearch.WordTrace]
  refine ⟨173071625935961913313838651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115381083957307942209225767 173071625935961913313838651)
  ·
    refine ⟨259607438903942869970757977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173071625935961913313838651 259607438903942869970757977)
    ·
      refine ⟨194705579177957152478068483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259607438903942869970757977 194705579177957152478068483)
      ·
        refine ⟨292058368766935728717102725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194705579177957152478068483 292058368766935728717102725)
        ·
          refine ⟨54760944143800449134456761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 292058368766935728717102725 54760944143800449134456761)
          ·
            refine ⟨41070708107850336850842571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54760944143800449134456761 41070708107850336850842571)
            ·
              refine ⟨61606062161775505276263857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41070708107850336850842571 61606062161775505276263857)
              ·
                refine ⟨46204546621331628957197893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61606062161775505276263857 46204546621331628957197893)
                ·
                  refine ⟨8663352491499680429474605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46204546621331628957197893 8663352491499680429474605)
                  ·
                    refine ⟨3248757184312380161052977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8663352491499680429474605 3248757184312380161052977)
                    ·
                      refine ⟨2436567888234285120789733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3248757184312380161052977 2436567888234285120789733)
                      ·
                        rfl

theorem cell23_4745199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 3, 2].length) (baseStart_4745199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745199 prefixEnd_4745199 := by exact prefixLift 4745199
  have htrace : WordTrace (prefixWord ++ tailWord_4745199) baseStart_4745199 baseEnd_4745199 := by
    simpa [prefixWord, tailWord_4745199, baseEnd_4745199] using wordTrace_append hprefix tailTrace_4745199
  have hstable : (prefixWord ++ tailWord_4745199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745199).length < 2 ^ (prefixWord ++ tailWord_4745199).sum := by decide
  have hdescent : baseEnd_4745199 < baseStart_4745199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745209 : List Nat := [1, 2, 1, 3, 1, 4, 3, 2, 1, 5]
def baseStart_4745209 : Nat := 118140960795 + 4745209 * 2 ^ 59
def prefixEnd_4745209 : Nat := 4983230072969 + 3 ^ 40 * 4745209 * 2
def baseEnd_4745209 : Nat := 812191007680276693888229

theorem tailTrace_4745209 : CollatzResearch.WordTrace tailWord_4745209 prefixEnd_4745209 812191007680276693888229 := by
  unfold tailWord_4745209
  simp only [CollatzResearch.WordTrace]
  refine ⟨173071990665925685021702681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115381327110617123347801787 173071990665925685021702681)
  ·
    refine ⟨129803992999444263766277011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173071990665925685021702681 129803992999444263766277011)
    ·
      refine ⟨194705989499166395649415517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129803992999444263766277011 194705989499166395649415517)
      ·
        refine ⟨73014746062187398368530819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194705989499166395649415517 73014746062187398368530819)
        ·
          refine ⟨109522119093281097552796229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73014746062187398368530819 109522119093281097552796229)
          ·
            refine ⟨20535397329990205791149293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109522119093281097552796229 20535397329990205791149293)
            ·
              refine ⟨7700773998746327171680985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20535397329990205791149293 7700773998746327171680985)
              ·
                refine ⟨5775580499059745378760739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7700773998746327171680985 5775580499059745378760739)
                ·
                  refine ⟨8663370748589618068141109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5775580499059745378760739 8663370748589618068141109)
                  ·
                    refine ⟨812191007680276693888229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8663370748589618068141109 812191007680276693888229)
                    ·
                      rfl

theorem cell23_4745209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 5].length) (baseStart_4745209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745209 prefixEnd_4745209 := by exact prefixLift 4745209
  have htrace : WordTrace (prefixWord ++ tailWord_4745209) baseStart_4745209 baseEnd_4745209 := by
    simpa [prefixWord, tailWord_4745209, baseEnd_4745209] using wordTrace_append hprefix tailTrace_4745209
  have hstable : (prefixWord ++ tailWord_4745209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745209).length < 2 ^ (prefixWord ++ tailWord_4745209).sum := by decide
  have hdescent : baseEnd_4745209 < baseStart_4745209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745279 : List Nat := [1, 1, 2, 2, 3, 1, 4, 2, 1, 3, 3]
def baseStart_4745279 : Nat := 118140960795 + 4745279 * 2 ^ 59
def prefixEnd_4745279 : Nat := 4983230072969 + 3 ^ 40 * 4745279 * 2
def baseEnd_4745279 : Nat := 2436608966686644807789365

theorem tailTrace_4745279 : CollatzResearch.WordTrace tailWord_4745279 prefixEnd_4745279 2436608966686644807789365 := by
  unfold tailWord_4745279
  simp only [CollatzResearch.WordTrace]
  refine ⟨173074543775672086976750891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115383029183781391317833927 173074543775672086976750891)
  ·
    refine ⟨259611815663508130465126337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173074543775672086976750891 259611815663508130465126337)
    ·
      refine ⟨194708861747631097848844753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259611815663508130465126337 194708861747631097848844753)
      ·
        refine ⟨146031646310723323386633565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194708861747631097848844753 146031646310723323386633565)
        ·
          refine ⟨54761867366521246269987587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146031646310723323386633565 54761867366521246269987587)
          ·
            refine ⟨82142801049781869404981381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54761867366521246269987587 82142801049781869404981381)
            ·
              refine ⟨15401775196834100513434009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82142801049781869404981381 15401775196834100513434009)
              ·
                refine ⟨11551331397625575385075507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15401775196834100513434009 11551331397625575385075507)
                ·
                  refine ⟨17326997096438363077613261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11551331397625575385075507 17326997096438363077613261)
                  ·
                    refine ⟨6497623911164386154104973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17326997096438363077613261 6497623911164386154104973)
                    ·
                      refine ⟨2436608966686644807789365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6497623911164386154104973 2436608966686644807789365)
                      ·
                        rfl

theorem cell23_4745279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3, 3].length) (baseStart_4745279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745279 prefixEnd_4745279 := by exact prefixLift 4745279
  have htrace : WordTrace (prefixWord ++ tailWord_4745279) baseStart_4745279 baseEnd_4745279 := by
    simpa [prefixWord, tailWord_4745279, baseEnd_4745279] using wordTrace_append hprefix tailTrace_4745279
  have hstable : (prefixWord ++ tailWord_4745279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745279).length < 2 ^ (prefixWord ++ tailWord_4745279).sum := by decide
  have hdescent : baseEnd_4745279 < baseStart_4745279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745280 : List Nat := [2, 1, 1, 2, 2, 5, 2, 3, 1, 2, 2]
def baseStart_4745280 : Nat := 118140960795 + 4745280 * 2 ^ 59
def prefixEnd_4745280 : Nat := 4983230072969 + 3 ^ 40 * 4745280 * 2
def baseEnd_4745280 : Nat := 2436609480167299303876861

theorem tailTrace_4745280 : CollatzResearch.WordTrace tailWord_4745280 prefixEnd_4745280 2436609480167299303876861 := by
  unfold tailWord_4745280
  simp only [CollatzResearch.WordTrace]
  refine ⟨86537290124334232073768647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115383053499112309431691529 86537290124334232073768647)
  ·
    refine ⟨129805935186501348110652971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86537290124334232073768647 129805935186501348110652971)
    ·
      refine ⟨194708902779752022165979457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129805935186501348110652971 194708902779752022165979457)
      ·
        refine ⟨146031677084814016624484593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194708902779752022165979457 146031677084814016624484593)
        ·
          refine ⟨109523757813610512468363445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146031677084814016624484593 109523757813610512468363445)
          ·
            refine ⟨10267852295025985543909073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 109523757813610512468363445 10267852295025985543909073)
            ·
              refine ⟨7700889221269489157931805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10267852295025985543909073 7700889221269489157931805)
              ·
                refine ⟨2887833457976058434224427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7700889221269489157931805 2887833457976058434224427)
                ·
                  refine ⟨4331750186964087651336641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2887833457976058434224427 4331750186964087651336641)
                  ·
                    refine ⟨3248812640223065738502481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4331750186964087651336641 3248812640223065738502481)
                    ·
                      refine ⟨2436609480167299303876861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3248812640223065738502481 2436609480167299303876861)
                      ·
                        rfl

theorem cell23_4745280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3, 1, 2, 2].length) (baseStart_4745280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745280 prefixEnd_4745280 := by exact prefixLift 4745280
  have htrace : WordTrace (prefixWord ++ tailWord_4745280) baseStart_4745280 baseEnd_4745280 := by
    simpa [prefixWord, tailWord_4745280, baseEnd_4745280] using wordTrace_append hprefix tailTrace_4745280
  have hstable : (prefixWord ++ tailWord_4745280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745280).length < 2 ^ (prefixWord ++ tailWord_4745280).sum := by decide
  have hdescent : baseEnd_4745280 < baseStart_4745280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745353 : List Nat := [1, 2, 1, 1, 4, 2, 2, 4, 2, 2, 2]
def baseStart_4745353 : Nat := 118140960795 + 4745353 * 2 ^ 59
def prefixEnd_4745353 : Nat := 4983230072969 + 3 ^ 40 * 4745353 * 2
def baseEnd_4745353 : Nat := 2436646964255077518264025

theorem tailTrace_4745353 : CollatzResearch.WordTrace tailWord_4745353 prefixEnd_4745353 2436646964255077518264025 := by
  unfold tailWord_4745353
  simp only [CollatzResearch.WordTrace]
  refine ⟨173077242777403997614944713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115384828518269331743296475 173077242777403997614944713)
  ·
    refine ⟨129807932083052998211208535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173077242777403997614944713 129807932083052998211208535)
    ·
      refine ⟨194711898124579497316812803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129807932083052998211208535 194711898124579497316812803)
      ·
        refine ⟨292067847186869245975219205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194711898124579497316812803 292067847186869245975219205)
        ·
          refine ⟨54762721347537983620353601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 292067847186869245975219205 54762721347537983620353601)
          ·
            refine ⟨41072041010653487715265201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54762721347537983620353601 41072041010653487715265201)
            ·
              refine ⟨30804030757990115786448901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41072041010653487715265201 30804030757990115786448901)
              ·
                refine ⟨5775755767123146709959169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30804030757990115786448901 5775755767123146709959169)
                ·
                  refine ⟨4331816825342360032469377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5775755767123146709959169 4331816825342360032469377)
                  ·
                    refine ⟨3248862619006770024352033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4331816825342360032469377 3248862619006770024352033)
                    ·
                      refine ⟨2436646964255077518264025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3248862619006770024352033 2436646964255077518264025)
                      ·
                        rfl

theorem cell23_4745353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2, 2, 2].length) (baseStart_4745353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745353 prefixEnd_4745353 := by exact prefixLift 4745353
  have htrace : WordTrace (prefixWord ++ tailWord_4745353) baseStart_4745353 baseEnd_4745353 := by
    simpa [prefixWord, tailWord_4745353, baseEnd_4745353] using wordTrace_append hprefix tailTrace_4745353
  have hstable : (prefixWord ++ tailWord_4745353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745353).length < 2 ^ (prefixWord ++ tailWord_4745353).sum := by decide
  have hdescent : baseEnd_4745353 < baseStart_4745353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745364 : List Nat := [2, 4, 2, 3, 1, 2, 2, 1, 2, 1, 3]
def baseStart_4745364 : Nat := 118140960795 + 4745364 * 2 ^ 59
def prefixEnd_4745364 : Nat := 4983230072969 + 3 ^ 40 * 4745364 * 2
def baseEnd_4745364 : Nat := 2436652612542276975226475

theorem tailTrace_4745364 : CollatzResearch.WordTrace tailWord_4745364 prefixEnd_4745364 2436652612542276975226475 := by
  unfold tailWord_4745364
  simp only [CollatzResearch.WordTrace]
  refine ⟨86538821990182073246797573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115385095986909430995730097 86538821990182073246797573)
  ·
    refine ⟨16226029123159138733774545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86538821990182073246797573 16226029123159138733774545)
    ·
      refine ⟨12169521842369354050330909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16226029123159138733774545 12169521842369354050330909)
      ·
        refine ⟨4563570690888507768874091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12169521842369354050330909 4563570690888507768874091)
        ·
          refine ⟨6845356036332761653311137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4563570690888507768874091 6845356036332761653311137)
          ·
            refine ⟨5134017027249571239983353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6845356036332761653311137 5134017027249571239983353)
            ·
              refine ⟨3850512770437178429987515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5134017027249571239983353 3850512770437178429987515)
              ·
                refine ⟨5775769155655767644981273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3850512770437178429987515 5775769155655767644981273)
                ·
                  refine ⟨4331826866741825733735955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5775769155655767644981273 4331826866741825733735955)
                  ·
                    refine ⟨6497740300112738600603933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4331826866741825733735955 6497740300112738600603933)
                    ·
                      refine ⟨2436652612542276975226475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6497740300112738600603933 2436652612542276975226475)
                      ·
                        rfl

theorem cell23_4745364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_4745364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745364 prefixEnd_4745364 := by exact prefixLift 4745364
  have htrace : WordTrace (prefixWord ++ tailWord_4745364) baseStart_4745364 baseEnd_4745364 := by
    simpa [prefixWord, tailWord_4745364, baseEnd_4745364] using wordTrace_append hprefix tailTrace_4745364
  have hstable : (prefixWord ++ tailWord_4745364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745364).length < 2 ^ (prefixWord ++ tailWord_4745364).sum := by decide
  have hdescent : baseEnd_4745364 < baseStart_4745364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745369 : List Nat := [1, 2, 1, 2, 1, 2, 1, 5, 2, 3, 3]
def baseStart_4745369 : Nat := 118140960795 + 4745369 * 2 ^ 59
def prefixEnd_4745369 : Nat := 4983230072969 + 3 ^ 40 * 4745369 * 2
def baseEnd_4745369 : Nat := 2436655179945549455663951

theorem tailTrace_4745369 : CollatzResearch.WordTrace tailWord_4745369 prefixEnd_4745369 2436655179945549455663951 := by
  unfold tailWord_4745369
  simp only [CollatzResearch.WordTrace]
  refine ⟨173077826345346032347527161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115385217563564021565018107 173077826345346032347527161)
  ·
    refine ⟨129808369759009524260645371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173077826345346032347527161 129808369759009524260645371)
    ·
      refine ⟨194712554638514286390968057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129808369759009524260645371 194712554638514286390968057)
      ·
        refine ⟨146034415978885714793226043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194712554638514286390968057 146034415978885714793226043)
        ·
          refine ⟨219051623968328572189839065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146034415978885714793226043 219051623968328572189839065)
          ·
            refine ⟨164288717976246429142379299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219051623968328572189839065 164288717976246429142379299)
            ·
              refine ⟨246433076964369643713568949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164288717976246429142379299 246433076964369643713568949)
              ·
                refine ⟨23103100965409654098147089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 246433076964369643713568949 23103100965409654098147089)
                ·
                  refine ⟨17327325724057240573610317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23103100965409654098147089 17327325724057240573610317)
                  ·
                    refine ⟨6497747146521465215103869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17327325724057240573610317 6497747146521465215103869)
                    ·
                      refine ⟨2436655179945549455663951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6497747146521465215103869 2436655179945549455663951)
                      ·
                        rfl

theorem cell23_4745369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 3, 3].length) (baseStart_4745369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745369 prefixEnd_4745369 := by exact prefixLift 4745369
  have htrace : WordTrace (prefixWord ++ tailWord_4745369) baseStart_4745369 baseEnd_4745369 := by
    simpa [prefixWord, tailWord_4745369, baseEnd_4745369] using wordTrace_append hprefix tailTrace_4745369
  have hstable : (prefixWord ++ tailWord_4745369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745369).length < 2 ^ (prefixWord ++ tailWord_4745369).sum := by decide
  have hdescent : baseEnd_4745369 < baseStart_4745369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745374 : List Nat := [4, 3, 1, 1, 4, 1, 1, 2, 1, 3, 2]
def baseStart_4745374 : Nat := 118140960795 + 4745374 * 2 ^ 59
def prefixEnd_4745374 : Nat := 4983230072969 + 3 ^ 40 * 4745374 * 2
def baseEnd_4745374 : Nat := 2436657747348821936101429

theorem tailTrace_4745374 : CollatzResearch.WordTrace tailWord_4745374 prefixEnd_4745374 2436657747348821936101429 := by
  unfold tailWord_4745374
  simp only [CollatzResearch.WordTrace]
  refine ⟨21634751088790989775182397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115385339140218612134306117 21634751088790989775182397)
  ·
    refine ⟨8113031658296621165693399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21634751088790989775182397 8113031658296621165693399)
    ·
      refine ⟨12169547487444931748540099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8113031658296621165693399 12169547487444931748540099)
      ·
        refine ⟨18254321231167397622810149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12169547487444931748540099 18254321231167397622810149)
        ·
          refine ⟨3422685230843887054276903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18254321231167397622810149 3422685230843887054276903)
          ·
            refine ⟨5134027846265830581415355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3422685230843887054276903 5134027846265830581415355)
            ·
              refine ⟨7701041769398745872123033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5134027846265830581415355 7701041769398745872123033)
              ·
                refine ⟨5775781327049059404092275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7701041769398745872123033 5775781327049059404092275)
                ·
                  refine ⟨8663671990573589106138413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5775781327049059404092275 8663671990573589106138413)
                  ·
                    refine ⟨3248876996465095914801905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8663671990573589106138413 3248876996465095914801905)
                    ·
                      refine ⟨2436657747348821936101429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3248876996465095914801905 2436657747348821936101429)
                      ·
                        rfl

theorem cell23_4745374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_4745374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745374 prefixEnd_4745374 := by exact prefixLift 4745374
  have htrace : WordTrace (prefixWord ++ tailWord_4745374) baseStart_4745374 baseEnd_4745374 := by
    simpa [prefixWord, tailWord_4745374, baseEnd_4745374] using wordTrace_append hprefix tailTrace_4745374
  have hstable : (prefixWord ++ tailWord_4745374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745374).length < 2 ^ (prefixWord ++ tailWord_4745374).sum := by decide
  have hdescent : baseEnd_4745374 < baseStart_4745374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745399 : List Nat := [1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 5]
def baseStart_4745399 : Nat := 118140960795 + 4745399 * 2 ^ 59
def prefixEnd_4745399 : Nat := 4983230072969 + 3 ^ 40 * 4745399 * 2
def baseEnd_4745399 : Nat := 2436670584365184338288813

theorem tailTrace_4745399 : CollatzResearch.WordTrace tailWord_4745399 prefixEnd_4745399 2436670584365184338288813 := by
  unfold tailWord_4745399
  simp only [CollatzResearch.WordTrace]
  refine ⟨173078920535237347471119251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115385947023491564980746167 173078920535237347471119251)
  ·
    refine ⟨259618380802856021206678877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173078920535237347471119251 259618380802856021206678877)
    ·
      refine ⟨97356892801071007952504579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 259618380802856021206678877 97356892801071007952504579)
      ·
        refine ⟨146035339201606511928756869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97356892801071007952504579 146035339201606511928756869)
        ·
          refine ⟨27381626100301220986641913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146035339201606511928756869 27381626100301220986641913)
          ·
            refine ⟨20536219575225915739981435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27381626100301220986641913 20536219575225915739981435)
            ·
              refine ⟨30804329362838873609972153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20536219575225915739981435 30804329362838873609972153)
              ·
                refine ⟨23103247022129155207479115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30804329362838873609972153 23103247022129155207479115)
                ·
                  refine ⟨34654870533193732811218673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23103247022129155207479115 34654870533193732811218673)
                  ·
                    refine ⟨25991152899895299608414005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34654870533193732811218673 25991152899895299608414005)
                    ·
                      refine ⟨2436670584365184338288813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25991152899895299608414005 2436670584365184338288813)
                      ·
                        rfl

theorem cell23_4745399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_4745399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745399 prefixEnd_4745399 := by exact prefixLift 4745399
  have htrace : WordTrace (prefixWord ++ tailWord_4745399) baseStart_4745399 baseEnd_4745399 := by
    simpa [prefixWord, tailWord_4745399, baseEnd_4745399] using wordTrace_append hprefix tailTrace_4745399
  have hstable : (prefixWord ++ tailWord_4745399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745399).length < 2 ^ (prefixWord ++ tailWord_4745399).sum := by decide
  have hdescent : baseEnd_4745399 < baseStart_4745399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745443 : List Nat := [1, 1, 1, 8, 1, 1, 1, 1, 1, 3, 4]
def baseStart_4745443 : Nat := 118140960795 + 4745443 * 2 ^ 59
def prefixEnd_4745443 : Nat := 4983230072969 + 3 ^ 40 * 4745443 * 2
def baseEnd_4745443 : Nat := 2436693177513982166138611

theorem tailTrace_4745443 : CollatzResearch.WordTrace tailWord_4745443 prefixEnd_4745443 2436693177513982166138611 := by
  unfold tailWord_4745443
  simp only [CollatzResearch.WordTrace]
  refine ⟨173080525347077942985720983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115387016898051961990480655 173080525347077942985720983)
  ·
    refine ⟨259620788020616914478581475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173080525347077942985720983 259620788020616914478581475)
    ·
      refine ⟨389431182030925371717872213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259620788020616914478581475 389431182030925371717872213)
      ·
        refine ⟨4563646664424906699818815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 389431182030925371717872213 4563646664424906699818815)
        ·
          refine ⟨6845469996637360049728223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4563646664424906699818815 6845469996637360049728223)
          ·
            refine ⟨10268204994956040074592335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6845469996637360049728223 10268204994956040074592335)
            ·
              refine ⟨15402307492434060111888503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10268204994956040074592335 15402307492434060111888503)
              ·
                refine ⟨23103461238651090167832755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15402307492434060111888503 23103461238651090167832755)
                ·
                  refine ⟨34655191857976635251749133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23103461238651090167832755 34655191857976635251749133)
                  ·
                    refine ⟨12995696946741238219405925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34655191857976635251749133 12995696946741238219405925)
                    ·
                      refine ⟨2436693177513982166138611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12995696946741238219405925 2436693177513982166138611)
                      ·
                        rfl

theorem cell23_4745443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_4745443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745443 prefixEnd_4745443 := by exact prefixLift 4745443
  have htrace : WordTrace (prefixWord ++ tailWord_4745443) baseStart_4745443 baseEnd_4745443 := by
    simpa [prefixWord, tailWord_4745443, baseEnd_4745443] using wordTrace_append hprefix tailTrace_4745443
  have hstable : (prefixWord ++ tailWord_4745443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745443).length < 2 ^ (prefixWord ++ tailWord_4745443).sum := by decide
  have hdescent : baseEnd_4745443 < baseStart_4745443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745466 : List Nat := [3, 1, 1, 1, 1, 5, 3, 2, 6]
def baseStart_4745466 : Nat := 118140960795 + 4745466 * 2 ^ 59
def prefixEnd_4745466 : Nat := 4983230072969 + 3 ^ 40 * 4745466 * 2
def baseEnd_4745466 : Nat := 270744998618781730683445

theorem tailTrace_4745466 : CollatzResearch.WordTrace tailWord_4745466 prefixEnd_4745466 270744998618781730683445 := by
  unfold tailWord_4745466
  simp only [CollatzResearch.WordTrace]
  refine ⟨43270341056498654478452063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115387576150663078609205501 43270341056498654478452063)
  ·
    refine ⟨64905511584747981717678095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43270341056498654478452063 64905511584747981717678095)
    ·
      refine ⟨97358267377121972576517143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64905511584747981717678095 97358267377121972576517143)
      ·
        refine ⟨146037401065682958864775715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97358267377121972576517143 146037401065682958864775715)
        ·
          refine ⟨219056101598524438297163573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146037401065682958864775715 219056101598524438297163573)
          ·
            refine ⟨20536509524861666090359085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 219056101598524438297163573 20536509524861666090359085)
            ·
              refine ⟨7701191071823124783884657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20536509524861666090359085 7701191071823124783884657)
              ·
                refine ⟨5775893303867343587913493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7701191071823124783884657 5775893303867343587913493)
                ·
                  refine ⟨270744998618781730683445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5775893303867343587913493 270744998618781730683445)
                  ·
                    rfl

theorem cell23_4745466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 6].length) (baseStart_4745466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745466 prefixEnd_4745466 := by exact prefixLift 4745466
  have htrace : WordTrace (prefixWord ++ tailWord_4745466) baseStart_4745466 baseEnd_4745466 := by
    simpa [prefixWord, tailWord_4745466, baseEnd_4745466] using wordTrace_append hprefix tailTrace_4745466
  have hstable : (prefixWord ++ tailWord_4745466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745466).length < 2 ^ (prefixWord ++ tailWord_4745466).sum := by decide
  have hdescent : baseEnd_4745466 < baseStart_4745466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745470 : List Nat := [4, 2, 2, 1, 1, 1, 1, 6, 1, 4]
def baseStart_4745470 : Nat := 118140960795 + 4745470 * 2 ^ 59
def prefixEnd_4745470 : Nat := 4983230072969 + 3 ^ 40 * 4745470 * 2
def baseEnd_4745470 : Nat := 812235680497217853500329

theorem tailTrace_4745470 : CollatzResearch.WordTrace tailWord_4745470 prefixEnd_4745470 812235680497217853500329 := by
  unfold tailWord_4745470
  simp only [CollatzResearch.WordTrace]
  refine ⟨21635188764747515824619233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115387673411986751064635909 21635188764747515824619233)
  ·
    refine ⟨16226391573560636868464425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21635188764747515824619233 16226391573560636868464425)
    ·
      refine ⟨12169793680170477651348319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16226391573560636868464425 12169793680170477651348319)
      ·
        refine ⟨18254690520255716477022479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12169793680170477651348319 18254690520255716477022479)
        ·
          refine ⟨27382035780383574715533719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18254690520255716477022479 27382035780383574715533719)
          ·
            refine ⟨41073053670575362073300579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27382035780383574715533719 41073053670575362073300579)
            ·
              refine ⟨61609580505863043109950869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41073053670575362073300579 61609580505863043109950869)
              ·
                refine ⟨2887949086212330145778947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61609580505863043109950869 2887949086212330145778947)
                ·
                  refine ⟨4331923629318495218668421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2887949086212330145778947 4331923629318495218668421)
                  ·
                    refine ⟨812235680497217853500329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4331923629318495218668421 812235680497217853500329)
                    ·
                      rfl

theorem cell23_4745470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_4745470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745470 prefixEnd_4745470 := by exact prefixLift 4745470
  have htrace : WordTrace (prefixWord ++ tailWord_4745470) baseStart_4745470 baseEnd_4745470 := by
    simpa [prefixWord, tailWord_4745470, baseEnd_4745470] using wordTrace_append hprefix tailTrace_4745470
  have hstable : (prefixWord ++ tailWord_4745470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745470).length < 2 ^ (prefixWord ++ tailWord_4745470).sum := by decide
  have hdescent : baseEnd_4745470 < baseStart_4745470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745493 : List Nat := [1, 3, 2, 1, 2, 1, 4, 2, 3, 1, 3]
def baseStart_4745493 : Nat := 118140960795 + 4745493 * 2 ^ 59
def prefixEnd_4745493 : Nat := 4983230072969 + 3 ^ 40 * 4745493 * 2
def baseEnd_4745493 : Nat := 2436718851546706970513381

theorem tailTrace_4745493 : CollatzResearch.WordTrace tailWord_4745493 prefixEnd_4745493 2436718851546706970513381 := by
  unfold tailWord_4745493
  simp only [CollatzResearch.WordTrace]
  refine ⟨173082348996896801525041133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115388232664597867683360755 173082348996896801525041133)
  ·
    refine ⟨64905880873836300571890425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173082348996896801525041133 64905880873836300571890425)
    ·
      refine ⟨48679410655377225428917819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64905880873836300571890425 48679410655377225428917819)
      ·
        refine ⟨73019115983065838143376729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48679410655377225428917819 73019115983065838143376729)
        ·
          refine ⟨54764336987299378607532547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73019115983065838143376729 54764336987299378607532547)
          ·
            refine ⟨82146505480949067911298821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54764336987299378607532547 82146505480949067911298821)
            ·
              refine ⟨15402469777677950233368529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82146505480949067911298821 15402469777677950233368529)
              ·
                refine ⟨11551852333258462675026397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15402469777677950233368529 11551852333258462675026397)
                ·
                  refine ⟨4331944624971923503134899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11551852333258462675026397 4331944624971923503134899)
                  ·
                    refine ⟨6497916937457885254702349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4331944624971923503134899 6497916937457885254702349)
                    ·
                      refine ⟨2436718851546706970513381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6497916937457885254702349 2436718851546706970513381)
                      ·
                        rfl

theorem cell23_4745493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_4745493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745493 prefixEnd_4745493 := by exact prefixLift 4745493
  have htrace : WordTrace (prefixWord ++ tailWord_4745493) baseStart_4745493 baseEnd_4745493 := by
    simpa [prefixWord, tailWord_4745493, baseEnd_4745493] using wordTrace_append hprefix tailTrace_4745493
  have hstable : (prefixWord ++ tailWord_4745493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745493).length < 2 ^ (prefixWord ++ tailWord_4745493).sum := by decide
  have hdescent : baseEnd_4745493 < baseStart_4745493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745503 : List Nat := [1, 1, 2, 4, 3, 1, 2, 1, 1, 5, 2]
def baseStart_4745503 : Nat := 118140960795 + 4745503 * 2 ^ 59
def prefixEnd_4745503 : Nat := 4983230072969 + 3 ^ 40 * 4745503 * 2
def baseEnd_4745503 : Nat := 2436723986353251931388335

theorem tailTrace_4745503 : CollatzResearch.WordTrace tailWord_4745503 prefixEnd_4745503 2436723986353251931388335 := by
  unfold tailWord_4745503
  simp only [CollatzResearch.WordTrace]
  refine ⟨173082713726860573232905163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115388475817907048821936775 173082713726860573232905163)
  ·
    refine ⟨259624070590290859849357745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173082713726860573232905163 259624070590290859849357745)
    ·
      refine ⟨194718052942718144887018309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259624070590290859849357745 194718052942718144887018309)
      ·
        refine ⟨36509634926759652166315933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 194718052942718144887018309 36509634926759652166315933)
        ·
          refine ⟨13691113097534869562368475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36509634926759652166315933 13691113097534869562368475)
          ·
            refine ⟨20536669646302304343552713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13691113097534869562368475 20536669646302304343552713)
            ·
              refine ⟨15402502234726728257664535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20536669646302304343552713 15402502234726728257664535)
              ·
                refine ⟨23103753352090092386496803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15402502234726728257664535 23103753352090092386496803)
                ·
                  refine ⟨34655630028135138579745205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23103753352090092386496803 34655630028135138579745205)
                  ·
                    refine ⟨3248965315137669241851113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34655630028135138579745205 3248965315137669241851113)
                    ·
                      refine ⟨2436723986353251931388335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3248965315137669241851113 2436723986353251931388335)
                      ·
                        rfl

theorem cell23_4745503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_4745503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745503 prefixEnd_4745503 := by exact prefixLift 4745503
  have htrace : WordTrace (prefixWord ++ tailWord_4745503) baseStart_4745503 baseEnd_4745503 := by
    simpa [prefixWord, tailWord_4745503, baseEnd_4745503] using wordTrace_append hprefix tailTrace_4745503
  have hstable : (prefixWord ++ tailWord_4745503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745503).length < 2 ^ (prefixWord ++ tailWord_4745503).sum := by decide
  have hdescent : baseEnd_4745503 < baseStart_4745503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745539 : List Nat := [1, 1, 1, 3, 1, 3, 3, 10]
def baseStart_4745539 : Nat := 118140960795 + 4745539 * 2 ^ 59
def prefixEnd_4745539 : Nat := 4983230072969 + 3 ^ 40 * 4745539 * 2
def baseEnd_4745539 : Nat := 90249721172474584834747

theorem tailTrace_4745539 : CollatzResearch.WordTrace tailWord_4745539 prefixEnd_4745539 90249721172474584834747 := by
  unfold tailWord_4745539
  simp only [CollatzResearch.WordTrace]
  refine ⟨173084026754730151381215671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115389351169820100920810447 173084026754730151381215671)
  ·
    refine ⟨259626040132095227071823507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173084026754730151381215671 259626040132095227071823507)
    ·
      refine ⟨389439060198142840607735261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259626040132095227071823507 389439060198142840607735261)
      ·
        refine ⟨146039647574303565227900723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 389439060198142840607735261 146039647574303565227900723)
        ·
          refine ⟨219059471361455347841851085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146039647574303565227900723 219059471361455347841851085)
          ·
            refine ⟨82147301760545755440694157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 219059471361455347841851085 82147301760545755440694157)
            ·
              refine ⟨30805238160204658290260309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82147301760545755440694157 30805238160204658290260309)
              ·
                refine ⟨90249721172474584834747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30805238160204658290260309 90249721172474584834747)
                ·
                  rfl

theorem cell23_4745539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 10].length) (baseStart_4745539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745539 prefixEnd_4745539 := by exact prefixLift 4745539
  have htrace : WordTrace (prefixWord ++ tailWord_4745539) baseStart_4745539 baseEnd_4745539 := by
    simpa [prefixWord, tailWord_4745539, baseEnd_4745539] using wordTrace_append hprefix tailTrace_4745539
  have hstable : (prefixWord ++ tailWord_4745539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745539).length < 2 ^ (prefixWord ++ tailWord_4745539).sum := by decide
  have hdescent : baseEnd_4745539 < baseStart_4745539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745543 : List Nat := [1, 1, 4, 1, 2, 2, 3, 3, 2, 4]
def baseStart_4745543 : Nat := 118140960795 + 4745543 * 2 ^ 59
def prefixEnd_4745543 : Nat := 4983230072969 + 3 ^ 40 * 4745543 * 2
def baseEnd_4745543 : Nat := 812248175193143924962717

theorem tailTrace_4745543 : CollatzResearch.WordTrace tailWord_4745543 prefixEnd_4745543 812248175193143924962717 := by
  unfold tailWord_4745543
  simp only [CollatzResearch.WordTrace]
  refine ⟨173084172646715660064361283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115389448431143773376240855 173084172646715660064361283)
  ·
    refine ⟨259626258970073490096541925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173084172646715660064361283 259626258970073490096541925)
    ·
      refine ⟨48679923556888779393101611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 259626258970073490096541925 48679923556888779393101611)
      ·
        refine ⟨73019885335333169089652417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48679923556888779393101611 73019885335333169089652417)
        ·
          refine ⟨54764914001499876817239313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73019885335333169089652417 54764914001499876817239313)
          ·
            refine ⟨41073685501124907612929485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54764914001499876817239313 41073685501124907612929485)
            ·
              refine ⟨15402632062921840354848557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41073685501124907612929485 15402632062921840354848557)
              ·
                refine ⟨5775987023595690133068209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15402632062921840354848557 5775987023595690133068209)
                ·
                  refine ⟨4331990267696767599801157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5775987023595690133068209 4331990267696767599801157)
                  ·
                    refine ⟨812248175193143924962717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4331990267696767599801157 812248175193143924962717)
                    ·
                      rfl

theorem cell23_4745543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_4745543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745543 prefixEnd_4745543 := by exact prefixLift 4745543
  have htrace : WordTrace (prefixWord ++ tailWord_4745543) baseStart_4745543 baseEnd_4745543 := by
    simpa [prefixWord, tailWord_4745543, baseEnd_4745543] using wordTrace_append hprefix tailTrace_4745543
  have hstable : (prefixWord ++ tailWord_4745543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745543).length < 2 ^ (prefixWord ++ tailWord_4745543).sum := by decide
  have hdescent : baseEnd_4745543 < baseStart_4745543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745553 : List Nat := [1, 2, 2, 1, 4, 3, 1, 1, 3, 2, 3]
def baseStart_4745553 : Nat := 118140960795 + 4745553 * 2 ^ 59
def prefixEnd_4745553 : Nat := 4983230072969 + 3 ^ 40 * 4745553 * 2
def baseEnd_4745553 : Nat := 2436749660385976735763105

theorem tailTrace_4745553 : CollatzResearch.WordTrace tailWord_4745553 prefixEnd_4745553 2436749660385976735763105 := by
  unfold tailWord_4745553
  simp only [CollatzResearch.WordTrace]
  refine ⟨173084537376679431772225313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115389691584452954514816875 173084537376679431772225313)
  ·
    refine ⟨129813403032509573829168985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173084537376679431772225313 129813403032509573829168985)
    ·
      refine ⟨97360052274382180371876739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129813403032509573829168985 97360052274382180371876739)
      ·
        refine ⟨146040078411573270557815109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97360052274382180371876739 146040078411573270557815109)
        ·
          refine ⟨27382514702169988229590333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146040078411573270557815109 27382514702169988229590333)
          ·
            refine ⟨10268443013313745586096375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27382514702169988229590333 10268443013313745586096375)
            ·
              refine ⟨15402664519970618379144563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10268443013313745586096375 15402664519970618379144563)
              ·
                refine ⟨23103996779955927568716845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15402664519970618379144563 23103996779955927568716845)
                ·
                  refine ⟨8663998792483472838268817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23103996779955927568716845 8663998792483472838268817)
                  ·
                    refine ⟨6497999094362604628701613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8663998792483472838268817 6497999094362604628701613)
                    ·
                      refine ⟨2436749660385976735763105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6497999094362604628701613 2436749660385976735763105)
                      ·
                        rfl

theorem cell23_4745553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 2, 3].length) (baseStart_4745553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745553 prefixEnd_4745553 := by exact prefixLift 4745553
  have htrace : WordTrace (prefixWord ++ tailWord_4745553) baseStart_4745553 baseEnd_4745553 := by
    simpa [prefixWord, tailWord_4745553, baseEnd_4745553] using wordTrace_append hprefix tailTrace_4745553
  have hstable : (prefixWord ++ tailWord_4745553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745553).length < 2 ^ (prefixWord ++ tailWord_4745553).sum := by decide
  have hdescent : baseEnd_4745553 < baseStart_4745553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745556 : List Nat := [2, 4, 1, 1, 2, 2, 2, 9]
def baseStart_4745556 : Nat := 118140960795 + 4745556 * 2 ^ 59
def prefixEnd_4745556 : Nat := 4983230072969 + 3 ^ 40 * 4745556 * 2
def baseEnd_4745556 : Nat := 90250044475108897186133

theorem tailTrace_4745556 : CollatzResearch.WordTrace tailWord_4745556 prefixEnd_4745556 90250044475108897186133 := by
  unfold tailWord_4745556
  simp only [CollatzResearch.WordTrace]
  refine ⟨86542323397834281642292261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115389764530445708856389681 86542323397834281642292261)
  ·
    refine ⟨16226685637093927807929799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86542323397834281642292261 16226685637093927807929799)
    ·
      refine ⟨24340028455640891711894699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16226685637093927807929799 24340028455640891711894699)
      ·
        refine ⟨36510042683461337567842049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24340028455640891711894699 36510042683461337567842049)
        ·
          refine ⟨27382532012596003175881537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36510042683461337567842049 27382532012596003175881537)
          ·
            refine ⟨20536899009447002381911153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27382532012596003175881537 20536899009447002381911153)
            ·
              refine ⟨15402674257085251786433365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20536899009447002381911153 15402674257085251786433365)
              ·
                refine ⟨90250044475108897186133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15402674257085251786433365 90250044475108897186133)
                ·
                  rfl

theorem cell23_4745556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 9].length) (baseStart_4745556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745556 prefixEnd_4745556 := by exact prefixLift 4745556
  have htrace : WordTrace (prefixWord ++ tailWord_4745556) baseStart_4745556 baseEnd_4745556 := by
    simpa [prefixWord, tailWord_4745556, baseEnd_4745556] using wordTrace_append hprefix tailTrace_4745556
  have hstable : (prefixWord ++ tailWord_4745556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745556).length < 2 ^ (prefixWord ++ tailWord_4745556).sum := by decide
  have hdescent : baseEnd_4745556 < baseStart_4745556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745570 : List Nat := [3, 3, 2, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_4745570 : Nat := 118140960795 + 4745570 * 2 ^ 59
def prefixEnd_4745570 : Nat := 4983230072969 + 3 ^ 40 * 4745570 * 2
def baseEnd_4745570 : Nat := 2436758389557103169250527

theorem tailTrace_4745570 : CollatzResearch.WordTrace tailWord_4745570 prefixEnd_4745570 2436758389557103169250527 := by
  unfold tailWord_4745570
  simp only [CollatzResearch.WordTrace]
  refine ⟨43271289354404460918898541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115390104945078562450396109 43271289354404460918898541)
  ·
    refine ⟨16226733507901672844586953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43271289354404460918898541 16226733507901672844586953)
    ·
      refine ⟨12170050130926254633440215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16226733507901672844586953 12170050130926254633440215)
      ·
        refine ⟨18255075196389381950160323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12170050130926254633440215 18255075196389381950160323)
        ·
          refine ⟨27382612794584072925240485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18255075196389381950160323 27382612794584072925240485)
          ·
            refine ⟨5134239898984513673482591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27382612794584072925240485 5134239898984513673482591)
            ·
              refine ⟨7701359848476770510223887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5134239898984513673482591 7701359848476770510223887)
              ·
                refine ⟨11552039772715155765335831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7701359848476770510223887 11552039772715155765335831)
                ·
                  refine ⟨17328059659072733648003747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11552039772715155765335831 17328059659072733648003747)
                  ·
                    refine ⟨25992089488609100472005621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17328059659072733648003747 25992089488609100472005621)
                    ·
                      refine ⟨2436758389557103169250527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25992089488609100472005621 2436758389557103169250527)
                      ·
                        rfl

theorem cell23_4745570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_4745570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745570 prefixEnd_4745570 := by exact prefixLift 4745570
  have htrace : WordTrace (prefixWord ++ tailWord_4745570) baseStart_4745570 baseEnd_4745570 := by
    simpa [prefixWord, tailWord_4745570, baseEnd_4745570] using wordTrace_append hprefix tailTrace_4745570
  have hstable : (prefixWord ++ tailWord_4745570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745570).length < 2 ^ (prefixWord ++ tailWord_4745570).sum := by decide
  have hdescent : baseEnd_4745570 < baseStart_4745570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745584 : List Nat := [2, 1, 1, 1, 4, 3, 4, 2, 1, 2, 2]
def baseStart_4745584 : Nat := 118140960795 + 4745584 * 2 ^ 59
def prefixEnd_4745584 : Nat := 4983230072969 + 3 ^ 40 * 4745584 * 2
def baseEnd_4745584 : Nat := 2436765578286266114475463

theorem tailTrace_4745584 : CollatzResearch.WordTrace tailWord_4745584 prefixEnd_4745584 2436765578286266114475463 := by
  unfold tailWord_4745584
  simp only [CollatzResearch.WordTrace]
  refine ⟨86542834019783562033301903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115390445359711416044402537 86542834019783562033301903)
  ·
    refine ⟨129814251029675343049952855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86542834019783562033301903 129814251029675343049952855)
    ·
      refine ⟨194721376544513014574929283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129814251029675343049952855 194721376544513014574929283)
      ·
        refine ⟨292082064816769521862393925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194721376544513014574929283 292082064816769521862393925)
        ·
          refine ⟨54765387153144285349198861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 292082064816769521862393925 54765387153144285349198861)
          ·
            refine ⟨20537020182429107005949573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54765387153144285349198861 20537020182429107005949573)
            ·
              refine ⟨3850691284205457563615545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20537020182429107005949573 3850691284205457563615545)
              ·
                refine ⟨2888018463154093172711659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3850691284205457563615545 2888018463154093172711659)
                ·
                  refine ⟨4332027694731139759067489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2888018463154093172711659 4332027694731139759067489)
                  ·
                    refine ⟨3249020771048354819300617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4332027694731139759067489 3249020771048354819300617)
                    ·
                      refine ⟨2436765578286266114475463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3249020771048354819300617 2436765578286266114475463)
                      ·
                        rfl

theorem cell23_4745584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2, 1, 2, 2].length) (baseStart_4745584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745584 prefixEnd_4745584 := by exact prefixLift 4745584
  have htrace : WordTrace (prefixWord ++ tailWord_4745584) baseStart_4745584 baseEnd_4745584 := by
    simpa [prefixWord, tailWord_4745584, baseEnd_4745584] using wordTrace_append hprefix tailTrace_4745584
  have hstable : (prefixWord ++ tailWord_4745584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745584).length < 2 ^ (prefixWord ++ tailWord_4745584).sum := by decide
  have hdescent : baseEnd_4745584 < baseStart_4745584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745586 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 2, 7]
def baseStart_4745586 : Nat := 118140960795 + 4745586 * 2 ^ 59
def prefixEnd_4745586 : Nat := 4983230072969 + 3 ^ 40 * 4745586 * 2
def baseEnd_4745586 : Nat := 812255535082525035550151

theorem tailTrace_4745586 : CollatzResearch.WordTrace tailWord_4745586 prefixEnd_4745586 812255535082525035550151 := by
  unfold tailWord_4745586
  simp only [CollatzResearch.WordTrace]
  refine ⟨43271435246389969602044153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115390493990373252272117741 43271435246389969602044153)
  ·
    refine ⟨32453576434792477201533115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43271435246389969602044153 32453576434792477201533115)
    ·
      refine ⟨48680364652188715802299673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32453576434792477201533115 48680364652188715802299673)
      ·
        refine ⟨36510273489141536851724755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48680364652188715802299673 36510273489141536851724755)
        ·
          refine ⟨54765410233712305277587133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36510273489141536851724755 54765410233712305277587133)
          ·
            refine ⟨20537028837642114479095175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54765410233712305277587133 20537028837642114479095175)
            ·
              refine ⟨30805543256463171718642763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20537028837642114479095175 30805543256463171718642763)
              ·
                refine ⟨46208314884694757577964145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30805543256463171718642763 46208314884694757577964145)
                ·
                  refine ⟨34656236163521068183473109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46208314884694757577964145 34656236163521068183473109)
                  ·
                    refine ⟨812255535082525035550151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34656236163521068183473109 812255535082525035550151)
                    ·
                      rfl

theorem cell23_4745586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_4745586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745586 prefixEnd_4745586 := by exact prefixLift 4745586
  have htrace : WordTrace (prefixWord ++ tailWord_4745586) baseStart_4745586 baseEnd_4745586 := by
    simpa [prefixWord, tailWord_4745586, baseEnd_4745586] using wordTrace_append hprefix tailTrace_4745586
  have hstable : (prefixWord ++ tailWord_4745586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745586).length < 2 ^ (prefixWord ++ tailWord_4745586).sum := by decide
  have hdescent : baseEnd_4745586 < baseStart_4745586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745657 : List Nat := [1, 2, 1, 4, 3, 3, 1, 1, 1, 4, 2]
def baseStart_4745657 : Nat := 118140960795 + 4745657 * 2 ^ 59
def prefixEnd_4745657 : Nat := 4983230072969 + 3 ^ 40 * 4745657 * 2
def baseEnd_4745657 : Nat := 2436803062374044328862627

theorem tailTrace_4745657 : CollatzResearch.WordTrace tailWord_4745657 prefixEnd_4745657 2436803062374044328862627 := by
  unfold tailWord_4745657
  simp only [CollatzResearch.WordTrace]
  refine ⟨173088330568302657534011225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115392220378868438356007483 173088330568302657534011225)
  ·
    refine ⟨129816247926226993150508419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173088330568302657534011225 129816247926226993150508419)
    ·
      refine ⟨194724371889340489725762629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129816247926226993150508419 194724371889340489725762629)
      ·
        refine ⟨36510819729251341823580493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 194724371889340489725762629 36510819729251341823580493)
        ·
          refine ⟨13691557398469253183842685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36510819729251341823580493 13691557398469253183842685)
          ·
            refine ⟨5134334024425969943941007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13691557398469253183842685 5134334024425969943941007)
            ·
              refine ⟨7701501036638954915911511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5134334024425969943941007 7701501036638954915911511)
              ·
                refine ⟨11552251554958432373867267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7701501036638954915911511 11552251554958432373867267)
                ·
                  refine ⟨17328377332437648560800901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11552251554958432373867267 17328377332437648560800901)
                  ·
                    refine ⟨3249070749832059105150169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17328377332437648560800901 3249070749832059105150169)
                    ·
                      refine ⟨2436803062374044328862627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3249070749832059105150169 2436803062374044328862627)
                      ·
                        rfl

theorem cell23_4745657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_4745657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745657 prefixEnd_4745657 := by exact prefixLift 4745657
  have htrace : WordTrace (prefixWord ++ tailWord_4745657) baseStart_4745657 baseEnd_4745657 := by
    simpa [prefixWord, tailWord_4745657, baseEnd_4745657] using wordTrace_append hprefix tailTrace_4745657
  have hstable : (prefixWord ++ tailWord_4745657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745657).length < 2 ^ (prefixWord ++ tailWord_4745657).sum := by decide
  have hdescent : baseEnd_4745657 < baseStart_4745657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745703 : List Nat := [1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_4745703 : Nat := 118140960795 + 4745703 * 2 ^ 59
def prefixEnd_4745703 : Nat := 4983230072969 + 3 ^ 40 * 4745703 * 2
def baseEnd_4745703 : Nat := 2436826682484151148887415

theorem tailTrace_4745703 : CollatzResearch.WordTrace tailWord_4745703 prefixEnd_4745703 2436826682484151148887415 := by
  unfold tailWord_4745703
  simp only [CollatzResearch.WordTrace]
  refine ⟨173090008326136007390185763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115393338884090671593457175 173090008326136007390185763)
  ·
    refine ⟨259635012489204011085278645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173090008326136007390185763 259635012489204011085278645)
    ·
      refine ⟨24340782420862876039244873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 259635012489204011085278645 24340782420862876039244873)
      ·
        refine ⟨18255586815647157029433655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24340782420862876039244873 18255586815647157029433655)
        ·
          refine ⟨27383380223470735544150483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18255586815647157029433655 27383380223470735544150483)
          ·
            refine ⟨41075070335206103316225725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27383380223470735544150483 41075070335206103316225725)
            ·
              refine ⟨15403151375702288743584647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41075070335206103316225725 15403151375702288743584647)
              ·
                refine ⟨23104727063553433115376971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15403151375702288743584647 23104727063553433115376971)
                ·
                  refine ⟨34657090595330149673065457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23104727063553433115376971 34657090595330149673065457)
                  ·
                    refine ⟨25992817946497612254799093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34657090595330149673065457 25992817946497612254799093)
                    ·
                      refine ⟨2436826682484151148887415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25992817946497612254799093 2436826682484151148887415)
                      ·
                        rfl

theorem cell23_4745703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_4745703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745703 prefixEnd_4745703 := by exact prefixLift 4745703
  have htrace : WordTrace (prefixWord ++ tailWord_4745703) baseStart_4745703 baseEnd_4745703 := by
    simpa [prefixWord, tailWord_4745703, baseEnd_4745703] using wordTrace_append hprefix tailTrace_4745703
  have hstable : (prefixWord ++ tailWord_4745703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745703).length < 2 ^ (prefixWord ++ tailWord_4745703).sum := by decide
  have hdescent : baseEnd_4745703 < baseStart_4745703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745713 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 4, 1, 4]
def baseStart_4745713 : Nat := 118140960795 + 4745713 * 2 ^ 59
def prefixEnd_4745713 : Nat := 4983230072969 + 3 ^ 40 * 4745713 * 2
def baseEnd_4745713 : Nat := 2436831817290696109762369

theorem tailTrace_4745713 : CollatzResearch.WordTrace tailWord_4745713 prefixEnd_4745713 2436831817290696109762369 := by
  unfold tailWord_4745713
  simp only [CollatzResearch.WordTrace]
  refine ⟨173090373056099779098049793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115393582037399852732033195 173090373056099779098049793)
  ·
    refine ⟨129817779792074834323537345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173090373056099779098049793 129817779792074834323537345)
    ·
      refine ⟨97363334844056125742653009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129817779792074834323537345 97363334844056125742653009)
      ·
        refine ⟨73022501133042094306989757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97363334844056125742653009 73022501133042094306989757)
        ·
          refine ⟨27383437924890785365121159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73022501133042094306989757 27383437924890785365121159)
          ·
            refine ⟨41075156887336178047681739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27383437924890785365121159 41075156887336178047681739)
            ·
              refine ⟨61612735331004267071522609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41075156887336178047681739 61612735331004267071522609)
              ·
                refine ⟨46209551498253200303641957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61612735331004267071522609 46209551498253200303641957)
                ·
                  refine ⟨8664290905922475056932867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46209551498253200303641957 8664290905922475056932867)
                  ·
                    refine ⟨12996436358883712585399301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8664290905922475056932867 12996436358883712585399301)
                    ·
                      refine ⟨2436831817290696109762369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12996436358883712585399301 2436831817290696109762369)
                      ·
                        rfl

theorem cell23_4745713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_4745713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745713 prefixEnd_4745713 := by exact prefixLift 4745713
  have htrace : WordTrace (prefixWord ++ tailWord_4745713) baseStart_4745713 baseEnd_4745713 := by
    simpa [prefixWord, tailWord_4745713, baseEnd_4745713] using wordTrace_append hprefix tailTrace_4745713
  have hstable : (prefixWord ++ tailWord_4745713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745713).length < 2 ^ (prefixWord ++ tailWord_4745713).sum := by decide
  have hdescent : baseEnd_4745713 < baseStart_4745713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745733 : List Nat := [1, 3, 1, 1, 2, 2, 2, 3, 1, 4, 3]
def baseStart_4745733 : Nat := 118140960795 + 4745733 * 2 ^ 59
def prefixEnd_4745733 : Nat := 4983230072969 + 3 ^ 40 * 4745733 * 2
def baseEnd_4745733 : Nat := 2436842086903786031512277

theorem tailTrace_4745733 : CollatzResearch.WordTrace tailWord_4745733 prefixEnd_4745733 2436842086903786031512277 := by
  unfold tailWord_4745733
  simp only [CollatzResearch.WordTrace]
  refine ⟨173091102516027322513777853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115394068344018215009185235 173091102516027322513777853)
  ·
    refine ⟨64909163443510245942666695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173091102516027322513777853 64909163443510245942666695)
    ·
      refine ⟨97363745165265368914000043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64909163443510245942666695 97363745165265368914000043)
      ·
        refine ⟨146045617747898053371000065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97363745165265368914000043 146045617747898053371000065)
        ·
          refine ⟨109534213310923540028250049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146045617747898053371000065 109534213310923540028250049)
          ·
            refine ⟨82150659983192655021187537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109534213310923540028250049 82150659983192655021187537)
            ·
              refine ⟨61612994987394491265890653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82150659983192655021187537 61612994987394491265890653)
              ·
                refine ⟨23104873120272934224708995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61612994987394491265890653 23104873120272934224708995)
                ·
                  refine ⟨34657309680409401337063493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23104873120272934224708995 34657309680409401337063493)
                  ·
                    refine ⟨6498245565076762750699405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34657309680409401337063493 6498245565076762750699405)
                    ·
                      refine ⟨2436842086903786031512277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6498245565076762750699405 2436842086903786031512277)
                      ·
                        rfl

theorem cell23_4745733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 4, 3].length) (baseStart_4745733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745733 prefixEnd_4745733 := by exact prefixLift 4745733
  have htrace : WordTrace (prefixWord ++ tailWord_4745733) baseStart_4745733 baseEnd_4745733 := by
    simpa [prefixWord, tailWord_4745733, baseEnd_4745733] using wordTrace_append hprefix tailTrace_4745733
  have hstable : (prefixWord ++ tailWord_4745733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745733).length < 2 ^ (prefixWord ++ tailWord_4745733).sum := by decide
  have hdescent : baseEnd_4745733 < baseStart_4745733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745764 : List Nat := [2, 3, 1, 5, 1, 1, 1, 1, 2, 4, 2]
def baseStart_4745764 : Nat := 118140960795 + 4745764 * 2 ^ 59
def prefixEnd_4745764 : Nat := 4983230072969 + 3 ^ 40 * 4745764 * 2
def baseEnd_4745764 : Nat := 2436858004804075410224635

theorem tailTrace_4745764 : CollatzResearch.WordTrace tailWord_4745764 prefixEnd_4745764 2436858004804075410224635 := by
  unfold tailWord_4745764
  simp only [CollatzResearch.WordTrace]
  refine ⟨86546116589457507404078173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115394822119276676538770897 86546116589457507404078173)
  ·
    refine ⟨32454793721046565276529315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86546116589457507404078173 32454793721046565276529315)
    ·
      refine ⟨48682190581569847914793973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32454793721046565276529315 48682190581569847914793973)
      ·
        refine ⟨4563955367022173242011935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48682190581569847914793973 4563955367022173242011935)
        ·
          refine ⟨6845933050533259863017903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4563955367022173242011935 6845933050533259863017903)
          ·
            refine ⟨10268899575799889794526855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6845933050533259863017903 10268899575799889794526855)
            ·
              refine ⟨15403349363699834691790283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10268899575799889794526855 15403349363699834691790283)
              ·
                refine ⟨23105024045549752037685425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15403349363699834691790283 23105024045549752037685425)
                ·
                  refine ⟨17328768034162314028264069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23105024045549752037685425 17328768034162314028264069)
                  ·
                    refine ⟨3249144006405433880299513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17328768034162314028264069 3249144006405433880299513)
                    ·
                      refine ⟨2436858004804075410224635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3249144006405433880299513 2436858004804075410224635)
                      ·
                        rfl

theorem cell23_4745764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_4745764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745764 prefixEnd_4745764 := by exact prefixLift 4745764
  have htrace : WordTrace (prefixWord ++ tailWord_4745764) baseStart_4745764 baseEnd_4745764 := by
    simpa [prefixWord, tailWord_4745764, baseEnd_4745764] using wordTrace_append hprefix tailTrace_4745764
  have hstable : (prefixWord ++ tailWord_4745764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745764).length < 2 ^ (prefixWord ++ tailWord_4745764).sum := by decide
  have hdescent : baseEnd_4745764 < baseStart_4745764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745770 : List Nat := [3, 1, 4, 1, 1, 2, 2, 3, 6]
def baseStart_4745770 : Nat := 118140960795 + 4745770 * 2 ^ 59
def prefixEnd_4745770 : Nat := 4983230072969 + 3 ^ 40 * 4745770 * 2
def baseEnd_4745770 : Nat := 270762342854222487416623

theorem tailTrace_4745770 : CollatzResearch.WordTrace tailWord_4745770 prefixEnd_4745770 270762342854222487416623 := by
  unfold tailWord_4745770
  simp only [CollatzResearch.WordTrace]
  refine ⟨43273113004223319458218691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115394968011262185221916509 43273113004223319458218691)
  ·
    refine ⟨64909669506334979187328037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43273113004223319458218691 64909669506334979187328037)
    ·
      refine ⟨12170563032437808597624007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64909669506334979187328037 12170563032437808597624007)
      ·
        refine ⟨18255844548656712896436011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12170563032437808597624007 18255844548656712896436011)
        ·
          refine ⟨27383766822985069344654017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18255844548656712896436011 27383766822985069344654017)
          ·
            refine ⟨20537825117238802008490513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27383766822985069344654017 20537825117238802008490513)
            ·
              refine ⟨15403368837929101506367885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20537825117238802008490513 15403368837929101506367885)
              ·
                refine ⟨5776263314223413064887957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15403368837929101506367885 5776263314223413064887957)
                ·
                  refine ⟨270762342854222487416623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5776263314223413064887957 270762342854222487416623)
                  ·
                    rfl

theorem cell23_4745770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 6].length) (baseStart_4745770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745770 prefixEnd_4745770 := by exact prefixLift 4745770
  have htrace : WordTrace (prefixWord ++ tailWord_4745770) baseStart_4745770 baseEnd_4745770 := by
    simpa [prefixWord, tailWord_4745770, baseEnd_4745770] using wordTrace_append hprefix tailTrace_4745770
  have hstable : (prefixWord ++ tailWord_4745770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745770).length < 2 ^ (prefixWord ++ tailWord_4745770).sum := by decide
  have hdescent : baseEnd_4745770 < baseStart_4745770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745783 : List Nat := [1, 1, 3, 1, 2, 3, 1, 3, 3, 5]
def baseStart_4745783 : Nat := 118140960795 + 4745783 * 2 ^ 59
def prefixEnd_4745783 : Nat := 4983230072969 + 3 ^ 40 * 4745783 * 2
def baseEnd_4745783 : Nat := 812289253645503611962349

theorem tailTrace_4745783 : CollatzResearch.WordTrace tailWord_4745783 prefixEnd_4745783 812289253645503611962349 := by
  unfold tailWord_4745783
  simp only [CollatzResearch.WordTrace]
  refine ⟨173092926165846181053098003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115395284110564120702065335 173092926165846181053098003)
  ·
    refine ⟨259639389248769271579647005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173092926165846181053098003 259639389248769271579647005)
    ·
      refine ⟨97364770968288476842367627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 259639389248769271579647005 97364770968288476842367627)
      ·
        refine ⟨146047156452432715263551441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97364770968288476842367627 146047156452432715263551441)
        ·
          refine ⟨109535367339324536447663581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146047156452432715263551441 109535367339324536447663581)
          ·
            refine ⟨41075762752246701167873843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109535367339324536447663581 41075762752246701167873843)
            ·
              refine ⟨61613644128370051751810765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41075762752246701167873843 61613644128370051751810765)
              ·
                refine ⟨23105116548138769406929037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61613644128370051751810765 23105116548138769406929037)
                ·
                  refine ⟨8664418705552038527598389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23105116548138769406929037 8664418705552038527598389)
                  ·
                    refine ⟨812289253645503611962349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8664418705552038527598389 812289253645503611962349)
                    ·
                      rfl

theorem cell23_4745783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 5].length) (baseStart_4745783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745783 prefixEnd_4745783 := by exact prefixLift 4745783
  have htrace : WordTrace (prefixWord ++ tailWord_4745783) baseStart_4745783 baseEnd_4745783 := by
    simpa [prefixWord, tailWord_4745783, baseEnd_4745783] using wordTrace_append hprefix tailTrace_4745783
  have hstable : (prefixWord ++ tailWord_4745783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745783).length < 2 ^ (prefixWord ++ tailWord_4745783).sum := by decide
  have hdescent : baseEnd_4745783 < baseStart_4745783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745813 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 3, 6]
def baseStart_4745813 : Nat := 118140960795 + 4745813 * 2 ^ 59
def prefixEnd_4745813 : Nat := 4983230072969 + 3 ^ 40 * 4745813 * 2
def baseEnd_4745813 : Nat := 812294388452048572837303

theorem tailTrace_4745813 : CollatzResearch.WordTrace tailWord_4745813 prefixEnd_4745813 812294388452048572837303 := by
  unfold tailWord_4745813
  simp only [CollatzResearch.WordTrace]
  refine ⟨173094020355737496176690093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115396013570491664117793395 173094020355737496176690093)
  ·
    refine ⟨64910257633401561066258785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173094020355737496176690093 64910257633401561066258785)
    ·
      refine ⟨48682693225051170799694089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64910257633401561066258785 48682693225051170799694089)
      ·
        refine ⟨36512019918788378099770567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48682693225051170799694089 36512019918788378099770567)
        ·
          refine ⟨54768029878182567149655851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36512019918788378099770567 54768029878182567149655851)
          ·
            refine ⟨82152044817273850724483777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54768029878182567149655851 82152044817273850724483777)
            ·
              refine ⟨61614033612955388043362833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82152044817273850724483777 61614033612955388043362833)
              ·
                refine ⟨46210525209716541032522125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61614033612955388043362833 46210525209716541032522125)
                ·
                  refine ⟨17328946953643702887195797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46210525209716541032522125 17328946953643702887195797)
                  ·
                    refine ⟨812294388452048572837303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17328946953643702887195797 812294388452048572837303)
                    ·
                      rfl

theorem cell23_4745813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_4745813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745813 prefixEnd_4745813 := by exact prefixLift 4745813
  have htrace : WordTrace (prefixWord ++ tailWord_4745813) baseStart_4745813 baseEnd_4745813 := by
    simpa [prefixWord, tailWord_4745813, baseEnd_4745813] using wordTrace_append hprefix tailTrace_4745813
  have hstable : (prefixWord ++ tailWord_4745813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745813).length < 2 ^ (prefixWord ++ tailWord_4745813).sum := by decide
  have hdescent : baseEnd_4745813 < baseStart_4745813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745837 : List Nat := [1, 5, 1, 1, 3, 1, 1, 4, 1, 1, 4]
def baseStart_4745837 : Nat := 118140960795 + 4745837 * 2 ^ 59
def prefixEnd_4745837 : Nat := 4983230072969 + 3 ^ 40 * 4745837 * 2
def baseEnd_4745837 : Nat := 2436895488891853624611799

theorem tailTrace_4745837 : CollatzResearch.WordTrace tailWord_4745837 prefixEnd_4745837 2436895488891853624611799 := by
  unfold tailWord_4745837
  simp only [CollatzResearch.WordTrace]
  refine ⟨173094895707650548275563765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115396597138433698850375843 173094895707650548275563765)
  ·
    refine ⟨16227646472592238900834103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 173094895707650548275563765 16227646472592238900834103)
    ·
      refine ⟨24341469708888358351251155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16227646472592238900834103 24341469708888358351251155)
      ·
        refine ⟨36512204563332537526876733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24341469708888358351251155 36512204563332537526876733)
        ·
          refine ⟨13692076711249701572578775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36512204563332537526876733 13692076711249701572578775)
          ·
            refine ⟨20538115066874552358868163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13692076711249701572578775 20538115066874552358868163)
            ·
              refine ⟨30807172600311828538302245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20538115066874552358868163 30807172600311828538302245)
              ·
                refine ⟨5776344862558467850931671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30807172600311828538302245 5776344862558467850931671)
                ·
                  refine ⟨8664517293837701776397507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5776344862558467850931671 8664517293837701776397507)
                  ·
                    refine ⟨12996775940756552664596261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8664517293837701776397507 12996775940756552664596261)
                    ·
                      refine ⟨2436895488891853624611799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12996775940756552664596261 2436895488891853624611799)
                      ·
                        rfl

theorem cell23_4745837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_4745837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745837 prefixEnd_4745837 := by exact prefixLift 4745837
  have htrace : WordTrace (prefixWord ++ tailWord_4745837) baseStart_4745837 baseEnd_4745837 := by
    simpa [prefixWord, tailWord_4745837, baseEnd_4745837] using wordTrace_append hprefix tailTrace_4745837
  have hstable : (prefixWord ++ tailWord_4745837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745837).length < 2 ^ (prefixWord ++ tailWord_4745837).sum := by decide
  have hdescent : baseEnd_4745837 < baseStart_4745837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745857 : List Nat := [1, 2, 4, 2, 1, 1, 1, 5, 1, 2, 3]
def baseStart_4745857 : Nat := 118140960795 + 4745857 * 2 ^ 59
def prefixEnd_4745857 : Nat := 4983230072969 + 3 ^ 40 * 4745857 * 2
def baseEnd_4745857 : Nat := 2436905758504943546361707

theorem tailTrace_4745857 : CollatzResearch.WordTrace tailWord_4745857 prefixEnd_4745857 2436905758504943546361707 := by
  unfold tailWord_4745857
  simp only [CollatzResearch.WordTrace]
  refine ⟨173095625167578091691291825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115397083445052061127527883 173095625167578091691291825)
  ·
    refine ⟨129821718875683568768468869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173095625167578091691291825 129821718875683568768468869)
    ·
      refine ⟨24341572289190669144087913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129821718875683568768468869 24341572289190669144087913)
      ·
        refine ⟨18256179216893001858065935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24341572289190669144087913 18256179216893001858065935)
        ·
          refine ⟨27384268825339502787098903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18256179216893001858065935 27384268825339502787098903)
          ·
            refine ⟨41076403238009254180648355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27384268825339502787098903 41076403238009254180648355)
            ·
              refine ⟨61614604857013881270972533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41076403238009254180648355 61614604857013881270972533)
              ·
                refine ⟨5776369205345051369153675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61614604857013881270972533 5776369205345051369153675)
                ·
                  refine ⟨8664553808017577053730513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5776369205345051369153675 8664553808017577053730513)
                  ·
                    refine ⟨6498415356013182790297885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8664553808017577053730513 6498415356013182790297885)
                    ·
                      refine ⟨2436905758504943546361707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6498415356013182790297885 2436905758504943546361707)
                      ·
                        rfl

theorem cell23_4745857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_4745857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745857 prefixEnd_4745857 := by exact prefixLift 4745857
  have htrace : WordTrace (prefixWord ++ tailWord_4745857) baseStart_4745857 baseEnd_4745857 := by
    simpa [prefixWord, tailWord_4745857, baseEnd_4745857] using wordTrace_append hprefix tailTrace_4745857
  have hstable : (prefixWord ++ tailWord_4745857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745857).length < 2 ^ (prefixWord ++ tailWord_4745857).sum := by decide
  have hdescent : baseEnd_4745857 < baseStart_4745857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745860 : List Nat := [2, 3, 2, 1, 3, 3, 9]
def baseStart_4745860 : Nat := 118140960795 + 4745860 * 2 ^ 59
def prefixEnd_4745860 : Nat := 4983230072969 + 3 ^ 40 * 4745860 * 2
def baseEnd_4745860 : Nat := 30085275295640827587953

theorem tailTrace_4745860 : CollatzResearch.WordTrace tailWord_4745860 prefixEnd_4745860 30085275295640827587953 := by
  unfold tailWord_4745860
  simp only [CollatzResearch.WordTrace]
  refine ⟨86547867293283611601825517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115397156391044815469100689 86547867293283611601825517)
  ·
    refine ⟨32455450234981354350684569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86547867293283611601825517 32455450234981354350684569)
    ·
      refine ⟨24341587676236015763013427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32455450234981354350684569 24341587676236015763013427)
      ·
        refine ⟨36512381514354023644520141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24341587676236015763013427 36512381514354023644520141)
        ·
          refine ⟨13692143067882758866695053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36512381514354023644520141 13692143067882758866695053)
          ·
            refine ⟨5134553650456034575010645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13692143067882758866695053 5134553650456034575010645)
            ·
              refine ⟨30085275295640827587953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5134553650456034575010645 30085275295640827587953)
              ·
                rfl

theorem cell23_4745860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 9].length) (baseStart_4745860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745860 prefixEnd_4745860 := by exact prefixLift 4745860
  have htrace : WordTrace (prefixWord ++ tailWord_4745860) baseStart_4745860 baseEnd_4745860 := by
    simpa [prefixWord, tailWord_4745860, baseEnd_4745860] using wordTrace_append hprefix tailTrace_4745860
  have hstable : (prefixWord ++ tailWord_4745860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745860).length < 2 ^ (prefixWord ++ tailWord_4745860).sum := by decide
  have hdescent : baseEnd_4745860 < baseStart_4745860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745893 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 1, 2, 8]
def baseStart_4745893 : Nat := 118140960795 + 4745893 * 2 ^ 59
def prefixEnd_4745893 : Nat := 4983230072969 + 3 ^ 40 * 4745893 * 2
def baseEnd_4745893 : Nat := 2436924243808505405511541

theorem tailTrace_4745893 : CollatzResearch.WordTrace tailWord_4745893 prefixEnd_4745893 2436924243808505405511541 := by
  unfold tailWord_4745893
  simp only [CollatzResearch.WordTrace]
  refine ⟨173096938195447669839602333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115397958796965113226401555 173096938195447669839602333)
  ·
    refine ⟨64911351823292876189850875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173096938195447669839602333 64911351823292876189850875)
    ·
      refine ⟨97367027734939314284776313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64911351823292876189850875 97367027734939314284776313)
      ·
        refine ⟨73025270801204485713582235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97367027734939314284776313 73025270801204485713582235)
        ·
          refine ⟨109537906201806728570373353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73025270801204485713582235 109537906201806728570373353)
          ·
            refine ⟨82153429651355046427780015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109537906201806728570373353 82153429651355046427780015)
            ·
              refine ⟨123230144477032569641670023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82153429651355046427780015 123230144477032569641670023)
              ·
                refine ⟨184845216715548854462505035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123230144477032569641670023 184845216715548854462505035)
                ·
                  refine ⟨277267825073323281693757553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184845216715548854462505035 277267825073323281693757553)
                  ·
                    refine ⟨207950868804992461270318165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 277267825073323281693757553 207950868804992461270318165)
                    ·
                      refine ⟨2436924243808505405511541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 207950868804992461270318165 2436924243808505405511541)
                      ·
                        rfl

theorem cell23_4745893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_4745893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745893 prefixEnd_4745893 := by exact prefixLift 4745893
  have htrace : WordTrace (prefixWord ++ tailWord_4745893) baseStart_4745893 baseEnd_4745893 := by
    simpa [prefixWord, tailWord_4745893, baseEnd_4745893] using wordTrace_append hprefix tailTrace_4745893
  have hstable : (prefixWord ++ tailWord_4745893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745893).length < 2 ^ (prefixWord ++ tailWord_4745893).sum := by decide
  have hdescent : baseEnd_4745893 < baseStart_4745893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745944 : List Nat := [2, 1, 2, 2, 3, 3, 2, 1, 1, 4, 2]
def baseStart_4745944 : Nat := 118140960795 + 4745944 * 2 ^ 59
def prefixEnd_4745944 : Nat := 4983230072969 + 3 ^ 40 * 4745944 * 2
def baseEnd_4745944 : Nat := 2436950431321884705973807

theorem tailTrace_4745944 : CollatzResearch.WordTrace tailWord_4745944 prefixEnd_4745944 2436950431321884705973807 := by
  unfold tailWord_4745944
  simp only [CollatzResearch.WordTrace]
  refine ⟨86549399159131452774854443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115399198878841937033139257 86549399159131452774854443)
  ·
    refine ⟨129824098738697179162281665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86549399159131452774854443 129824098738697179162281665)
    ·
      refine ⟨97368074054022884371711249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129824098738697179162281665 97368074054022884371711249)
      ·
        refine ⟨73026055540517163278783437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97368074054022884371711249 73026055540517163278783437)
        ·
          refine ⟨27384770827693936229543789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73026055540517163278783437 27384770827693936229543789)
          ·
            refine ⟨10269289060385226086078921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27384770827693936229543789 10269289060385226086078921)
            ·
              refine ⟨7701966795288919564559191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10269289060385226086078921 7701966795288919564559191)
              ·
                refine ⟨11552950192933379346838787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7701966795288919564559191 11552950192933379346838787)
                ·
                  refine ⟨17329425289400069020258181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11552950192933379346838787 17329425289400069020258181)
                  ·
                    refine ⟨3249267241762512941298409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17329425289400069020258181 3249267241762512941298409)
                    ·
                      refine ⟨2436950431321884705973807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3249267241762512941298409 2436950431321884705973807)
                      ·
                        rfl

theorem cell23_4745944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 1, 4, 2].length) (baseStart_4745944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745944 prefixEnd_4745944 := by exact prefixLift 4745944
  have htrace : WordTrace (prefixWord ++ tailWord_4745944) baseStart_4745944 baseEnd_4745944 := by
    simpa [prefixWord, tailWord_4745944, baseEnd_4745944] using wordTrace_append hprefix tailTrace_4745944
  have hstable : (prefixWord ++ tailWord_4745944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745944).length < 2 ^ (prefixWord ++ tailWord_4745944).sum := by decide
  have hdescent : baseEnd_4745944 < baseStart_4745944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745967 : List Nat := [1, 1, 2, 1, 5, 2, 1, 5, 5]
def baseStart_4745967 : Nat := 118140960795 + 4745967 * 2 ^ 59
def prefixEnd_4745967 : Nat := 4983230072969 + 3 ^ 40 * 4745967 * 2
def baseEnd_4745967 : Nat := 270773582375215346220689

theorem tailTrace_4745967 : CollatzResearch.WordTrace tailWord_4745967 prefixEnd_4745967 270773582375215346220689 := by
  unfold tailWord_4745967
  simp only [CollatzResearch.WordTrace]
  refine ⟨173099637197179580477796155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115399758131453053651864103 173099637197179580477796155)
  ·
    refine ⟨259649455795769370716694233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173099637197179580477796155 259649455795769370716694233)
    ·
      refine ⟨194737091846827028037520675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259649455795769370716694233 194737091846827028037520675)
      ·
        refine ⟨292105637770240542056281013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194737091846827028037520675 292105637770240542056281013)
        ·
          refine ⟨27384903540960050817776345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 292105637770240542056281013 27384903540960050817776345)
          ·
            refine ⟨20538677655720038113332259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27384903540960050817776345 20538677655720038113332259)
            ·
              refine ⟨30808016483580057169998389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20538677655720038113332259 30808016483580057169998389)
              ·
                refine ⟨2888251545335630359687349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30808016483580057169998389 2888251545335630359687349)
                ·
                  refine ⟨270773582375215346220689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2888251545335630359687349 270773582375215346220689)
                  ·
                    rfl

theorem cell23_4745967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5, 5].length) (baseStart_4745967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745967 prefixEnd_4745967 := by exact prefixLift 4745967
  have htrace : WordTrace (prefixWord ++ tailWord_4745967) baseStart_4745967 baseEnd_4745967 := by
    simpa [prefixWord, tailWord_4745967, baseEnd_4745967] using wordTrace_append hprefix tailTrace_4745967
  have hstable : (prefixWord ++ tailWord_4745967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745967).length < 2 ^ (prefixWord ++ tailWord_4745967).sum := by decide
  have hdescent : baseEnd_4745967 < baseStart_4745967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4745972 : List Nat := [2, 6, 1, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_4745972 : Nat := 118140960795 + 4745972 * 2 ^ 59
def prefixEnd_4745972 : Nat := 4983230072969 + 3 ^ 40 * 4745972 * 2
def baseEnd_4745972 : Nat := 2436964808780210596423679

theorem tailTrace_4745972 : CollatzResearch.WordTrace tailWord_4745972 prefixEnd_4745972 2436964808780210596423679 := by
  unfold tailWord_4745972
  simp only [CollatzResearch.WordTrace]
  refine ⟨86549909781080733165864085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115399879708107644221152113 86549909781080733165864085)
  ·
    refine ⟨4057027020988159367149879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 86549909781080733165864085 4057027020988159367149879)
    ·
      refine ⟨6085540531482239050724819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4057027020988159367149879 6085540531482239050724819)
      ·
        refine ⟨9128310797223358576087229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6085540531482239050724819 9128310797223358576087229)
        ·
          refine ⟨3423116548958759466032711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9128310797223358576087229 3423116548958759466032711)
          ·
            refine ⟨5134674823438139199049067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3423116548958759466032711 5134674823438139199049067)
            ·
              refine ⟨7702012235157208798573601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5134674823438139199049067 7702012235157208798573601)
              ·
                refine ⟨5776509176367906598930201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7702012235157208798573601 5776509176367906598930201)
                ·
                  refine ⟨4332381882275929949197651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5776509176367906598930201 4332381882275929949197651)
                  ·
                    refine ⟨6498572823413894923796477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4332381882275929949197651 6498572823413894923796477)
                    ·
                      refine ⟨2436964808780210596423679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6498572823413894923796477 2436964808780210596423679)
                      ·
                        rfl

theorem cell23_4745972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_4745972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4745972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4745972 prefixEnd_4745972 := by exact prefixLift 4745972
  have htrace : WordTrace (prefixWord ++ tailWord_4745972) baseStart_4745972 baseEnd_4745972 := by
    simpa [prefixWord, tailWord_4745972, baseEnd_4745972] using wordTrace_append hprefix tailTrace_4745972
  have hstable : (prefixWord ++ tailWord_4745972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4745972).length < 2 ^ (prefixWord ++ tailWord_4745972).sum := by decide
  have hdescent : baseEnd_4745972 < baseStart_4745972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4745972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746010 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 2, 8]
def baseStart_4746010 : Nat := 118140960795 + 4746010 * 2 ^ 59
def prefixEnd_4746010 : Nat := 4983230072969 + 3 ^ 40 * 4746010 * 2
def baseEnd_4746010 : Nat := 812328107015027149249501

theorem tailTrace_4746010 : CollatzResearch.WordTrace tailWord_4746010 prefixEnd_4746010 812328107015027149249501 := by
  unfold tailWord_4746010
  simp only [CollatzResearch.WordTrace]
  refine ⟨43275301384005949705402871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115400803690682532547740989 43275301384005949705402871)
  ·
    refine ⟨64912952076008924558104307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43275301384005949705402871 64912952076008924558104307)
    ·
      refine ⟨97369428114013386837156461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64912952076008924558104307 97369428114013386837156461)
      ·
        refine ⟨36513535542755020063933673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97369428114013386837156461 36513535542755020063933673)
        ·
          refine ⟨27385151657066265047950255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36513535542755020063933673 27385151657066265047950255)
          ·
            refine ⟨41077727485599397571925383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27385151657066265047950255 41077727485599397571925383)
            ·
              refine ⟨61616591228399096357888075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41077727485599397571925383 61616591228399096357888075)
              ·
                refine ⟨92424886842598644536832113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61616591228399096357888075 92424886842598644536832113)
                ·
                  refine ⟨69318665131948983402624085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92424886842598644536832113 69318665131948983402624085)
                  ·
                    refine ⟨812328107015027149249501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69318665131948983402624085 812328107015027149249501)
                    ·
                      rfl

theorem cell23_4746010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_4746010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746010 prefixEnd_4746010 := by exact prefixLift 4746010
  have htrace : WordTrace (prefixWord ++ tailWord_4746010) baseStart_4746010 baseEnd_4746010 := by
    simpa [prefixWord, tailWord_4746010, baseEnd_4746010] using wordTrace_append hprefix tailTrace_4746010
  have hstable : (prefixWord ++ tailWord_4746010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746010).length < 2 ^ (prefixWord ++ tailWord_4746010).sum := by decide
  have hdescent : baseEnd_4746010 < baseStart_4746010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746017 : List Nat := [1, 2, 3, 2, 1, 2, 2, 3, 2, 1, 4]
def baseStart_4746017 : Nat := 118140960795 + 4746017 * 2 ^ 59
def prefixEnd_4746017 : Nat := 4983230072969 + 3 ^ 40 * 4746017 * 2
def baseEnd_4746017 : Nat := 2436987915409662920360971

theorem tailTrace_4746017 : CollatzResearch.WordTrace tailWord_4746017 prefixEnd_4746017 2436987915409662920360971 := by
  unfold tailWord_4746017
  simp only [CollatzResearch.WordTrace]
  refine ⟨173101460846998439017116305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115400973897998959344744203 173101460846998439017116305)
  ·
    refine ⟨129826095635248829262837229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173101460846998439017116305 129826095635248829262837229)
    ·
      refine ⟨48684785863218310973563961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129826095635248829262837229 48684785863218310973563961)
      ·
        refine ⟨36513589397413733230172971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48684785863218310973563961 36513589397413733230172971)
        ·
          refine ⟨54770384096120599845259457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36513589397413733230172971 54770384096120599845259457)
          ·
            refine ⟨41077788072090449883944593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54770384096120599845259457 41077788072090449883944593)
            ·
              refine ⟨30808341054067837412958445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41077788072090449883944593 30808341054067837412958445)
              ·
                refine ⟨11553127895275439029859417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30808341054067837412958445 11553127895275439029859417)
                ·
                  refine ⟨8664845921456579272394563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11553127895275439029859417 8664845921456579272394563)
                  ·
                    refine ⟨12997268882184868908591845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8664845921456579272394563 12997268882184868908591845)
                    ·
                      refine ⟨2436987915409662920360971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12997268882184868908591845 2436987915409662920360971)
                      ·
                        rfl

theorem cell23_4746017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_4746017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746017 prefixEnd_4746017 := by exact prefixLift 4746017
  have htrace : WordTrace (prefixWord ++ tailWord_4746017) baseStart_4746017 baseEnd_4746017 := by
    simpa [prefixWord, tailWord_4746017, baseEnd_4746017] using wordTrace_append hprefix tailTrace_4746017
  have hstable : (prefixWord ++ tailWord_4746017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746017).length < 2 ^ (prefixWord ++ tailWord_4746017).sum := by decide
  have hdescent : baseEnd_4746017 < baseStart_4746017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746040 : List Nat := [2, 1, 2, 1, 3, 2, 1, 3, 8]
def baseStart_4746040 : Nat := 118140960795 + 4746040 * 2 ^ 59
def prefixEnd_4746040 : Nat := 4983230072969 + 3 ^ 40 * 4746040 * 2
def baseEnd_4746040 : Nat := 270777747273857370041485

theorem tailTrace_4746040 : CollatzResearch.WordTrace tailWord_4746040 prefixEnd_4746040 270777747273857370041485 := by
  unfold tailWord_4746040
  simp only [CollatzResearch.WordTrace]
  refine ⟨86551149862957556972601787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115401533150610075963469049 86551149862957556972601787)
  ·
    refine ⟨129826724794436335458902681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86551149862957556972601787 129826724794436335458902681)
    ·
      refine ⟨97370043595827251594177011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129826724794436335458902681 97370043595827251594177011)
      ·
        refine ⟨146055065393740877391265517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97370043595827251594177011 146055065393740877391265517)
        ·
          refine ⟨54770649522652829021724569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146055065393740877391265517 54770649522652829021724569)
          ·
            refine ⟨41077987141989621766293427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54770649522652829021724569 41077987141989621766293427)
            ·
              refine ⟨61616980712984432649440141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41077987141989621766293427 61616980712984432649440141)
              ·
                refine ⟨23106367767369162243540053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61616980712984432649440141 23106367767369162243540053)
                ·
                  refine ⟨270777747273857370041485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23106367767369162243540053 270777747273857370041485)
                  ·
                    rfl

theorem cell23_4746040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 8].length) (baseStart_4746040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746040 prefixEnd_4746040 := by exact prefixLift 4746040
  have htrace : WordTrace (prefixWord ++ tailWord_4746040) baseStart_4746040 baseEnd_4746040 := by
    simpa [prefixWord, tailWord_4746040, baseEnd_4746040] using wordTrace_append hprefix tailTrace_4746040
  have hstable : (prefixWord ++ tailWord_4746040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746040).length < 2 ^ (prefixWord ++ tailWord_4746040).sum := by decide
  have hdescent : baseEnd_4746040 < baseStart_4746040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746057 : List Nat := [1, 2, 1, 1, 2, 6, 1, 3, 6]
def baseStart_4746057 : Nat := 118140960795 + 4746057 * 2 ^ 59
def prefixEnd_4746057 : Nat := 4983230072969 + 3 ^ 40 * 4746057 * 2
def baseEnd_4746057 : Nat := 270778717181760307095643

theorem tailTrace_4746057 : CollatzResearch.WordTrace tailWord_4746057 prefixEnd_4746057 270778717181760307095643 := by
  unfold tailWord_4746057
  simp only [CollatzResearch.WordTrace]
  refine ⟨173102919766853525848572425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115401946511235683899048283 173102919766853525848572425)
  ·
    refine ⟨129827189825140144386429319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173102919766853525848572425 129827189825140144386429319)
    ·
      refine ⟨194740784737710216579643979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129827189825140144386429319 194740784737710216579643979)
      ·
        refine ⟨292111177106565324869465969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194740784737710216579643979 292111177106565324869465969)
        ·
          refine ⟨219083382829923993652099477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292111177106565324869465969 219083382829923993652099477)
          ·
            refine ⟨10269533570152687202442163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 219083382829923993652099477 10269533570152687202442163)
            ·
              refine ⟨15404300355229030803663245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10269533570152687202442163 15404300355229030803663245)
              ·
                refine ⟨5776612633210886551373717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15404300355229030803663245 5776612633210886551373717)
                ·
                  refine ⟨270778717181760307095643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5776612633210886551373717 270778717181760307095643)
                  ·
                    rfl

theorem cell23_4746057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 6].length) (baseStart_4746057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746057 prefixEnd_4746057 := by exact prefixLift 4746057
  have htrace : WordTrace (prefixWord ++ tailWord_4746057) baseStart_4746057 baseEnd_4746057 := by
    simpa [prefixWord, tailWord_4746057, baseEnd_4746057] using wordTrace_append hprefix tailTrace_4746057
  have hstable : (prefixWord ++ tailWord_4746057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746057).length < 2 ^ (prefixWord ++ tailWord_4746057).sum := by decide
  have hdescent : baseEnd_4746057 < baseStart_4746057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746107 : List Nat := [1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 4]
def baseStart_4746107 : Nat := 118140960795 + 4746107 * 2 ^ 59
def prefixEnd_4746107 : Nat := 4983230072969 + 3 ^ 40 * 4746107 * 2
def baseEnd_4746107 : Nat := 2437034128668567568235557

theorem tailTrace_4746107 : CollatzResearch.WordTrace tailWord_4746107 prefixEnd_4746107 2437034128668567568235557 := by
  unfold tailWord_4746107
  simp only [CollatzResearch.WordTrace]
  refine ⟨173104743416672384387892575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115403162277781589591928383 173104743416672384387892575)
  ·
    refine ⟨259657115125008576581838863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173104743416672384387892575 259657115125008576581838863)
    ·
      refine ⟨389485672687512864872758295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259657115125008576581838863 389485672687512864872758295)
      ·
        refine ⟨584228509031269297309137443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389485672687512864872758295 584228509031269297309137443)
        ·
          refine ⟨876342763546903945963706165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 584228509031269297309137443 876342763546903945963706165)
          ·
            refine ⟨82157134082522244934097453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 876342763546903945963706165 82157134082522244934097453)
            ·
              refine ⟨30808925280945841850286545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82157134082522244934097453 30808925280945841850286545)
              ·
                refine ⟨23106693960709381387714909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30808925280945841850286545 23106693960709381387714909)
                ·
                  refine ⟨8665010235266018020393091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23106693960709381387714909 8665010235266018020393091)
                  ·
                    refine ⟨12997515352899027030589637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8665010235266018020393091 12997515352899027030589637)
                    ·
                      refine ⟨2437034128668567568235557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12997515352899027030589637 2437034128668567568235557)
                      ·
                        rfl

theorem cell23_4746107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 4].length) (baseStart_4746107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746107 prefixEnd_4746107 := by exact prefixLift 4746107
  have htrace : WordTrace (prefixWord ++ tailWord_4746107) baseStart_4746107 baseEnd_4746107 := by
    simpa [prefixWord, tailWord_4746107, baseEnd_4746107] using wordTrace_append hprefix tailTrace_4746107
  have hstable : (prefixWord ++ tailWord_4746107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746107).length < 2 ^ (prefixWord ++ tailWord_4746107).sum := by decide
  have hdescent : baseEnd_4746107 < baseStart_4746107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746117 : List Nat := [1, 3, 1, 1, 3, 3, 1, 3, 1, 6]
def baseStart_4746117 : Nat := 118140960795 + 4746117 * 2 ^ 59
def prefixEnd_4746117 : Nat := 4983230072969 + 3 ^ 40 * 4746117 * 2
def baseEnd_4746117 : Nat := 812346421158370843036837

theorem tailTrace_4746117 : CollatzResearch.WordTrace tailWord_4746117 prefixEnd_4746117 812346421158370843036837 := by
  unfold tailWord_4746117
  simp only [CollatzResearch.WordTrace]
  refine ⟨173105108146636156095756605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115403405431090770730504403 173105108146636156095756605)
  ·
    refine ⟨64914415554988558535908727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173105108146636156095756605 64914415554988558535908727)
    ·
      refine ⟨97371623332482837803863091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64914415554988558535908727 97371623332482837803863091)
      ·
        refine ⟨146057434998724256705794637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97371623332482837803863091 146057434998724256705794637)
        ·
          refine ⟨54771538124521596264672989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146057434998724256705794637 54771538124521596264672989)
          ·
            refine ⟨20539326796695598599252371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54771538124521596264672989 20539326796695598599252371)
            ·
              refine ⟨30808990195043397898878557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20539326796695598599252371 30808990195043397898878557)
              ·
                refine ⟨11553371323141274212079459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30808990195043397898878557 11553371323141274212079459)
                ·
                  refine ⟨17330056984711911318119189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11553371323141274212079459 17330056984711911318119189)
                  ·
                    refine ⟨812346421158370843036837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17330056984711911318119189 812346421158370843036837)
                    ·
                      rfl

theorem cell23_4746117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 6].length) (baseStart_4746117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746117 prefixEnd_4746117 := by exact prefixLift 4746117
  have htrace : WordTrace (prefixWord ++ tailWord_4746117) baseStart_4746117 baseEnd_4746117 := by
    simpa [prefixWord, tailWord_4746117, baseEnd_4746117] using wordTrace_append hprefix tailTrace_4746117
  have hstable : (prefixWord ++ tailWord_4746117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746117).length < 2 ^ (prefixWord ++ tailWord_4746117).sum := by decide
  have hdescent : baseEnd_4746117 < baseStart_4746117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746138 : List Nat := [3, 1, 1, 4, 3, 2, 2, 1, 1, 5]
def baseStart_4746138 : Nat := 118140960795 + 4746138 * 2 ^ 59
def prefixEnd_4746138 : Nat := 4983230072969 + 3 ^ 40 * 4746138 * 2
def baseEnd_4746138 : Nat := 812350015522952315649305

theorem tailTrace_4746138 : CollatzResearch.WordTrace tailWord_4746138 prefixEnd_4746138 812350015522952315649305 := by
  unfold tailWord_4746138
  simp only [CollatzResearch.WordTrace]
  refine ⟨43276468519890019170567767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115403916053040051121514045 43276468519890019170567767)
  ·
    refine ⟨64914702779835028755851651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43276468519890019170567767 64914702779835028755851651)
    ·
      refine ⟨97372054169752543133777477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64914702779835028755851651 97372054169752543133777477)
      ·
        refine ⟨18257260156828601837583277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97372054169752543133777477 18257260156828601837583277)
        ·
          refine ⟨6846472558810725689093729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18257260156828601837583277 6846472558810725689093729)
          ·
            refine ⟨5134854419108044266820297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6846472558810725689093729 5134854419108044266820297)
            ·
              refine ⟨3851140814331033200115223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5134854419108044266820297 3851140814331033200115223)
              ·
                refine ⟨5776711221496549800172835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3851140814331033200115223 5776711221496549800172835)
                ·
                  refine ⟨8665066832244824700259253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5776711221496549800172835 8665066832244824700259253)
                  ·
                    refine ⟨812350015522952315649305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8665066832244824700259253 812350015522952315649305)
                    ·
                      rfl

theorem cell23_4746138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 1, 5].length) (baseStart_4746138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746138 prefixEnd_4746138 := by exact prefixLift 4746138
  have htrace : WordTrace (prefixWord ++ tailWord_4746138) baseStart_4746138 baseEnd_4746138 := by
    simpa [prefixWord, tailWord_4746138, baseEnd_4746138] using wordTrace_append hprefix tailTrace_4746138
  have hstable : (prefixWord ++ tailWord_4746138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746138).length < 2 ^ (prefixWord ++ tailWord_4746138).sum := by decide
  have hdescent : baseEnd_4746138 < baseStart_4746138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746141 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 5, 2, 2]
def baseStart_4746141 : Nat := 118140960795 + 4746141 * 2 ^ 59
def prefixEnd_4746141 : Nat := 4983230072969 + 3 ^ 40 * 4746141 * 2
def baseEnd_4746141 : Nat := 2437051587010820435210401

theorem tailTrace_4746141 : CollatzResearch.WordTrace tailWord_4746141 prefixEnd_4746141 2437051587010820435210401 := by
  unfold tailWord_4746141
  simp only [CollatzResearch.WordTrace]
  refine ⟨173105983498549208194630277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115403988999032805463086851 173105983498549208194630277)
  ·
    refine ⟨32457371905977976536493177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173105983498549208194630277 32457371905977976536493177)
    ·
      refine ⟨24343028929483482402369883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32457371905977976536493177 24343028929483482402369883)
      ·
        refine ⟨36514543394225223603554825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24343028929483482402369883 36514543394225223603554825)
        ·
          refine ⟨27385907545668917702666119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36514543394225223603554825 27385907545668917702666119)
          ·
            refine ⟨41078861318503376553999179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27385907545668917702666119 41078861318503376553999179)
            ·
              refine ⟨61618291977755064830998769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41078861318503376553999179 61618291977755064830998769)
              ·
                refine ⟨46213718983316298623249077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61618291977755064830998769 46213718983316298623249077)
                ·
                  refine ⟨4332536154685902995929601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46213718983316298623249077 4332536154685902995929601)
                  ·
                    refine ⟨3249402116014427246947201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4332536154685902995929601 3249402116014427246947201)
                    ·
                      refine ⟨2437051587010820435210401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3249402116014427246947201 2437051587010820435210401)
                      ·
                        rfl

theorem cell23_4746141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_4746141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746141 prefixEnd_4746141 := by exact prefixLift 4746141
  have htrace : WordTrace (prefixWord ++ tailWord_4746141) baseStart_4746141 baseEnd_4746141 := by
    simpa [prefixWord, tailWord_4746141, baseEnd_4746141] using wordTrace_append hprefix tailTrace_4746141
  have hstable : (prefixWord ++ tailWord_4746141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746141).length < 2 ^ (prefixWord ++ tailWord_4746141).sum := by decide
  have hdescent : baseEnd_4746141 < baseStart_4746141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746151 : List Nat := [1, 1, 6, 1, 3, 1, 1, 1, 4, 4]
def baseStart_4746151 : Nat := 118140960795 + 4746151 * 2 ^ 59
def prefixEnd_4746151 : Nat := 4983230072969 + 3 ^ 40 * 4746151 * 2
def baseEnd_4746151 : Nat := 812352240605788465361785

theorem tailTrace_4746151 : CollatzResearch.WordTrace tailWord_4746151 prefixEnd_4746151 812352240605788465361785 := by
  unfold tailWord_4746151
  simp only [CollatzResearch.WordTrace]
  refine ⟨173106348228512979902494307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115404232152341986601662871 173106348228512979902494307)
  ·
    refine ⟨259659522342769469853741461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173106348228512979902494307 259659522342769469853741461)
    ·
      refine ⟨12171540109817318899394131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 259659522342769469853741461 12171540109817318899394131)
      ·
        refine ⟨18257310164725978349091197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12171540109817318899394131 18257310164725978349091197)
        ·
          refine ⟨6846491311772241880909199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18257310164725978349091197 6846491311772241880909199)
          ·
            refine ⟨10269736967658362821363799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6846491311772241880909199 10269736967658362821363799)
            ·
              refine ⟨15404605451487544232045699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10269736967658362821363799 15404605451487544232045699)
              ·
                refine ⟨23106908177231316348068549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15404605451487544232045699 23106908177231316348068549)
                ·
                  refine ⟨4332545283230871815262853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23106908177231316348068549 4332545283230871815262853)
                  ·
                    refine ⟨812352240605788465361785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4332545283230871815262853 812352240605788465361785)
                    ·
                      rfl

theorem cell23_4746151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_4746151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746151 prefixEnd_4746151 := by exact prefixLift 4746151
  have htrace : WordTrace (prefixWord ++ tailWord_4746151) baseStart_4746151 baseEnd_4746151 := by
    simpa [prefixWord, tailWord_4746151, baseEnd_4746151] using wordTrace_append hprefix tailTrace_4746151
  have hstable : (prefixWord ++ tailWord_4746151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746151).length < 2 ^ (prefixWord ++ tailWord_4746151).sum := by decide
  have hdescent : baseEnd_4746151 < baseStart_4746151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746187 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 5]
def baseStart_4746187 : Nat := 118140960795 + 4746187 * 2 ^ 59
def prefixEnd_4746187 : Nat := 4983230072969 + 3 ^ 40 * 4746187 * 2
def baseEnd_4746187 : Nat := 2437075207120927255235189

theorem tailTrace_4746187 : CollatzResearch.WordTrace tailWord_4746187 prefixEnd_4746187 2437075207120927255235189 := by
  unfold tailWord_4746187
  simp only [CollatzResearch.WordTrace]
  refine ⟨173107661256382558050804815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115405107504255038700536543 173107661256382558050804815)
  ·
    refine ⟨259661491884573837076207223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173107661256382558050804815 259661491884573837076207223)
    ·
      refine ⟨389492237826860755614310835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259661491884573837076207223 389492237826860755614310835)
      ·
        refine ⟨584238356740291133421466253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389492237826860755614310835 584238356740291133421466253)
        ·
          refine ⟨219089383777609175033049845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 584238356740291133421466253 219089383777609175033049845)
          ·
            refine ⟨20539629729150860159348423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 219089383777609175033049845 20539629729150860159348423)
            ·
              refine ⟨30809444593726290239022635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20539629729150860159348423 30809444593726290239022635)
              ·
                refine ⟨46214166890589435358533953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30809444593726290239022635 46214166890589435358533953)
                ·
                  refine ⟨34660625167942076518900465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46214166890589435358533953 34660625167942076518900465)
                  ·
                    refine ⟨25995468875956557389175349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34660625167942076518900465 25995468875956557389175349)
                    ·
                      refine ⟨2437075207120927255235189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25995468875956557389175349 2437075207120927255235189)
                      ·
                        rfl

theorem cell23_4746187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 5].length) (baseStart_4746187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746187 prefixEnd_4746187 := by exact prefixLift 4746187
  have htrace : WordTrace (prefixWord ++ tailWord_4746187) baseStart_4746187 baseEnd_4746187 := by
    simpa [prefixWord, tailWord_4746187, baseEnd_4746187] using wordTrace_append hprefix tailTrace_4746187
  have hstable : (prefixWord ++ tailWord_4746187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746187).length < 2 ^ (prefixWord ++ tailWord_4746187).sum := by decide
  have hdescent : baseEnd_4746187 < baseStart_4746187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746225 : List Nat := [1, 2, 2, 2, 4, 3, 2, 1, 2, 1, 3]
def baseStart_4746225 : Nat := 118140960795 + 4746225 * 2 ^ 59
def prefixEnd_4746225 : Nat := 4983230072969 + 3 ^ 40 * 4746225 * 2
def baseEnd_4746225 : Nat := 2437094719385798106560015

theorem tailTrace_4746225 : CollatzResearch.WordTrace tailWord_4746225 prefixEnd_4746225 2437094719385798106560015 := by
  unfold tailWord_4746225
  simp only [CollatzResearch.WordTrace]
  refine ⟨173109047230244890540688129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115406031486829927027125419 173109047230244890540688129)
  ·
    refine ⟨129831785422683667905516097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173109047230244890540688129 129831785422683667905516097)
    ·
      refine ⟨97373839067012750929137073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129831785422683667905516097 97373839067012750929137073)
      ·
        refine ⟨73030379300259563196852805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97373839067012750929137073 73030379300259563196852805)
        ·
          refine ⟨13693196118798668099409901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73030379300259563196852805 13693196118798668099409901)
          ·
            refine ⟨5134948544549500537278713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13693196118798668099409901 5134948544549500537278713)
            ·
              refine ⟨3851211408412125402959035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5134948544549500537278713 3851211408412125402959035)
              ·
                refine ⟨5776817112618188104438553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3851211408412125402959035 5776817112618188104438553)
                ·
                  refine ⟨4332612834463641078328915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5776817112618188104438553 4332612834463641078328915)
                  ·
                    refine ⟨6498919251695461617493373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4332612834463641078328915 6498919251695461617493373)
                    ·
                      refine ⟨2437094719385798106560015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6498919251695461617493373 2437094719385798106560015)
                      ·
                        rfl

theorem cell23_4746225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 2, 1, 3].length) (baseStart_4746225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746225 prefixEnd_4746225 := by exact prefixLift 4746225
  have htrace : WordTrace (prefixWord ++ tailWord_4746225) baseStart_4746225 baseEnd_4746225 := by
    simpa [prefixWord, tailWord_4746225, baseEnd_4746225] using wordTrace_append hprefix tailTrace_4746225
  have hstable : (prefixWord ++ tailWord_4746225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746225).length < 2 ^ (prefixWord ++ tailWord_4746225).sum := by decide
  have hdescent : baseEnd_4746225 < baseStart_4746225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746237 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 9]
def baseStart_4746237 : Nat := 118140960795 + 4746237 * 2 ^ 59
def prefixEnd_4746237 : Nat := 4983230072969 + 3 ^ 40 * 4746237 * 2
def baseEnd_4746237 : Nat := 270788986794850228845551

theorem tailTrace_4746237 : CollatzResearch.WordTrace tailWord_4746237 prefixEnd_4746237 270788986794850228845551 := by
  unfold tailWord_4746237
  simp only [CollatzResearch.WordTrace]
  refine ⟨173109484906201416590124965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115406323270800944393416643 173109484906201416590124965)
  ·
    refine ⟨32458028419912765610648431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173109484906201416590124965 32458028419912765610648431)
    ·
      refine ⟨48687042629869148415972647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32458028419912765610648431 48687042629869148415972647)
      ·
        refine ⟨73030563944803722623958971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48687042629869148415972647 73030563944803722623958971)
        ·
          refine ⟨109545845917205583935938457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73030563944803722623958971 109545845917205583935938457)
          ·
            refine ⟨82159384437904187951953843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109545845917205583935938457 82159384437904187951953843)
            ·
              refine ⟨123239076656856281927930765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82159384437904187951953843 123239076656856281927930765)
              ·
                refine ⟨46214653746321105722974037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123239076656856281927930765 46214653746321105722974037)
                ·
                  refine ⟨270788986794850228845551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46214653746321105722974037 270788986794850228845551)
                  ·
                    rfl

theorem cell23_4746237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_4746237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746237 prefixEnd_4746237 := by exact prefixLift 4746237
  have htrace : WordTrace (prefixWord ++ tailWord_4746237) baseStart_4746237 baseEnd_4746237 := by
    simpa [prefixWord, tailWord_4746237, baseEnd_4746237] using wordTrace_append hprefix tailTrace_4746237
  have hstable : (prefixWord ++ tailWord_4746237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746237).length < 2 ^ (prefixWord ++ tailWord_4746237).sum := by decide
  have hdescent : baseEnd_4746237 < baseStart_4746237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746271 : List Nat := [1, 1, 2, 4, 1, 4, 1, 4, 5]
def baseStart_4746271 : Nat := 118140960795 + 4746271 * 2 ^ 59
def prefixEnd_4746271 : Nat := 4983230072969 + 3 ^ 40 * 4746271 * 2
def baseEnd_4746271 : Nat := 270790926610656102953867

theorem tailTrace_4746271 : CollatzResearch.WordTrace tailWord_4746271 prefixEnd_4746271 270790926610656102953867 := by
  unfold tailWord_4746271
  simp only [CollatzResearch.WordTrace]
  refine ⟨173110724988078240396862667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115407149992052160264575111 173110724988078240396862667)
  ·
    refine ⟨259666087482117360595294001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173110724988078240396862667 259666087482117360595294001)
    ·
      refine ⟨194749565611588020446470501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259666087482117360595294001 194749565611588020446470501)
      ·
        refine ⟨36515543552172753833713219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 194749565611588020446470501 36515543552172753833713219)
        ·
          refine ⟨54773315328259130750569829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36515543552172753833713219 54773315328259130750569829)
          ·
            refine ⟨10269996624048587015731843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54773315328259130750569829 10269996624048587015731843)
            ·
              refine ⟨15404994936072880523597765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10269996624048587015731843 15404994936072880523597765)
              ·
                refine ⟨2888436550513665098174581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15404994936072880523597765 2888436550513665098174581)
                ·
                  refine ⟨270790926610656102953867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2888436550513665098174581 270790926610656102953867)
                  ·
                    rfl

theorem cell23_4746271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4, 5].length) (baseStart_4746271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746271 prefixEnd_4746271 := by exact prefixLift 4746271
  have htrace : WordTrace (prefixWord ++ tailWord_4746271) baseStart_4746271 baseEnd_4746271 := by
    simpa [prefixWord, tailWord_4746271, baseEnd_4746271] using wordTrace_append hprefix tailTrace_4746271
  have hstable : (prefixWord ++ tailWord_4746271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746271).length < 2 ^ (prefixWord ++ tailWord_4746271).sum := by decide
  have hdescent : baseEnd_4746271 < baseStart_4746271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746301 : List Nat := [1, 4, 1, 3, 1, 2, 3, 1, 2, 5]
def baseStart_4746301 : Nat := 118140960795 + 4746301 * 2 ^ 59
def prefixEnd_4746301 : Nat := 4983230072969 + 3 ^ 40 * 4746301 * 2
def baseEnd_4746301 : Nat := 812377914638513269736555

theorem tailTrace_4746301 : CollatzResearch.WordTrace tailWord_4746301 prefixEnd_4746301 812377914638513269736555 := by
  unfold tailWord_4746301
  simp only [CollatzResearch.WordTrace]
  refine ⟨173111819177969555520454757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115407879451979703680303171 173111819177969555520454757)
  ·
    refine ⟨32458466095869291660085267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173111819177969555520454757 32458466095869291660085267)
    ·
      refine ⟨48687699143803937490127901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32458466095869291660085267 48687699143803937490127901)
      ·
        refine ⟨18257887178926476558797963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48687699143803937490127901 18257887178926476558797963)
        ·
          refine ⟨27386830768389714838196945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18257887178926476558797963 27386830768389714838196945)
          ·
            refine ⟨20540123076292286128647709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27386830768389714838196945 20540123076292286128647709)
            ·
              refine ⟨7702546153609607298242891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20540123076292286128647709 7702546153609607298242891)
              ·
                refine ⟨11553819230414410947364337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7702546153609607298242891 11553819230414410947364337)
                ·
                  refine ⟨8665364422810808210523253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11553819230414410947364337 8665364422810808210523253)
                  ·
                    refine ⟨812377914638513269736555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8665364422810808210523253 812377914638513269736555)
                    ·
                      rfl

theorem cell23_4746301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_4746301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746301 prefixEnd_4746301 := by exact prefixLift 4746301
  have htrace : WordTrace (prefixWord ++ tailWord_4746301) baseStart_4746301 baseEnd_4746301 := by
    simpa [prefixWord, tailWord_4746301, baseEnd_4746301] using wordTrace_append hprefix tailTrace_4746301
  have hstable : (prefixWord ++ tailWord_4746301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746301).length < 2 ^ (prefixWord ++ tailWord_4746301).sum := by decide
  have hdescent : baseEnd_4746301 < baseStart_4746301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746304 : List Nat := [2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 4]
def baseStart_4746304 : Nat := 118140960795 + 4746304 * 2 ^ 59
def prefixEnd_4746304 : Nat := 4983230072969 + 3 ^ 40 * 4746304 * 2
def baseEnd_4746304 : Nat := 2437135284357503297472151

theorem tailTrace_4746304 : CollatzResearch.WordTrace tailWord_4746304 prefixEnd_4746304 2437135284357503297472151 := by
  unfold tailWord_4746304
  simp only [CollatzResearch.WordTrace]
  refine ⟨86555964298479343516406983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115407952397972458021875977 86555964298479343516406983)
  ·
    refine ⟨129833946447719015274610475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86555964298479343516406983 129833946447719015274610475)
    ·
      refine ⟨194750919671578522911915713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129833946447719015274610475 194750919671578522911915713)
      ·
        refine ⟨146063189753683892183936785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194750919671578522911915713 146063189753683892183936785)
        ·
          refine ⟨109547392315262919137952589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146063189753683892183936785 109547392315262919137952589)
          ·
            refine ⟨41080272118223594676732221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109547392315262919137952589 41080272118223594676732221)
            ·
              refine ⟨15405102044333848003774583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41080272118223594676732221 15405102044333848003774583)
              ·
                refine ⟨23107653066500772005661875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15405102044333848003774583 23107653066500772005661875)
                ·
                  refine ⟨34661479599751158008492813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23107653066500772005661875 34661479599751158008492813)
                  ·
                    refine ⟨12998054849906684253184805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34661479599751158008492813 12998054849906684253184805)
                    ·
                      refine ⟨2437135284357503297472151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12998054849906684253184805 2437135284357503297472151)
                      ·
                        rfl

theorem cell23_4746304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_4746304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746304 prefixEnd_4746304 := by exact prefixLift 4746304
  have htrace : WordTrace (prefixWord ++ tailWord_4746304) baseStart_4746304 baseEnd_4746304 := by
    simpa [prefixWord, tailWord_4746304, baseEnd_4746304] using wordTrace_append hprefix tailTrace_4746304
  have hstable : (prefixWord ++ tailWord_4746304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746304).length < 2 ^ (prefixWord ++ tailWord_4746304).sum := by decide
  have hdescent : baseEnd_4746304 < baseStart_4746304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746321 : List Nat := [1, 2, 2, 1, 3, 1, 3, 2, 2, 4, 2]
def baseStart_4746321 : Nat := 118140960795 + 4746321 * 2 ^ 59
def prefixEnd_4746321 : Nat := 4983230072969 + 3 ^ 40 * 4746321 * 2
def baseEnd_4746321 : Nat := 2437144013528629730959573

theorem tailTrace_4746321 : CollatzResearch.WordTrace tailWord_4746321 prefixEnd_4746321 2437144013528629730959573 := by
  unfold tailWord_4746321
  simp only [CollatzResearch.WordTrace]
  refine ⟨173112548637897098936182817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115408365758598065957455211 173112548637897098936182817)
  ·
    refine ⟨129834411478422824202137113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173112548637897098936182817 129834411478422824202137113)
    ·
      refine ⟨97375808608817118151602835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129834411478422824202137113 97375808608817118151602835)
      ·
        refine ⟨146063712913225677227404253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97375808608817118151602835 146063712913225677227404253)
        ·
          refine ⟨54773892342459628960276595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146063712913225677227404253 54773892342459628960276595)
          ·
            refine ⟨82160838513689443440414893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54773892342459628960276595 82160838513689443440414893)
            ·
              refine ⟨30810314442633541290155585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82160838513689443440414893 30810314442633541290155585)
              ·
                refine ⟨23107735831975155967616689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30810314442633541290155585 23107735831975155967616689)
                ·
                  refine ⟨17330801873981366975712517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23107735831975155967616689 17330801873981366975712517)
                  ·
                    refine ⟨3249525351371506307946097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17330801873981366975712517 3249525351371506307946097)
                    ·
                      refine ⟨2437144013528629730959573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3249525351371506307946097 2437144013528629730959573)
                      ·
                        rfl

theorem cell23_4746321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 4, 2].length) (baseStart_4746321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746321 prefixEnd_4746321 := by exact prefixLift 4746321
  have htrace : WordTrace (prefixWord ++ tailWord_4746321) baseStart_4746321 baseEnd_4746321 := by
    simpa [prefixWord, tailWord_4746321, baseEnd_4746321] using wordTrace_append hprefix tailTrace_4746321
  have hstable : (prefixWord ++ tailWord_4746321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746321).length < 2 ^ (prefixWord ++ tailWord_4746321).sum := by decide
  have hdescent : baseEnd_4746321 < baseStart_4746321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746324 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_4746324 : Nat := 118140960795 + 4746324 * 2 ^ 59
def prefixEnd_4746324 : Nat := 4983230072969 + 3 ^ 40 * 4746324 * 2
def baseEnd_4746324 : Nat := 2437145553970593219222059

theorem tailTrace_4746324 : CollatzResearch.WordTrace tailWord_4746324 prefixEnd_4746324 2437145553970593219222059 := by
  unfold tailWord_4746324
  simp only [CollatzResearch.WordTrace]
  refine ⟨86556329028443115224271013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115408438704590820299028017 86556329028443115224271013)
  ·
    refine ⟨16229311692833084104550815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86556329028443115224271013 16229311692833084104550815)
    ·
      refine ⟨24343967539249626156826223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16229311692833084104550815 24343967539249626156826223)
      ·
        refine ⟨36515951308874439235239335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24343967539249626156826223 36515951308874439235239335)
        ·
          refine ⟨54773926963311658852859003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36515951308874439235239335 54773926963311658852859003)
          ·
            refine ⟨82160890444967488279288505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54773926963311658852859003 82160890444967488279288505)
            ·
              refine ⟨61620667833725616209466379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82160890444967488279288505 61620667833725616209466379)
              ·
                refine ⟨92431001750588424314199569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61620667833725616209466379 92431001750588424314199569)
                ·
                  refine ⟨69323251312941318235649677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92431001750588424314199569 69323251312941318235649677)
                  ·
                    refine ⟨25996219242352994338368629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69323251312941318235649677 25996219242352994338368629)
                    ·
                      refine ⟨2437145553970593219222059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25996219242352994338368629 2437145553970593219222059)
                      ·
                        rfl

theorem cell23_4746324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_4746324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746324 prefixEnd_4746324 := by exact prefixLift 4746324
  have htrace : WordTrace (prefixWord ++ tailWord_4746324) baseStart_4746324 baseEnd_4746324 := by
    simpa [prefixWord, tailWord_4746324, baseEnd_4746324] using wordTrace_append hprefix tailTrace_4746324
  have hstable : (prefixWord ++ tailWord_4746324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746324).length < 2 ^ (prefixWord ++ tailWord_4746324).sum := by decide
  have hdescent : baseEnd_4746324 < baseStart_4746324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746358 : List Nat := [5, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3]
def baseStart_4746358 : Nat := 118140960795 + 4746358 * 2 ^ 59
def prefixEnd_4746358 : Nat := 4983230072969 + 3 ^ 40 * 4746358 * 2
def baseEnd_4746358 : Nat := 2437163012312846086196903

theorem tailTrace_4746358 : CollatzResearch.WordTrace tailWord_4746358 prefixEnd_4746358 2437163012312846086196903 := by
  unfold tailWord_4746358
  simp only [CollatzResearch.WordTrace]
  refine ⟨10819618633672690890954983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115409265425842036170186485 10819618633672690890954983)
  ·
    refine ⟨16229427950509036336432475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10819618633672690890954983 16229427950509036336432475)
    ·
      refine ⟨24344141925763554504648713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16229427950509036336432475 24344141925763554504648713)
      ·
        refine ⟨18258106444322665878486535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24344141925763554504648713 18258106444322665878486535)
        ·
          refine ⟨27387159666483998817729803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18258106444322665878486535 27387159666483998817729803)
          ·
            refine ⟨41080739499725998226594705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27387159666483998817729803 41080739499725998226594705)
            ·
              refine ⟨30810554624794498669946029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41080739499725998226594705 30810554624794498669946029)
              ·
                refine ⟨11553957984297937001229761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30810554624794498669946029 11553957984297937001229761)
                ·
                  refine ⟨8665468488223452750922321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11553957984297937001229761 8665468488223452750922321)
                  ·
                    refine ⟨6499101366167589563191741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8665468488223452750922321 6499101366167589563191741)
                    ·
                      refine ⟨2437163012312846086196903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6499101366167589563191741 2437163012312846086196903)
                      ·
                        rfl

theorem cell23_4746358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_4746358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746358 prefixEnd_4746358 := by exact prefixLift 4746358
  have htrace : WordTrace (prefixWord ++ tailWord_4746358) baseStart_4746358 baseEnd_4746358 := by
    simpa [prefixWord, tailWord_4746358, baseEnd_4746358] using wordTrace_append hprefix tailTrace_4746358
  have hstable : (prefixWord ++ tailWord_4746358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746358).length < 2 ^ (prefixWord ++ tailWord_4746358).sum := by decide
  have hdescent : baseEnd_4746358 < baseStart_4746358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746382 : List Nat := [4, 1, 1, 3, 2, 2, 3, 2, 1, 4]
def baseStart_4746382 : Nat := 118140960795 + 4746382 * 2 ^ 59
def prefixEnd_4746382 : Nat := 4983230072969 + 3 ^ 40 * 4746382 * 2
def baseEnd_4746382 : Nat := 812391778616184664098931

theorem tailTrace_4746382 : CollatzResearch.WordTrace tailWord_4746382 prefixEnd_4746382 812391778616184664098931 := by
  unfold tailWord_4746382
  simp only [CollatzResearch.WordTrace]
  refine ⟨21639346686334513294269175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115409848993784070902768933 21639346686334513294269175)
  ·
    refine ⟨32459020029501769941403763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21639346686334513294269175 32459020029501769941403763)
    ·
      refine ⟨48688530044252654912105645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32459020029501769941403763 48688530044252654912105645)
      ·
        refine ⟨18258198766594745592039617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48688530044252654912105645 18258198766594745592039617)
        ·
          refine ⟨13693649074946059194029713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18258198766594745592039617 13693649074946059194029713)
          ·
            refine ⟨10270236806209544395522285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13693649074946059194029713 10270236806209544395522285)
            ·
              refine ⟨3851338802328579148320857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10270236806209544395522285 3851338802328579148320857)
              ·
                refine ⟨2888504101746434361240643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3851338802328579148320857 2888504101746434361240643)
                ·
                  refine ⟨4332756152619651541860965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2888504101746434361240643 4332756152619651541860965)
                  ·
                    refine ⟨812391778616184664098931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4332756152619651541860965 812391778616184664098931)
                    ·
                      rfl

theorem cell23_4746382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_4746382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746382 prefixEnd_4746382 := by exact prefixLift 4746382
  have htrace : WordTrace (prefixWord ++ tailWord_4746382) baseStart_4746382 baseEnd_4746382 := by
    simpa [prefixWord, tailWord_4746382, baseEnd_4746382] using wordTrace_append hprefix tailTrace_4746382
  have hstable : (prefixWord ++ tailWord_4746382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746382).length < 2 ^ (prefixWord ++ tailWord_4746382).sum := by decide
  have hdescent : baseEnd_4746382 < baseStart_4746382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746424 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 3, 1, 6]
def baseStart_4746424 : Nat := 118140960795 + 4746424 * 2 ^ 59
def prefixEnd_4746424 : Nat := 4983230072969 + 3 ^ 40 * 4746424 * 2
def baseEnd_4746424 : Nat := 2437196902036042827971599

theorem tailTrace_4746424 : CollatzResearch.WordTrace tailWord_4746424 prefixEnd_4746424 2437196902036042827971599 := by
  unfold tailWord_4746424
  simp only [CollatzResearch.WordTrace]
  refine ⟨86558152678261973763591163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115410870237682631684788217 86558152678261973763591163)
  ·
    refine ⟨129837229017392960645386745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86558152678261973763591163 129837229017392960645386745)
    ·
      refine ⟨97377921763044720484040059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129837229017392960645386745 97377921763044720484040059)
      ·
        refine ⟨146066882644567080726060089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97377921763044720484040059 146066882644567080726060089)
        ·
          refine ⟨109550161983425310544545067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146066882644567080726060089 109550161983425310544545067)
          ·
            refine ⟨164325242975137965816817601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109550161983425310544545067 164325242975137965816817601)
            ·
              refine ⟨123243932231353474362613201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164325242975137965816817601 123243932231353474362613201)
              ·
                refine ⟨92432949173515105771959901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123243932231353474362613201 92432949173515105771959901)
                ·
                  refine ⟨34662355940068164664484963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92432949173515105771959901 34662355940068164664484963)
                  ·
                    refine ⟨51993533910102246996727445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34662355940068164664484963 51993533910102246996727445)
                    ·
                      refine ⟨2437196902036042827971599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51993533910102246996727445 2437196902036042827971599)
                      ·
                        rfl

theorem cell23_4746424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_4746424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746424 prefixEnd_4746424 := by exact prefixLift 4746424
  have htrace : WordTrace (prefixWord ++ tailWord_4746424) baseStart_4746424 baseEnd_4746424 := by
    simpa [prefixWord, tailWord_4746424, baseEnd_4746424] using wordTrace_append hprefix tailTrace_4746424
  have hstable : (prefixWord ++ tailWord_4746424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746424).length < 2 ^ (prefixWord ++ tailWord_4746424).sum := by decide
  have hdescent : baseEnd_4746424 < baseStart_4746424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746431 : List Nat := [1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 5]
def baseStart_4746431 : Nat := 118140960795 + 4746431 * 2 ^ 59
def prefixEnd_4746431 : Nat := 4983230072969 + 3 ^ 40 * 4746431 * 2
def baseEnd_4746431 : Nat := 2437200496400624300584067

theorem tailTrace_4746431 : CollatzResearch.WordTrace tailWord_4746431 prefixEnd_4746431 2437200496400624300584067 := by
  unfold tailWord_4746431
  simp only [CollatzResearch.WordTrace]
  refine ⟨173116560667498587722687147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115411040444999058481791431 173116560667498587722687147)
  ·
    refine ⟨259674841001247881584030721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173116560667498587722687147 259674841001247881584030721)
    ·
      refine ⟨194756130750935911188023041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259674841001247881584030721 194756130750935911188023041)
      ·
        refine ⟨146067098063201933391017281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194756130750935911188023041 146067098063201933391017281)
        ·
          refine ⟨109550323547401450043262961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146067098063201933391017281 109550323547401450043262961)
          ·
            refine ⟨82162742660551087532447221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109550323547401450043262961 82162742660551087532447221)
            ·
              refine ⟨7702757124426664456166927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82162742660551087532447221 7702757124426664456166927)
              ·
                refine ⟨11554135686639996684250391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7702757124426664456166927 11554135686639996684250391)
                ·
                  refine ⟨17331203529959995026375587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11554135686639996684250391 17331203529959995026375587)
                  ·
                    refine ⟨25996805294939992539563381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17331203529959995026375587 25996805294939992539563381)
                    ·
                      refine ⟨2437200496400624300584067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25996805294939992539563381 2437200496400624300584067)
                      ·
                        rfl

theorem cell23_4746431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 5].length) (baseStart_4746431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746431 prefixEnd_4746431 := by exact prefixLift 4746431
  have htrace : WordTrace (prefixWord ++ tailWord_4746431) baseStart_4746431 baseEnd_4746431 := by
    simpa [prefixWord, tailWord_4746431, baseEnd_4746431] using wordTrace_append hprefix tailTrace_4746431
  have hstable : (prefixWord ++ tailWord_4746431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746431).length < 2 ^ (prefixWord ++ tailWord_4746431).sum := by decide
  have hdescent : baseEnd_4746431 < baseStart_4746431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746478 : List Nat := [4, 1, 2, 1, 1, 1, 4, 2, 1, 3, 3]
def baseStart_4746478 : Nat := 118140960795 + 4746478 * 2 ^ 59
def prefixEnd_4746478 : Nat := 4983230072969 + 3 ^ 40 * 4746478 * 2
def baseEnd_4746478 : Nat := 2437224629991385616696351

theorem tailTrace_4746478 : CollatzResearch.WordTrace tailWord_4746478 prefixEnd_4746478 2437224629991385616696351 := by
  unfold tailWord_4746478
  simp only [CollatzResearch.WordTrace]
  refine ⟨21639784362291039343706011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115412183265552209833098725 21639784362291039343706011)
  ·
    refine ⟨32459676543436559015559017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21639784362291039343706011 32459676543436559015559017)
    ·
      refine ⟨24344757407577419261669263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32459676543436559015559017 24344757407577419261669263)
      ·
        refine ⟨36517136111366128892503895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24344757407577419261669263 36517136111366128892503895)
        ·
          refine ⟨54775704167049193338755843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36517136111366128892503895 54775704167049193338755843)
          ·
            refine ⟨82163556250573790008133765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54775704167049193338755843 82163556250573790008133765)
            ·
              refine ⟨15405666796982585626525081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82163556250573790008133765 15405666796982585626525081)
              ·
                refine ⟨11554250097736939219893811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15405666796982585626525081 11554250097736939219893811)
                ·
                  refine ⟨17331375146605408829840717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11554250097736939219893811 17331375146605408829840717)
                  ·
                    refine ⟨6499265679977028311190269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17331375146605408829840717 6499265679977028311190269)
                    ·
                      refine ⟨2437224629991385616696351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6499265679977028311190269 2437224629991385616696351)
                      ·
                        rfl

theorem cell23_4746478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_4746478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746478 prefixEnd_4746478 := by exact prefixLift 4746478
  have htrace : WordTrace (prefixWord ++ tailWord_4746478) baseStart_4746478 baseEnd_4746478 := by
    simpa [prefixWord, tailWord_4746478, baseEnd_4746478] using wordTrace_append hprefix tailTrace_4746478
  have hstable : (prefixWord ++ tailWord_4746478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746478).length < 2 ^ (prefixWord ++ tailWord_4746478).sum := by decide
  have hdescent : baseEnd_4746478 < baseStart_4746478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746479 : List Nat := [1, 1, 2, 1, 7, 1, 2, 3, 1, 2, 2]
def baseStart_4746479 : Nat := 118140960795 + 4746479 * 2 ^ 59
def prefixEnd_4746479 : Nat := 4983230072969 + 3 ^ 40 * 4746479 * 2
def baseEnd_4746479 : Nat := 2437225143472040112783847

theorem tailTrace_4746479 : CollatzResearch.WordTrace tailWord_4746479 prefixEnd_4746479 2437225143472040112783847 := by
  unfold tailWord_4746479
  simp only [CollatzResearch.WordTrace]
  refine ⟨173118311371324691920434491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115412207580883127946956327 173118311371324691920434491)
  ·
    refine ⟨259677467056987037880651737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173118311371324691920434491 259677467056987037880651737)
    ·
      refine ⟨194758100292740278410488803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259677467056987037880651737 194758100292740278410488803)
      ·
        refine ⟨292137150439110417615733205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194758100292740278410488803 292137150439110417615733205)
        ·
          refine ⟨6846964463416650412868747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 292137150439110417615733205 6846964463416650412868747)
          ·
            refine ⟨10270446695124975619303121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6846964463416650412868747 10270446695124975619303121)
            ·
              refine ⟨7702835021343731714477341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10270446695124975619303121 7702835021343731714477341)
              ·
                refine ⟨2888563133003899392929003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7702835021343731714477341 2888563133003899392929003)
                ·
                  refine ⟨4332844699505849089393505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2888563133003899392929003 4332844699505849089393505)
                  ·
                    refine ⟨3249633524629386817045129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4332844699505849089393505 3249633524629386817045129)
                    ·
                      refine ⟨2437225143472040112783847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3249633524629386817045129 2437225143472040112783847)
                      ·
                        rfl

theorem cell23_4746479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3, 1, 2, 2].length) (baseStart_4746479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746479 prefixEnd_4746479 := by exact prefixLift 4746479
  have htrace : WordTrace (prefixWord ++ tailWord_4746479) baseStart_4746479 baseEnd_4746479 := by
    simpa [prefixWord, tailWord_4746479, baseEnd_4746479] using wordTrace_append hprefix tailTrace_4746479
  have hstable : (prefixWord ++ tailWord_4746479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746479).length < 2 ^ (prefixWord ++ tailWord_4746479).sum := by decide
  have hdescent : baseEnd_4746479 < baseStart_4746479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746495 : List Nat := [1, 1, 2, 2, 1, 5, 3, 2, 2, 1, 3]
def baseStart_4746495 : Nat := 118140960795 + 4746495 * 2 ^ 59
def prefixEnd_4746495 : Nat := 4983230072969 + 3 ^ 40 * 4746495 * 2
def baseEnd_4746495 : Nat := 2437233359162512050183773

theorem tailTrace_4746495 : CollatzResearch.WordTrace tailWord_4746495 prefixEnd_4746495 2437233359162512050183773 := by
  unfold tailWord_4746495
  simp only [CollatzResearch.WordTrace]
  refine ⟨173118894939266726653016939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115412596626177817768677959 173118894939266726653016939)
  ·
    refine ⟨259678342408900089979525409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173118894939266726653016939 259678342408900089979525409)
    ·
      refine ⟨194758756806675067484644057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259678342408900089979525409 194758756806675067484644057)
      ·
        refine ⟨146069067605006300613483043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194758756806675067484644057 146069067605006300613483043)
        ·
          refine ⟨219103601407509450920224565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146069067605006300613483043 219103601407509450920224565)
          ·
            refine ⟨20540962631954011023771053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 219103601407509450920224565 20540962631954011023771053)
            ·
              refine ⟨7702860986982754133914145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20540962631954011023771053 7702860986982754133914145)
              ·
                refine ⟨5777145740237065600435609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7702860986982754133914145 5777145740237065600435609)
                ·
                  refine ⟨4332859305177799200326707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5777145740237065600435609 4332859305177799200326707)
                  ·
                    refine ⟨6499288957766698800490061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4332859305177799200326707 6499288957766698800490061)
                    ·
                      refine ⟨2437233359162512050183773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6499288957766698800490061 2437233359162512050183773)
                      ·
                        rfl

theorem cell23_4746495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2, 1, 3].length) (baseStart_4746495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746495 prefixEnd_4746495 := by exact prefixLift 4746495
  have htrace : WordTrace (prefixWord ++ tailWord_4746495) baseStart_4746495 baseEnd_4746495 := by
    simpa [prefixWord, tailWord_4746495, baseEnd_4746495] using wordTrace_append hprefix tailTrace_4746495
  have hstable : (prefixWord ++ tailWord_4746495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746495).length < 2 ^ (prefixWord ++ tailWord_4746495).sum := by decide
  have hdescent : baseEnd_4746495 < baseStart_4746495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746522 : List Nat := [3, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2]
def baseStart_4746522 : Nat := 118140960795 + 4746522 * 2 ^ 59
def prefixEnd_4746522 : Nat := 4983230072969 + 3 ^ 40 * 4746522 * 2
def baseEnd_4746522 : Nat := 2437247223140183444546149

theorem tailTrace_4746522 : CollatzResearch.WordTrace tailWord_4746522 prefixEnd_4746522 2437247223140183444546149 := by
  unfold tailWord_4746522
  simp only [CollatzResearch.WordTrace]
  refine ⟨43279969927542227566062455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115413253140112606842833213 43279969927542227566062455)
  ·
    refine ⟨64919954891313341349093683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43279969927542227566062455 64919954891313341349093683)
    ·
      refine ⟨97379932336970012023640525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64919954891313341349093683 97379932336970012023640525)
      ·
        refine ⟨36517474626363754508865197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97379932336970012023640525 36517474626363754508865197)
        ·
          refine ⟨13694052984886407940824449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36517474626363754508865197 13694052984886407940824449)
          ·
            refine ⟨10270539738664805955618337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13694052984886407940824449 10270539738664805955618337)
            ·
              refine ⟨7702904803998604466713753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10270539738664805955618337 7702904803998604466713753)
              ·
                refine ⟨5777178602998953350035315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7702904803998604466713753 5777178602998953350035315)
                ·
                  refine ⟨8665767904498430025052973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5777178602998953350035315 8665767904498430025052973)
                  ·
                    refine ⟨3249662964186911259394865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8665767904498430025052973 3249662964186911259394865)
                    ·
                      refine ⟨2437247223140183444546149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3249662964186911259394865 2437247223140183444546149)
                      ·
                        rfl

theorem cell23_4746522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_4746522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746522 prefixEnd_4746522 := by exact prefixLift 4746522
  have htrace : WordTrace (prefixWord ++ tailWord_4746522) baseStart_4746522 baseEnd_4746522 := by
    simpa [prefixWord, tailWord_4746522, baseEnd_4746522] using wordTrace_append hprefix tailTrace_4746522
  have hstable : (prefixWord ++ tailWord_4746522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746522).length < 2 ^ (prefixWord ++ tailWord_4746522).sum := by decide
  have hdescent : baseEnd_4746522 < baseStart_4746522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746538 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_4746538 : Nat := 118140960795 + 4746538 * 2 ^ 59
def prefixEnd_4746538 : Nat := 4983230072969 + 3 ^ 40 * 4746538 * 2
def baseEnd_4746538 : Nat := 2437255438830655381946075

theorem tailTrace_4746538 : CollatzResearch.WordTrace tailWord_4746538 prefixEnd_4746538 2437255438830655381946075 := by
  unfold tailWord_4746538
  simp only [CollatzResearch.WordTrace]
  refine ⟨43280115819527736249208067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115413642185407296664554845 43280115819527736249208067)
  ·
    refine ⟨64920173729291604373812101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43280115819527736249208067 64920173729291604373812101)
    ·
      refine ⟨12172532574242175820089769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64920173729291604373812101 12172532574242175820089769)
      ·
        refine ⟨9129399430681631865067327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12172532574242175820089769 9129399430681631865067327)
        ·
          refine ⟨13694099146022447797600991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9129399430681631865067327 13694099146022447797600991)
          ·
            refine ⟨20541148719033671696401487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13694099146022447797600991 20541148719033671696401487)
            ·
              refine ⟨30811723078550507544602231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20541148719033671696401487 30811723078550507544602231)
              ·
                refine ⟨46217584617825761316903347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30811723078550507544602231 46217584617825761316903347)
                ·
                  refine ⟨69326376926738641975355021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46217584617825761316903347 69326376926738641975355021)
                  ·
                    refine ⟨25997391347526990740758133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69326376926738641975355021 25997391347526990740758133)
                    ·
                      refine ⟨2437255438830655381946075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25997391347526990740758133 2437255438830655381946075)
                      ·
                        rfl

theorem cell23_4746538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_4746538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746538 prefixEnd_4746538 := by exact prefixLift 4746538
  have htrace : WordTrace (prefixWord ++ tailWord_4746538) baseStart_4746538 baseEnd_4746538 := by
    simpa [prefixWord, tailWord_4746538, baseEnd_4746538] using wordTrace_append hprefix tailTrace_4746538
  have hstable : (prefixWord ++ tailWord_4746538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746538).length < 2 ^ (prefixWord ++ tailWord_4746538).sum := by decide
  have hdescent : baseEnd_4746538 < baseStart_4746538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746573 : List Nat := [1, 6, 1, 3, 2, 1, 1, 2, 1, 3, 2]
def baseStart_4746573 : Nat := 118140960795 + 4746573 * 2 ^ 59
def prefixEnd_4746573 : Nat := 4983230072969 + 3 ^ 40 * 4746573 * 2
def baseEnd_4746573 : Nat := 2437273410653562745008415

theorem tailTrace_4746573 : CollatzResearch.WordTrace tailWord_4746573 prefixEnd_4746573 2437273410653562745008415 := by
  unfold tailWord_4746573
  simp only [CollatzResearch.WordTrace]
  refine ⟨173121739832984145974356373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115414493221989430649570915 173121739832984145974356373)
  ·
    refine ⟨8115081554671131842547955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 173121739832984145974356373 8115081554671131842547955)
    ·
      refine ⟨12172622332006697763821933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8115081554671131842547955 12172622332006697763821933)
      ·
        refine ⟨4564733374502511661433225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12172622332006697763821933 4564733374502511661433225)
        ·
          refine ⟨3423550030876883746074919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4564733374502511661433225 3423550030876883746074919)
          ·
            refine ⟨5135325046315325619112379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3423550030876883746074919 5135325046315325619112379)
            ·
              refine ⟨7702987569472988428668569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5135325046315325619112379 7702987569472988428668569)
              ·
                refine ⟨5777240677104741321501427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7702987569472988428668569 5777240677104741321501427)
                ·
                  refine ⟨8665861015657111982252141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5777240677104741321501427 8665861015657111982252141)
                  ·
                    refine ⟨3249697880871416993344553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8665861015657111982252141 3249697880871416993344553)
                    ·
                      refine ⟨2437273410653562745008415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3249697880871416993344553 2437273410653562745008415)
                      ·
                        rfl

theorem cell23_4746573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_4746573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746573 prefixEnd_4746573 := by exact prefixLift 4746573
  have htrace : WordTrace (prefixWord ++ tailWord_4746573) baseStart_4746573 baseEnd_4746573 := by
    simpa [prefixWord, tailWord_4746573, baseEnd_4746573] using wordTrace_append hprefix tailTrace_4746573
  have hstable : (prefixWord ++ tailWord_4746573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746573).length < 2 ^ (prefixWord ++ tailWord_4746573).sum := by decide
  have hdescent : baseEnd_4746573 < baseStart_4746573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746608 : List Nat := [2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 4]
def baseStart_4746608 : Nat := 118140960795 + 4746608 * 2 ^ 59
def prefixEnd_4746608 : Nat := 4983230072969 + 3 ^ 40 * 4746608 * 2
def baseEnd_4746608 : Nat := 2437291382476470108070753

theorem tailTrace_4746608 : CollatzResearch.WordTrace tailWord_4746608 prefixEnd_4746608 2437291382476470108070753 := by
  unfold tailWord_4746608
  simp only [CollatzResearch.WordTrace]
  refine ⟨86561508193928673475940239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115415344258571564634586985 86561508193928673475940239)
  ·
    refine ⟨129842262290893010213910359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86561508193928673475940239 129842262290893010213910359)
    ·
      refine ⟨194763393436339515320865539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129842262290893010213910359 194763393436339515320865539)
      ·
        refine ⟨292145090154509272981298309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194763393436339515320865539 292145090154509272981298309)
        ·
          refine ⟨54777204403970488683993433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 292145090154509272981298309 54777204403970488683993433)
          ·
            refine ⟨41082903302977866512995075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54777204403970488683993433 41082903302977866512995075)
            ·
              refine ⟨61624354954466799769492613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41082903302977866512995075 61624354954466799769492613)
              ·
                refine ⟨11554566553962524956779865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61624354954466799769492613 11554566553962524956779865)
                ·
                  refine ⟨8665924915471893717584899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11554566553962524956779865 8665924915471893717584899)
                  ·
                    refine ⟨12998887373207840576377349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8665924915471893717584899 12998887373207840576377349)
                    ·
                      refine ⟨2437291382476470108070753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12998887373207840576377349 2437291382476470108070753)
                      ·
                        rfl

theorem cell23_4746608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 4].length) (baseStart_4746608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746608 prefixEnd_4746608 := by exact prefixLift 4746608
  have htrace : WordTrace (prefixWord ++ tailWord_4746608) baseStart_4746608 baseEnd_4746608 := by
    simpa [prefixWord, tailWord_4746608, baseEnd_4746608] using wordTrace_append hprefix tailTrace_4746608
  have hstable : (prefixWord ++ tailWord_4746608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746608).length < 2 ^ (prefixWord ++ tailWord_4746608).sum := by decide
  have hdescent : baseEnd_4746608 < baseStart_4746608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746642 : List Nat := [3, 2, 3, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_4746642 : Nat := 118140960795 + 4746642 * 2 ^ 59
def prefixEnd_4746642 : Nat := 4983230072969 + 3 ^ 40 * 4746642 * 2
def baseEnd_4746642 : Nat := 2437308840818722975045597

theorem tailTrace_4746642 : CollatzResearch.WordTrace tailWord_4746642 prefixEnd_4746642 2437308840818722975045597 := by
  unfold tailWord_4746642
  simp only [CollatzResearch.WordTrace]
  refine ⟨43281064117433542689654545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115416170979822780505745453 43281064117433542689654545)
  ·
    refine ⟨32460798088075157017240909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43281064117433542689654545 32460798088075157017240909)
    ·
      refine ⟨12172799283028183881465341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32460798088075157017240909 12172799283028183881465341)
      ·
        refine ⟨4564799731135568955549503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12172799283028183881465341 4564799731135568955549503)
        ·
          refine ⟨6847199596703353433324255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4564799731135568955549503 6847199596703353433324255)
          ·
            refine ⟨10270799395055030149986383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6847199596703353433324255 10270799395055030149986383)
            ·
              refine ⟨15406199092582545224979575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10270799395055030149986383 15406199092582545224979575)
              ·
                refine ⟨23109298638873817837469363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15406199092582545224979575 23109298638873817837469363)
                ·
                  refine ⟨34663947958310726756204045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23109298638873817837469363 34663947958310726756204045)
                  ·
                    refine ⟨12998980484366522533576517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34663947958310726756204045 12998980484366522533576517)
                    ·
                      refine ⟨2437308840818722975045597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12998980484366522533576517 2437308840818722975045597)
                      ·
                        rfl

theorem cell23_4746642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_4746642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746642 prefixEnd_4746642 := by exact prefixLift 4746642
  have htrace : WordTrace (prefixWord ++ tailWord_4746642) baseStart_4746642 baseEnd_4746642 := by
    simpa [prefixWord, tailWord_4746642, baseEnd_4746642] using wordTrace_append hprefix tailTrace_4746642
  have hstable : (prefixWord ++ tailWord_4746642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746642).length < 2 ^ (prefixWord ++ tailWord_4746642).sum := by decide
  have hdescent : baseEnd_4746642 < baseStart_4746642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746645 : List Nat := [1, 3, 2, 1, 1, 2, 5, 1, 2, 2, 3]
def baseStart_4746645 : Nat := 118140960795 + 4746645 * 2 ^ 59
def prefixEnd_4746645 : Nat := 4983230072969 + 3 ^ 40 * 4746645 * 2
def baseEnd_4746645 : Nat := 2437310381260686463308083

theorem tailTrace_4746645 : CollatzResearch.WordTrace tailWord_4746645 prefixEnd_4746645 2437310381260686463308083 := by
  unfold tailWord_4746645
  simp only [CollatzResearch.WordTrace]
  refine ⟨173124365888723302270977389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115416243925815534847318259 173124365888723302270977389)
  ·
    refine ⟨64921637208271238351616521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173124365888723302270977389 64921637208271238351616521)
    ·
      refine ⟨48691227906203428763712391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64921637208271238351616521 48691227906203428763712391)
      ·
        refine ⟨73036841859305143145568587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48691227906203428763712391 73036841859305143145568587)
        ·
          refine ⟨109555262788957714718352881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73036841859305143145568587 109555262788957714718352881)
          ·
            refine ⟨82166447091718286038764661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109555262788957714718352881 82166447091718286038764661)
            ·
              refine ⟨7703104414848589316134187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82166447091718286038764661 7703104414848589316134187)
              ·
                refine ⟨11554656622272883974201281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7703104414848589316134187 11554656622272883974201281)
                ·
                  refine ⟨8665992466704662980650961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11554656622272883974201281 8665992466704662980650961)
                  ·
                    refine ⟨6499494350028497235488221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8665992466704662980650961 6499494350028497235488221)
                    ·
                      refine ⟨2437310381260686463308083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6499494350028497235488221 2437310381260686463308083)
                      ·
                        rfl

theorem cell23_4746645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_4746645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746645 prefixEnd_4746645 := by exact prefixLift 4746645
  have htrace : WordTrace (prefixWord ++ tailWord_4746645) baseStart_4746645 baseEnd_4746645 := by
    simpa [prefixWord, tailWord_4746645, baseEnd_4746645] using wordTrace_append hprefix tailTrace_4746645
  have hstable : (prefixWord ++ tailWord_4746645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746645).length < 2 ^ (prefixWord ++ tailWord_4746645).sum := by decide
  have hdescent : baseEnd_4746645 < baseStart_4746645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746669 : List Nat := [1, 5, 2, 2, 1, 1, 2, 4, 1, 4]
def baseStart_4746669 : Nat := 118140960795 + 4746669 * 2 ^ 59
def prefixEnd_4746669 : Nat := 4983230072969 + 3 ^ 40 * 4746669 * 2
def baseEnd_4746669 : Nat := 812440901598798123135991

theorem tailTrace_4746669 : CollatzResearch.WordTrace tailWord_4746669 prefixEnd_4746669 812440901598798123135991 := by
  unfold tailWord_4746669
  simp only [CollatzResearch.WordTrace]
  refine ⟨173125241240636354369851061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115416827493757569579900707 173125241240636354369851061)
  ·
    refine ⟨16230491366309658222173537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 173125241240636354369851061 16230491366309658222173537)
    ·
      refine ⟨12172868524732243666630153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16230491366309658222173537 12172868524732243666630153)
      ·
        refine ⟨9129651393549182749972615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12172868524732243666630153 9129651393549182749972615)
        ·
          refine ⟨13694477090323774124958923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9129651393549182749972615 13694477090323774124958923)
          ·
            refine ⟨20541715635485661187438385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13694477090323774124958923 20541715635485661187438385)
            ·
              refine ⟨15406286726614245890578789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20541715635485661187438385 15406286726614245890578789)
              ·
                refine ⟨2888678761240171104483523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15406286726614245890578789 2888678761240171104483523)
                ·
                  refine ⟨4333018141860256656725285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2888678761240171104483523 4333018141860256656725285)
                  ·
                    refine ⟨812440901598798123135991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4333018141860256656725285 812440901598798123135991)
                    ·
                      rfl

theorem cell23_4746669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_4746669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746669 prefixEnd_4746669 := by exact prefixLift 4746669
  have htrace : WordTrace (prefixWord ++ tailWord_4746669) baseStart_4746669 baseEnd_4746669 := by
    simpa [prefixWord, tailWord_4746669, baseEnd_4746669] using wordTrace_append hprefix tailTrace_4746669
  have hstable : (prefixWord ++ tailWord_4746669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746669).length < 2 ^ (prefixWord ++ tailWord_4746669).sum := by decide
  have hdescent : baseEnd_4746669 < baseStart_4746669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746685 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 3, 5, 2]
def baseStart_4746685 : Nat := 118140960795 + 4746685 * 2 ^ 59
def prefixEnd_4746685 : Nat := 4983230072969 + 3 ^ 40 * 4746685 * 2
def baseEnd_4746685 : Nat := 2437330920486866306807899

theorem tailTrace_4746685 : CollatzResearch.WordTrace tailWord_4746685 prefixEnd_4746685 2437330920486866306807899 := by
  unfold tailWord_4746685
  simp only [CollatzResearch.WordTrace]
  refine ⟨173125824808578389102433509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115417216539052259401622339 173125824808578389102433509)
  ·
    refine ⟨32461092151608447956706283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173125824808578389102433509 32461092151608447956706283)
    ·
      refine ⟨48691638227412671935059425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32461092151608447956706283 48691638227412671935059425)
      ·
        refine ⟨36518728670559503951294569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48691638227412671935059425 36518728670559503951294569)
        ·
          refine ⟨27389046502919627963470927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36518728670559503951294569 27389046502919627963470927)
          ·
            refine ⟨41083569754379441945206391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27389046502919627963470927 41083569754379441945206391)
            ·
              refine ⟨61625354631569162917809587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41083569754379441945206391 61625354631569162917809587)
              ·
                refine ⟨92438031947353744376714381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61625354631569162917809587 92438031947353744376714381)
                ·
                  refine ⟨34664261980257654141267893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92438031947353744376714381 34664261980257654141267893)
                  ·
                    refine ⟨3249774560649155075743865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34664261980257654141267893 3249774560649155075743865)
                    ·
                      refine ⟨2437330920486866306807899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3249774560649155075743865 2437330920486866306807899)
                      ·
                        rfl

theorem cell23_4746685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_4746685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746685 prefixEnd_4746685 := by exact prefixLift 4746685
  have htrace : WordTrace (prefixWord ++ tailWord_4746685) baseStart_4746685 baseEnd_4746685 := by
    simpa [prefixWord, tailWord_4746685, baseEnd_4746685] using wordTrace_append hprefix tailTrace_4746685
  have hstable : (prefixWord ++ tailWord_4746685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746685).length < 2 ^ (prefixWord ++ tailWord_4746685).sum := by decide
  have hdescent : baseEnd_4746685 < baseStart_4746685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746695 : List Nat := [1, 1, 4, 1, 1, 3, 4, 2, 1, 5]
def baseStart_4746695 : Nat := 118140960795 + 4746695 * 2 ^ 59
def prefixEnd_4746695 : Nat := 4983230072969 + 3 ^ 40 * 4746695 * 2
def baseEnd_4746695 : Nat := 812445351764470422560951

theorem tailTrace_4746695 : CollatzResearch.WordTrace tailWord_4746695 prefixEnd_4746695 812445351764470422560951 := by
  unfold tailWord_4746695
  simp only [CollatzResearch.WordTrace]
  refine ⟨173126189538542160810297539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115417459692361440540198359 173126189538542160810297539)
  ·
    refine ⟨259689284307813241215446309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173126189538542160810297539 259689284307813241215446309)
    ·
      refine ⟨48691740807714982727896183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 259689284307813241215446309 48691740807714982727896183)
      ·
        refine ⟨73037611211572474091844275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48691740807714982727896183 73037611211572474091844275)
        ·
          refine ⟨109556416817358711137766413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73037611211572474091844275 109556416817358711137766413)
          ·
            refine ⟨41083656306509516676662405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109556416817358711137766413 41083656306509516676662405)
            ·
              refine ⟨7703185557470534376874201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41083656306509516676662405 7703185557470534376874201)
              ·
                refine ⟨5777389168102900782655651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7703185557470534376874201 5777389168102900782655651)
                ·
                  refine ⟨8666083752154351173983477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5777389168102900782655651 8666083752154351173983477)
                  ·
                    refine ⟨812445351764470422560951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8666083752154351173983477 812445351764470422560951)
                    ·
                      rfl

theorem cell23_4746695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_4746695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746695 prefixEnd_4746695 := by exact prefixLift 4746695
  have htrace : WordTrace (prefixWord ++ tailWord_4746695) baseStart_4746695 baseEnd_4746695 := by
    simpa [prefixWord, tailWord_4746695, baseEnd_4746695] using wordTrace_append hprefix tailTrace_4746695
  have hstable : (prefixWord ++ tailWord_4746695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746695).length < 2 ^ (prefixWord ++ tailWord_4746695).sum := by decide
  have hdescent : baseEnd_4746695 < baseStart_4746695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746728 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_4746728 : Nat := 118140960795 + 4746728 * 2 ^ 59
def prefixEnd_4746728 : Nat := 4983230072969 + 3 ^ 40 * 4746728 * 2
def baseEnd_4746728 : Nat := 2437353000155009638570201

theorem tailTrace_4746728 : CollatzResearch.WordTrace tailWord_4746728 prefixEnd_4746728 2437353000155009638570201 := by
  unfold tailWord_4746728
  simp only [CollatzResearch.WordTrace]
  refine ⟨86563696573711303723124419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115418262098281738297499225 86563696573711303723124419)
  ·
    refine ⟨129845544860566955584686629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86563696573711303723124419 129845544860566955584686629)
    ·
      refine ⟨24346039661356304172128743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129845544860566955584686629 24346039661356304172128743)
      ·
        refine ⟨36519059492034456258193115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24346039661356304172128743 36519059492034456258193115)
        ·
          refine ⟨54778589238051684387289673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36519059492034456258193115 54778589238051684387289673)
          ·
            refine ⟨41083941928538763290467255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54778589238051684387289673 41083941928538763290467255)
            ·
              refine ⟨61625912892808144935700883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41083941928538763290467255 61625912892808144935700883)
              ·
                refine ⟨92438869339212217403551325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61625912892808144935700883 92438869339212217403551325)
                ·
                  refine ⟨34664576002204581526331747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92438869339212217403551325 34664576002204581526331747)
                  ·
                    refine ⟨51996864003306872289497621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34664576002204581526331747 51996864003306872289497621)
                    ·
                      refine ⟨2437353000155009638570201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51996864003306872289497621 2437353000155009638570201)
                      ·
                        rfl

theorem cell23_4746728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_4746728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746728 prefixEnd_4746728 := by exact prefixLift 4746728
  have htrace : WordTrace (prefixWord ++ tailWord_4746728) baseStart_4746728 baseEnd_4746728 := by
    simpa [prefixWord, tailWord_4746728, baseEnd_4746728] using wordTrace_append hprefix tailTrace_4746728
  have hstable : (prefixWord ++ tailWord_4746728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746728).length < 2 ^ (prefixWord ++ tailWord_4746728).sum := by decide
  have hdescent : baseEnd_4746728 < baseStart_4746728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746732 : List Nat := [2, 2, 1, 1, 2, 1, 2, 5, 3, 2, 2]
def baseStart_4746732 : Nat := 118140960795 + 4746732 * 2 ^ 59
def prefixEnd_4746732 : Nat := 4983230072969 + 3 ^ 40 * 4746732 * 2
def baseEnd_4746732 : Nat := 2437355054077627622920183

theorem tailTrace_4746732 : CollatzResearch.WordTrace tailWord_4746732 prefixEnd_4746732 2437355054077627622920183 := by
  unfold tailWord_4746732
  simp only [CollatzResearch.WordTrace]
  refine ⟨86563769519704058064697225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115418359359605410752929633 86563769519704058064697225)
  ·
    refine ⟨64922827139778043548522919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86563769519704058064697225 64922827139778043548522919)
    ·
      refine ⟨97384240709667065322784379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64922827139778043548522919 97384240709667065322784379)
      ·
        refine ⟨146076361064500597984176569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97384240709667065322784379 146076361064500597984176569)
        ·
          refine ⟨109557270798375448488132427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146076361064500597984176569 109557270798375448488132427)
          ·
            refine ⟨164335906197563172732198641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109557270798375448488132427 164335906197563172732198641)
            ·
              refine ⟨123251929648172379549148981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164335906197563172732198641 123251929648172379549148981)
              ·
                refine ⟨11554868404516160582732717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 123251929648172379549148981 11554868404516160582732717)
                ·
                  refine ⟨4333075651693560218524769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11554868404516160582732717 4333075651693560218524769)
                  ·
                    refine ⟨3249806738770170163893577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4333075651693560218524769 3249806738770170163893577)
                    ·
                      refine ⟨2437355054077627622920183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3249806738770170163893577 2437355054077627622920183)
                      ·
                        rfl

theorem cell23_4746732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 2, 2].length) (baseStart_4746732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746732 prefixEnd_4746732 := by exact prefixLift 4746732
  have htrace : WordTrace (prefixWord ++ tailWord_4746732) baseStart_4746732 baseEnd_4746732 := by
    simpa [prefixWord, tailWord_4746732, baseEnd_4746732] using wordTrace_append hprefix tailTrace_4746732
  have hstable : (prefixWord ++ tailWord_4746732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746732).length < 2 ^ (prefixWord ++ tailWord_4746732).sum := by decide
  have hdescent : baseEnd_4746732 < baseStart_4746732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746772 : List Nat := [2, 4, 3, 1, 3, 10]
def baseStart_4746772 : Nat := 118140960795 + 4746772 * 2 ^ 59
def prefixEnd_4746772 : Nat := 4983230072969 + 3 ^ 40 * 4746772 * 2
def baseEnd_4746772 : Nat := 10030352235818137721893

theorem tailTrace_4746772 : CollatzResearch.WordTrace tailWord_4746772 prefixEnd_4746772 10030352235818137721893 := by
  unfold tailWord_4746772
  simp only [CollatzResearch.WordTrace]
  refine ⟨86564498979631601480425285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115419331972842135307233713 86564498979631601480425285)
  ·
    refine ⟨16230843558680925277579741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86564498979631601480425285 16230843558680925277579741)
    ·
      refine ⟨6086566334505346979092403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16230843558680925277579741 6086566334505346979092403)
      ·
        refine ⟨9129849501758020468638605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6086566334505346979092403 9129849501758020468638605)
        ·
          refine ⟨3423693563159257675739477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9129849501758020468638605 3423693563159257675739477)
          ·
            refine ⟨10030352235818137721893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3423693563159257675739477 10030352235818137721893)
            ·
              rfl

theorem cell23_4746772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 10].length) (baseStart_4746772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746772 prefixEnd_4746772 := by exact prefixLift 4746772
  have htrace : WordTrace (prefixWord ++ tailWord_4746772) baseStart_4746772 baseEnd_4746772 := by
    simpa [prefixWord, tailWord_4746772, baseEnd_4746772] using wordTrace_append hprefix tailTrace_4746772
  have hstable : (prefixWord ++ tailWord_4746772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746772).length < 2 ^ (prefixWord ++ tailWord_4746772).sum := by decide
  have hdescent : baseEnd_4746772 < baseStart_4746772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746839 : List Nat := [1, 1, 3, 2, 2, 4, 1, 1, 4, 2, 2]
def baseStart_4746839 : Nat := 118140960795 + 4746839 * 2 ^ 59
def prefixEnd_4746839 : Nat := 4983230072969 + 3 ^ 40 * 4746839 * 2
def baseEnd_4746839 : Nat := 2437409996507658704282191

theorem tailTrace_4746839 : CollatzResearch.WordTrace tailWord_4746839 prefixEnd_4746839 2437409996507658704282191 := by
  unfold tailWord_4746839
  simp only [CollatzResearch.WordTrace]
  refine ⟨173131441650020473403539571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115420961100013648935693047 173131441650020473403539571)
  ·
    refine ⟨259697162475030710105309357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173131441650020473403539571 259697162475030710105309357)
    ·
      refine ⟨97386435928136516289491009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 259697162475030710105309357 97386435928136516289491009)
      ·
        refine ⟨73039826946102387217118257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97386435928136516289491009 73039826946102387217118257)
        ·
          refine ⟨54779870209576790412838693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73039826946102387217118257 54779870209576790412838693)
          ·
            refine ⟨10271225664295648202407255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54779870209576790412838693 10271225664295648202407255)
            ·
              refine ⟨15406838496443472303610883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10271225664295648202407255 15406838496443472303610883)
              ·
                refine ⟨23110257744665208455416325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15406838496443472303610883 23110257744665208455416325)
                ·
                  refine ⟨4333173327124726585390561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23110257744665208455416325 4333173327124726585390561)
                  ·
                    refine ⟨3249879995343544939042921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4333173327124726585390561 3249879995343544939042921)
                    ·
                      refine ⟨2437409996507658704282191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3249879995343544939042921 2437409996507658704282191)
                      ·
                        rfl

theorem cell23_4746839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4, 2, 2].length) (baseStart_4746839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746839 prefixEnd_4746839 := by exact prefixLift 4746839
  have htrace : WordTrace (prefixWord ++ tailWord_4746839) baseStart_4746839 baseEnd_4746839 := by
    simpa [prefixWord, tailWord_4746839, baseEnd_4746839] using wordTrace_append hprefix tailTrace_4746839
  have hstable : (prefixWord ++ tailWord_4746839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746839).length < 2 ^ (prefixWord ++ tailWord_4746839).sum := by decide
  have hdescent : baseEnd_4746839 < baseStart_4746839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746856 : List Nat := [2, 1, 4, 3, 1, 3, 1, 1, 1, 4, 2]
def baseStart_4746856 : Nat := 118140960795 + 4746856 * 2 ^ 59
def prefixEnd_4746856 : Nat := 4983230072969 + 3 ^ 40 * 4746856 * 2
def baseEnd_4746856 : Nat := 2437418725678785137769613

theorem tailTrace_4746856 : CollatzResearch.WordTrace tailWord_4746856 prefixEnd_4746856 2437418725678785137769613 := by
  unfold tailWord_4746856
  simp only [CollatzResearch.WordTrace]
  refine ⟨86566030845479442653454211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115421374460639256871272281 86566030845479442653454211)
  ·
    refine ⟨129849046268219163980181317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86566030845479442653454211 129849046268219163980181317)
    ·
      refine ⟨24346696175291093246283997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129849046268219163980181317 24346696175291093246283997)
      ·
        refine ⟨9130011065734159967356499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24346696175291093246283997 9130011065734159967356499)
        ·
          refine ⟨13695016598601239951034749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9130011065734159967356499 13695016598601239951034749)
          ·
            refine ⟨5135631224475464981638031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13695016598601239951034749 5135631224475464981638031)
            ·
              refine ⟨7703446836713197472457047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5135631224475464981638031 7703446836713197472457047)
              ·
                refine ⟨11555170255069796208685571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7703446836713197472457047 11555170255069796208685571)
                ·
                  refine ⟨17332755382604694313028357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11555170255069796208685571 17332755382604694313028357)
                  ·
                    refine ⟨3249891634238380183692817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17332755382604694313028357 3249891634238380183692817)
                    ·
                      refine ⟨2437418725678785137769613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3249891634238380183692817 2437418725678785137769613)
                      ·
                        rfl

theorem cell23_4746856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_4746856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746856 prefixEnd_4746856 := by exact prefixLift 4746856
  have htrace : WordTrace (prefixWord ++ tailWord_4746856) baseStart_4746856 baseEnd_4746856 := by
    simpa [prefixWord, tailWord_4746856, baseEnd_4746856] using wordTrace_append hprefix tailTrace_4746856
  have hstable : (prefixWord ++ tailWord_4746856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746856).length < 2 ^ (prefixWord ++ tailWord_4746856).sum := by decide
  have hdescent : baseEnd_4746856 < baseStart_4746856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746875 : List Nat := [1, 1, 1, 1, 1, 4, 4, 3, 2, 5]
def baseStart_4746875 : Nat := 118140960795 + 4746875 * 2 ^ 59
def prefixEnd_4746875 : Nat := 4983230072969 + 3 ^ 40 * 4746875 * 2
def baseEnd_4746875 : Nat := 812476160603740187810675

theorem tailTrace_4746875 : CollatzResearch.WordTrace tailWord_4746875 prefixEnd_4746875 812476160603740187810675 := by
  unfold tailWord_4746875
  simp only [CollatzResearch.WordTrace]
  refine ⟨173132754677890051551850079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115421836451926701034566719 173132754677890051551850079)
  ·
    refine ⟨259699132016835077327775119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173132754677890051551850079 259699132016835077327775119)
    ·
      refine ⟨389548698025252615991662679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259699132016835077327775119 389548698025252615991662679)
      ·
        refine ⟨584323047037878923987494019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389548698025252615991662679 584323047037878923987494019)
        ·
          refine ⟨876484570556818385981241029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 584323047037878923987494019 876484570556818385981241029)
          ·
            refine ⟨164340856979403447371482693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 876484570556818385981241029 164340856979403447371482693)
            ·
              refine ⟨30813910683638146382153005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 164340856979403447371482693 30813910683638146382153005)
              ·
                refine ⟨11555216506364304893307377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30813910683638146382153005 11555216506364304893307377)
                ·
                  refine ⟨8666412379773228669980533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11555216506364304893307377 8666412379773228669980533)
                  ·
                    refine ⟨812476160603740187810675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8666412379773228669980533 812476160603740187810675)
                    ·
                      rfl

theorem cell23_4746875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 5].length) (baseStart_4746875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746875 prefixEnd_4746875 := by exact prefixLift 4746875
  have htrace : WordTrace (prefixWord ++ tailWord_4746875) baseStart_4746875 baseEnd_4746875 := by
    simpa [prefixWord, tailWord_4746875, baseEnd_4746875] using wordTrace_append hprefix tailTrace_4746875
  have hstable : (prefixWord ++ tailWord_4746875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746875).length < 2 ^ (prefixWord ++ tailWord_4746875).sum := by decide
  have hdescent : baseEnd_4746875 < baseStart_4746875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746885 : List Nat := [1, 3, 1, 1, 4, 1, 2, 2, 1, 2, 5]
def baseStart_4746885 : Nat := 118140960795 + 4746885 * 2 ^ 59
def prefixEnd_4746885 : Nat := 4983230072969 + 3 ^ 40 * 4746885 * 2
def baseEnd_4746885 : Nat := 2437433616617765524306979

theorem tailTrace_4746885 : CollatzResearch.WordTrace tailWord_4746885 prefixEnd_4746885 2437433616617765524306979 := by
  unfold tailWord_4746885
  simp only [CollatzResearch.WordTrace]
  refine ⟨173133119407853823259714109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115422079605235882173142739 173133119407853823259714109)
  ·
    refine ⟨64924919777945183722392791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173133119407853823259714109 64924919777945183722392791)
    ·
      refine ⟨97387379666917775583589187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64924919777945183722392791 97387379666917775583589187)
      ·
        refine ⟨146081069500376663375383781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97387379666917775583589187 146081069500376663375383781)
        ·
          refine ⟨27390200531320624382884459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146081069500376663375383781 27390200531320624382884459)
          ·
            refine ⟨41085300796980936574326689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27390200531320624382884459 41085300796980936574326689)
            ·
              refine ⟨30813975597735702430745017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41085300796980936574326689 30813975597735702430745017)
              ·
                refine ⟨23110481698301776823058763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30813975597735702430745017 23110481698301776823058763)
                ·
                  refine ⟨34665722547452665234588145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23110481698301776823058763 34665722547452665234588145)
                  ·
                    refine ⟨25999291910589498925941109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34665722547452665234588145 25999291910589498925941109)
                    ·
                      refine ⟨2437433616617765524306979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25999291910589498925941109 2437433616617765524306979)
                      ·
                        rfl

theorem cell23_4746885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_4746885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746885 prefixEnd_4746885 := by exact prefixLift 4746885
  have htrace : WordTrace (prefixWord ++ tailWord_4746885) baseStart_4746885 baseEnd_4746885 := by
    simpa [prefixWord, tailWord_4746885, baseEnd_4746885] using wordTrace_append hprefix tailTrace_4746885
  have hstable : (prefixWord ++ tailWord_4746885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746885).length < 2 ^ (prefixWord ++ tailWord_4746885).sum := by decide
  have hdescent : baseEnd_4746885 < baseStart_4746885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746926 : List Nat := [4, 1, 4, 1, 2, 1, 2, 1, 2, 5]
def baseStart_4746926 : Nat := 118140960795 + 4746926 * 2 ^ 59
def prefixEnd_4746926 : Nat := 4983230072969 + 3 ^ 40 * 4746926 * 2
def baseEnd_4746926 : Nat := 812484889774866621298097

theorem tailTrace_4746926 : CollatzResearch.WordTrace tailWord_4746926 prefixEnd_4746926 812484889774866621298097 := by
  unfold tailWord_4746926
  simp only [CollatzResearch.WordTrace]
  refine ⟨21641826850088160907744579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115423076533803524841304421 21641826850088160907744579)
  ·
    refine ⟨32462740275132241361616869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21641826850088160907744579 32462740275132241361616869)
    ·
      refine ⟨6086763801587295255303163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32462740275132241361616869 6086763801587295255303163)
      ·
        refine ⟨9130145702380942882954745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6086763801587295255303163 9130145702380942882954745)
        ·
          refine ⟨6847609276785707162216059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9130145702380942882954745 6847609276785707162216059)
          ·
            refine ⟨10271413915178560743324089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6847609276785707162216059 10271413915178560743324089)
            ·
              refine ⟨7703560436383920557493067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10271413915178560743324089 7703560436383920557493067)
              ·
                refine ⟨11555340654575880836239601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7703560436383920557493067 11555340654575880836239601)
                ·
                  refine ⟨8666505490931910627179701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11555340654575880836239601 8666505490931910627179701)
                  ·
                    refine ⟨812484889774866621298097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8666505490931910627179701 812484889774866621298097)
                    ·
                      rfl

theorem cell23_4746926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_4746926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746926 prefixEnd_4746926 := by exact prefixLift 4746926
  have htrace : WordTrace (prefixWord ++ tailWord_4746926) baseStart_4746926 baseEnd_4746926 := by
    simpa [prefixWord, tailWord_4746926, baseEnd_4746926] using wordTrace_append hprefix tailTrace_4746926
  have hstable : (prefixWord ++ tailWord_4746926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746926).length < 2 ^ (prefixWord ++ tailWord_4746926).sum := by decide
  have hdescent : baseEnd_4746926 < baseStart_4746926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746952 : List Nat := [2, 1, 3, 1, 2, 2, 4, 2, 6]
def baseStart_4746952 : Nat := 118140960795 + 4746952 * 2 ^ 59
def prefixEnd_4746952 : Nat := 4983230072969 + 3 ^ 40 * 4746952 * 2
def baseEnd_4746952 : Nat := 270829779980179640241019

theorem tailTrace_4746952 : CollatzResearch.WordTrace tailWord_4746952 prefixEnd_4746952 270829779980179640241019 := by
  unfold tailWord_4746952
  simp only [CollatzResearch.WordTrace]
  refine ⟨86567781549305546851201555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115423708732407395801602073 86567781549305546851201555)
  ·
    refine ⟨129851672323958320276802333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86567781549305546851201555 129851672323958320276802333)
    ·
      refine ⟨48694377121484370103800875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129851672323958320276802333 48694377121484370103800875)
      ·
        refine ⟨73041565682226555155701313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48694377121484370103800875 73041565682226555155701313)
        ·
          refine ⟨54781174261669916366775985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73041565682226555155701313 54781174261669916366775985)
          ·
            refine ⟨41085880696252437275081989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54781174261669916366775985 41085880696252437275081989)
            ·
              refine ⟨7703602630547331989077873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41085880696252437275081989 7703602630547331989077873)
              ·
                refine ⟨5777701972910498991808405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7703602630547331989077873 5777701972910498991808405)
                ·
                  refine ⟨270829779980179640241019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5777701972910498991808405 270829779980179640241019)
                  ·
                    rfl

theorem cell23_4746952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 6].length) (baseStart_4746952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746952 prefixEnd_4746952 := by exact prefixLift 4746952
  have htrace : WordTrace (prefixWord ++ tailWord_4746952) baseStart_4746952 baseEnd_4746952 := by
    simpa [prefixWord, tailWord_4746952, baseEnd_4746952] using wordTrace_append hprefix tailTrace_4746952
  have hstable : (prefixWord ++ tailWord_4746952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746952).length < 2 ^ (prefixWord ++ tailWord_4746952).sum := by decide
  have hdescent : baseEnd_4746952 < baseStart_4746952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746975 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 7]
def baseStart_4746975 : Nat := 118140960795 + 4746975 * 2 ^ 59
def prefixEnd_4746975 : Nat := 4983230072969 + 3 ^ 40 * 4746975 * 2
def baseEnd_4746975 : Nat := 2437479829876670172181565

theorem tailTrace_4746975 : CollatzResearch.WordTrace tailWord_4746975 prefixEnd_4746975 2437479829876670172181565 := by
  unfold tailWord_4746975
  simp only [CollatzResearch.WordTrace]
  refine ⟨173136401977527768630490379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115424267985018512420326919 173136401977527768630490379)
  ·
    refine ⟨259704602966291652945735569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173136401977527768630490379 259704602966291652945735569)
    ·
      refine ⟨194778452224718739709301677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259704602966291652945735569 194778452224718739709301677)
      ·
        refine ⟨73041919584269527390988129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194778452224718739709301677 73041919584269527390988129)
        ·
          refine ⟨54781439688202145543241097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73041919584269527390988129 54781439688202145543241097)
          ·
            refine ⟨41086079766151609157430823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54781439688202145543241097 41086079766151609157430823)
            ·
              refine ⟨61629119649227413736146235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41086079766151609157430823 61629119649227413736146235)
              ·
                refine ⟨92443679473841120604219353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61629119649227413736146235 92443679473841120604219353)
                ·
                  refine ⟨69332759605380840453164515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92443679473841120604219353 69332759605380840453164515)
                  ·
                    refine ⟨103999139408071260679746773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69332759605380840453164515 103999139408071260679746773)
                    ·
                      refine ⟨2437479829876670172181565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 103999139408071260679746773 2437479829876670172181565)
                      ·
                        rfl

theorem cell23_4746975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_4746975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746975 prefixEnd_4746975 := by exact prefixLift 4746975
  have htrace : WordTrace (prefixWord ++ tailWord_4746975) baseStart_4746975 baseEnd_4746975 := by
    simpa [prefixWord, tailWord_4746975, baseEnd_4746975] using wordTrace_append hprefix tailTrace_4746975
  have hstable : (prefixWord ++ tailWord_4746975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746975).length < 2 ^ (prefixWord ++ tailWord_4746975).sum := by decide
  have hdescent : baseEnd_4746975 < baseStart_4746975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746983 : List Nat := [1, 1, 5, 4, 1, 2, 1, 1, 2, 2, 3]
def baseStart_4746983 : Nat := 118140960795 + 4746983 * 2 ^ 59
def prefixEnd_4746983 : Nat := 4983230072969 + 3 ^ 40 * 4746983 * 2
def baseEnd_4746983 : Nat := 2437483937721906140881529

theorem tailTrace_4746983 : CollatzResearch.WordTrace tailWord_4746983 prefixEnd_4746983 2437483937721906140881529 := by
  unfold tailWord_4746983
  simp only [CollatzResearch.WordTrace]
  refine ⟨173136693761498785996781603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115424462507665857331187735 173136693761498785996781603)
  ·
    refine ⟨259705040642248178995172405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173136693761498785996781603 259705040642248178995172405)
    ·
      refine ⟨24347347560210766780797413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 259705040642248178995172405 24347347560210766780797413)
      ·
        refine ⟨4565127667539518771399515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24347347560210766780797413 4565127667539518771399515)
        ·
          refine ⟨6847691501309278157099273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4565127667539518771399515 6847691501309278157099273)
          ·
            refine ⟨5135768625981958617824455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6847691501309278157099273 5135768625981958617824455)
            ·
              refine ⟨7703652938972937926736683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5135768625981958617824455 7703652938972937926736683)
              ·
                refine ⟨11555479408459406890105025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7703652938972937926736683 11555479408459406890105025)
                ·
                  refine ⟨8666609556344555167578769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11555479408459406890105025 8666609556344555167578769)
                  ·
                    refine ⟨6499957167258416375684077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8666609556344555167578769 6499957167258416375684077)
                    ·
                      refine ⟨2437483937721906140881529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6499957167258416375684077 2437483937721906140881529)
                      ·
                        rfl

theorem cell23_4746983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_4746983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746983 prefixEnd_4746983 := by exact prefixLift 4746983
  have htrace : WordTrace (prefixWord ++ tailWord_4746983) baseStart_4746983 baseEnd_4746983 := by
    simpa [prefixWord, tailWord_4746983, baseEnd_4746983] using wordTrace_append hprefix tailTrace_4746983
  have hstable : (prefixWord ++ tailWord_4746983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746983).length < 2 ^ (prefixWord ++ tailWord_4746983).sum := by decide
  have hdescent : baseEnd_4746983 < baseStart_4746983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4746999 : List Nat := [1, 1, 3, 1, 1, 1, 8, 1, 1, 5]
def baseStart_4746999 : Nat := 118140960795 + 4746999 * 2 ^ 59
def prefixEnd_4746999 : Nat := 4983230072969 + 3 ^ 40 * 4746999 * 2
def baseEnd_4746999 : Nat := 812497384470792692760485

theorem tailTrace_4746999 : CollatzResearch.WordTrace tailWord_4746999 prefixEnd_4746999 812497384470792692760485 := by
  unfold tailWord_4746999
  simp only [CollatzResearch.WordTrace]
  refine ⟨173137277329440820729364051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115424851552960547152909367 173137277329440820729364051)
  ·
    refine ⟨259705915994161231094046077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173137277329440820729364051 259705915994161231094046077)
    ·
      refine ⟨97389718497810461660267279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 259705915994161231094046077 97389718497810461660267279)
      ·
        refine ⟨146084577746715692490400919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97389718497810461660267279 146084577746715692490400919)
        ·
          refine ⟨219126866620073538735601379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146084577746715692490400919 219126866620073538735601379)
          ·
            refine ⟨328690299930110308103402069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219126866620073538735601379 328690299930110308103402069)
            ·
              refine ⟨3851839452305980173086743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 328690299930110308103402069 3851839452305980173086743)
              ·
                refine ⟨5777759178458970259630115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3851839452305980173086743 5777759178458970259630115)
                ·
                  refine ⟨8666638767688455389445173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5777759178458970259630115 8666638767688455389445173)
                  ·
                    refine ⟨812497384470792692760485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8666638767688455389445173 812497384470792692760485)
                    ·
                      rfl

theorem cell23_4746999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 1, 5].length) (baseStart_4746999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4746999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4746999 prefixEnd_4746999 := by exact prefixLift 4746999
  have htrace : WordTrace (prefixWord ++ tailWord_4746999) baseStart_4746999 baseEnd_4746999 := by
    simpa [prefixWord, tailWord_4746999, baseEnd_4746999] using wordTrace_append hprefix tailTrace_4746999
  have hstable : (prefixWord ++ tailWord_4746999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4746999).length < 2 ^ (prefixWord ++ tailWord_4746999).sum := by decide
  have hdescent : baseEnd_4746999 < baseStart_4746999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4746999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747022 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5]
def baseStart_4747022 : Nat := 118140960795 + 4747022 * 2 ^ 59
def prefixEnd_4747022 : Nat := 4983230072969 + 3 ^ 40 * 4747022 * 2
def baseEnd_4747022 : Nat := 2437503963467431488293849

theorem tailTrace_4747022 : CollatzResearch.WordTrace tailWord_4747022 prefixEnd_4747022 2437503963467431488293849 := by
  unfold tailWord_4747022
  simp only [CollatzResearch.WordTrace]
  refine ⟨21642264526044686957181415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115425410805571663771634213 21642264526044686957181415)
  ·
    refine ⟨32463396789067030435772123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21642264526044686957181415 32463396789067030435772123)
    ·
      refine ⟨48695095183600545653658185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32463396789067030435772123 48695095183600545653658185)
      ·
        refine ⟨36521321387700409240243639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48695095183600545653658185 36521321387700409240243639)
        ·
          refine ⟨54781982081550613860365459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36521321387700409240243639 54781982081550613860365459)
          ·
            refine ⟨82172973122325920790548189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54781982081550613860365459 82172973122325920790548189)
            ·
              refine ⟨30814864920872220296455571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82172973122325920790548189 30814864920872220296455571)
              ·
                refine ⟨46222297381308330444683357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30814864920872220296455571 46222297381308330444683357)
                ·
                  refine ⟨17333361517990623916756259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46222297381308330444683357 17333361517990623916756259)
                  ·
                    refine ⟨26000042276985935875134389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17333361517990623916756259 26000042276985935875134389)
                    ·
                      refine ⟨2437503963467431488293849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26000042276985935875134389 2437503963467431488293849)
                      ·
                        rfl

theorem cell23_4747022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_4747022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747022 prefixEnd_4747022 := by exact prefixLift 4747022
  have htrace : WordTrace (prefixWord ++ tailWord_4747022) baseStart_4747022 baseEnd_4747022 := by
    simpa [prefixWord, tailWord_4747022, baseEnd_4747022] using wordTrace_append hprefix tailTrace_4747022
  have hstable : (prefixWord ++ tailWord_4747022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747022).length < 2 ^ (prefixWord ++ tailWord_4747022).sum := by decide
  have hdescent : baseEnd_4747022 < baseStart_4747022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747025 : List Nat := [1, 2, 2, 1, 1, 3, 1, 12]
def baseStart_4747025 : Nat := 118140960795 + 4747025 * 2 ^ 59
def prefixEnd_4747025 : Nat := 4983230072969 + 3 ^ 40 * 4747025 * 2
def baseEnd_4747025 : Nat := 90277981626273888020605

theorem tailTrace_4747025 : CollatzResearch.WordTrace tailWord_4747025 prefixEnd_4747025 90277981626273888020605 := by
  unfold tailWord_4747025
  simp only [CollatzResearch.WordTrace]
  refine ⟨173138225627346627169810529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115425483751564418113207019 173138225627346627169810529)
  ·
    refine ⟨129853669220509970377357897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173138225627346627169810529 129853669220509970377357897)
    ·
      refine ⟨97390251915382477783018423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129853669220509970377357897 97390251915382477783018423)
      ·
        refine ⟨146085377873073716674527635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97390251915382477783018423 146085377873073716674527635)
        ·
          refine ⟨219128066809610575011791453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146085377873073716674527635 219128066809610575011791453)
          ·
            refine ⟨82173025053603965629421795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 219128066809610575011791453 82173025053603965629421795)
            ·
              refine ⟨123259537580405948444132693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82173025053603965629421795 123259537580405948444132693)
              ·
                refine ⟨90277981626273888020605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 123259537580405948444132693 90277981626273888020605)
                ·
                  rfl

theorem cell23_4747025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 12].length) (baseStart_4747025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747025 prefixEnd_4747025 := by exact prefixLift 4747025
  have htrace : WordTrace (prefixWord ++ tailWord_4747025) baseStart_4747025 baseEnd_4747025 := by
    simpa [prefixWord, tailWord_4747025, baseEnd_4747025] using wordTrace_append hprefix tailTrace_4747025
  have hstable : (prefixWord ++ tailWord_4747025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747025).length < 2 ^ (prefixWord ++ tailWord_4747025).sum := by decide
  have hdescent : baseEnd_4747025 < baseStart_4747025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747029 : List Nat := [1, 3, 2, 1, 2, 5, 1, 1, 1, 6]
def baseStart_4747029 : Nat := 118140960795 + 4747029 * 2 ^ 59
def prefixEnd_4747029 : Nat := 4983230072969 + 3 ^ 40 * 4747029 * 2
def baseEnd_4747029 : Nat := 812502519277337653635439

theorem tailTrace_4747029 : CollatzResearch.WordTrace tailWord_4747029 prefixEnd_4747029 812502519277337653635439 := by
  unfold tailWord_4747029
  simp only [CollatzResearch.WordTrace]
  refine ⟨173138371519332135852956141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115425581012888090568637427 173138371519332135852956141)
  ·
    refine ⟨64926889319749550944858553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173138371519332135852956141 64926889319749550944858553)
    ·
      refine ⟨48695166989812163208643915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64926889319749550944858553 48695166989812163208643915)
      ·
        refine ⟨73042750484718244812965873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48695166989812163208643915 73042750484718244812965873)
        ·
          refine ⟨54782062863538683609724405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73042750484718244812965873 54782062863538683609724405)
          ·
            refine ⟨5135818393456751588411663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54782062863538683609724405 5135818393456751588411663)
            ·
              refine ⟨7703727590185127382617495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5135818393456751588411663 7703727590185127382617495)
              ·
                refine ⟨11555591385277691073926243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7703727590185127382617495 11555591385277691073926243)
                ·
                  refine ⟨17333387077916536610889365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11555591385277691073926243 17333387077916536610889365)
                  ·
                    refine ⟨812502519277337653635439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17333387077916536610889365 812502519277337653635439)
                    ·
                      rfl

theorem cell23_4747029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_4747029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747029 prefixEnd_4747029 := by exact prefixLift 4747029
  have htrace : WordTrace (prefixWord ++ tailWord_4747029) baseStart_4747029 baseEnd_4747029 := by
    simpa [prefixWord, tailWord_4747029, baseEnd_4747029] using wordTrace_append hprefix tailTrace_4747029
  have hstable : (prefixWord ++ tailWord_4747029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747029).length < 2 ^ (prefixWord ++ tailWord_4747029).sum := by decide
  have hdescent : baseEnd_4747029 < baseStart_4747029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747035 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 7]
def baseStart_4747035 : Nat := 118140960795 + 4747035 * 2 ^ 59
def prefixEnd_4747035 : Nat := 4983230072969 + 3 ^ 40 * 4747035 * 2
def baseEnd_4747035 : Nat := 2437510638715939937431289

theorem tailTrace_4747035 : CollatzResearch.WordTrace tailWord_4747035 prefixEnd_4747035 2437510638715939937431289 := by
  unfold tailWord_4747035
  simp only [CollatzResearch.WordTrace]
  refine ⟨173138590357310398877674559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115425726904873599251783039 173138590357310398877674559)
  ·
    refine ⟨259707885535965598316511839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173138590357310398877674559 259707885535965598316511839)
    ·
      refine ⟨389561828303948397474767759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259707885535965598316511839 389561828303948397474767759)
      ·
        refine ⟨584342742455922596212151639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389561828303948397474767759 584342742455922596212151639)
        ·
          refine ⟨876514113683883894318227459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 584342742455922596212151639 876514113683883894318227459)
          ·
            refine ⟨1314771170525825841477341189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876514113683883894318227459 1314771170525825841477341189)
            ·
              refine ⟨246519594473592345277001473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1314771170525825841477341189 246519594473592345277001473)
              ·
                refine ⟨184889695855194258957751105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246519594473592345277001473 184889695855194258957751105)
                ·
                  refine ⟨138667271891395694218313329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184889695855194258957751105 138667271891395694218313329)
                  ·
                    refine ⟨104000453918546770663734997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 138667271891395694218313329 104000453918546770663734997)
                    ·
                      refine ⟨2437510638715939937431289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104000453918546770663734997 2437510638715939937431289)
                      ·
                        rfl

theorem cell23_4747035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 7].length) (baseStart_4747035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747035 prefixEnd_4747035 := by exact prefixLift 4747035
  have htrace : WordTrace (prefixWord ++ tailWord_4747035) baseStart_4747035 baseEnd_4747035 := by
    simpa [prefixWord, tailWord_4747035, baseEnd_4747035] using wordTrace_append hprefix tailTrace_4747035
  have hstable : (prefixWord ++ tailWord_4747035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747035).length < 2 ^ (prefixWord ++ tailWord_4747035).sum := by decide
  have hdescent : baseEnd_4747035 < baseStart_4747035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747036 : List Nat := [2, 2, 3, 1, 1, 2, 1, 4, 3, 2, 2]
def baseStart_4747036 : Nat := 118140960795 + 4747036 * 2 ^ 59
def prefixEnd_4747036 : Nat := 4983230072969 + 3 ^ 40 * 4747036 * 2
def baseEnd_4747036 : Nat := 2437511152196594433518785

theorem tailTrace_4747036 : CollatzResearch.WordTrace tailWord_4747036 prefixEnd_4747036 2437511152196594433518785 := by
  unfold tailWord_4747036
  simp only [CollatzResearch.WordTrace]
  refine ⟨86569313415153388024230481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115425751220204517365640641 86569313415153388024230481)
  ·
    refine ⟨64926985061365041018172861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86569313415153388024230481 64926985061365041018172861)
    ·
      refine ⟨24347619398011890381814823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64926985061365041018172861 24347619398011890381814823)
      ·
        refine ⟨36521429097017835572722235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24347619398011890381814823 36521429097017835572722235)
        ·
          refine ⟨54782143645526753359083353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36521429097017835572722235 54782143645526753359083353)
          ·
            refine ⟨41086607734145065019312515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54782143645526753359083353 41086607734145065019312515)
            ·
              refine ⟨61629911601217597528968773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41086607734145065019312515 61629911601217597528968773)
              ·
                refine ⟨11555608425228299536681645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61629911601217597528968773 11555608425228299536681645)
                ·
                  refine ⟨4333353159460612326255617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11555608425228299536681645 4333353159460612326255617)
                  ·
                    refine ⟨3250014869595459244691713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4333353159460612326255617 3250014869595459244691713)
                    ·
                      refine ⟨2437511152196594433518785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3250014869595459244691713 2437511152196594433518785)
                      ·
                        rfl

theorem cell23_4747036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_4747036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747036 prefixEnd_4747036 := by exact prefixLift 4747036
  have htrace : WordTrace (prefixWord ++ tailWord_4747036) baseStart_4747036 baseEnd_4747036 := by
    simpa [prefixWord, tailWord_4747036, baseEnd_4747036] using wordTrace_append hprefix tailTrace_4747036
  have hstable : (prefixWord ++ tailWord_4747036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747036).length < 2 ^ (prefixWord ++ tailWord_4747036).sum := by decide
  have hdescent : baseEnd_4747036 < baseStart_4747036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747042 : List Nat := [3, 3, 1, 1, 2, 1, 3, 9]
def baseStart_4747042 : Nat := 118140960795 + 4747042 * 2 ^ 59
def prefixEnd_4747042 : Nat := 4983230072969 + 3 ^ 40 * 4747042 * 2
def baseEnd_4747042 : Nat := 90278304928908200371991

theorem tailTrace_4747042 : CollatzResearch.WordTrace tailWord_4747042 prefixEnd_4747042 90278304928908200371991 := by
  unfold tailWord_4747042
  simp only [CollatzResearch.WordTrace]
  refine ⟨43284711417071259768294845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115425897112190026048786253 43284711417071259768294845)
  ·
    refine ⟨16231766781401722413110567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43284711417071259768294845 16231766781401722413110567)
    ·
      refine ⟨24347650172102583619665851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16231766781401722413110567 24347650172102583619665851)
      ·
        refine ⟨36521475258153875429498777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24347650172102583619665851 36521475258153875429498777)
        ·
          refine ⟨27391106443615406572124083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36521475258153875429498777 27391106443615406572124083)
          ·
            refine ⟨41086659665423109858186125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27391106443615406572124083 41086659665423109858186125)
            ·
              refine ⟨15407497374533666196819797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41086659665423109858186125 15407497374533666196819797)
              ·
                refine ⟨90278304928908200371991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15407497374533666196819797 90278304928908200371991)
                ·
                  rfl

theorem cell23_4747042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 9].length) (baseStart_4747042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747042 prefixEnd_4747042 := by exact prefixLift 4747042
  have htrace : WordTrace (prefixWord ++ tailWord_4747042) baseStart_4747042 baseEnd_4747042 := by
    simpa [prefixWord, tailWord_4747042, baseEnd_4747042] using wordTrace_append hprefix tailTrace_4747042
  have hstable : (prefixWord ++ tailWord_4747042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747042).length < 2 ^ (prefixWord ++ tailWord_4747042).sum := by decide
  have hdescent : baseEnd_4747042 < baseStart_4747042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747059 : List Nat := [1, 1, 1, 2, 8, 1, 9]
def baseStart_4747059 : Nat := 118140960795 + 4747059 * 2 ^ 59
def prefixEnd_4747059 : Nat := 4983230072969 + 3 ^ 40 * 4747059 * 2
def baseEnd_4747059 : Nat := 30092876077180837574459

theorem tailTrace_4747059 : CollatzResearch.WordTrace tailWord_4747059 prefixEnd_4747059 30092876077180837574459 := by
  unfold tailWord_4747059
  simp only [CollatzResearch.WordTrace]
  refine ⟨173139465709223450976548231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115426310472815633984365487 173139465709223450976548231)
  ·
    refine ⟨259709198563835176464822347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173139465709223450976548231 259709198563835176464822347)
    ·
      refine ⟨389563797845752764697233521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259709198563835176464822347 389563797845752764697233521)
      ·
        refine ⟨292172848384314573522925141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 389563797845752764697233521 292172848384314573522925141)
        ·
          refine ⟨3423900567003686408471779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 292172848384314573522925141 3423900567003686408471779)
          ·
            refine ⟨5135850850505529612707669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3423900567003686408471779 5135850850505529612707669)
            ·
              refine ⟨30092876077180837574459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5135850850505529612707669 30092876077180837574459)
              ·
                rfl

theorem cell23_4747059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 9].length) (baseStart_4747059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747059 prefixEnd_4747059 := by exact prefixLift 4747059
  have htrace : WordTrace (prefixWord ++ tailWord_4747059) baseStart_4747059 baseEnd_4747059 := by
    simpa [prefixWord, tailWord_4747059, baseEnd_4747059] using wordTrace_append hprefix tailTrace_4747059
  have hstable : (prefixWord ++ tailWord_4747059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747059).length < 2 ^ (prefixWord ++ tailWord_4747059).sum := by decide
  have hdescent : baseEnd_4747059 < baseStart_4747059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747070 : List Nat := [4, 2, 1, 2, 2, 3, 1, 1, 3, 2, 2]
def baseStart_4747070 : Nat := 118140960795 + 4747070 * 2 ^ 59
def prefixEnd_4747070 : Nat := 4983230072969 + 3 ^ 40 * 4747070 * 2
def baseEnd_4747070 : Nat := 2437528610538847300493629

theorem tailTrace_4747070 : CollatzResearch.WordTrace tailWord_4747070 prefixEnd_4747070 2437528610538847300493629 := by
  unfold tailWord_4747070
  simp only [CollatzResearch.WordTrace]
  refine ⟨21642483364022949981899833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115426577941455733236799109 21642483364022949981899833)
  ·
    refine ⟨16231862523017212486424875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21642483364022949981899833 16231862523017212486424875)
    ·
      refine ⟨24347793784525818729637313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16231862523017212486424875 24347793784525818729637313)
      ·
        refine ⟨18260845338394364047227985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24347793784525818729637313 18260845338394364047227985)
        ·
          refine ⟨13695634003795773035420989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18260845338394364047227985 13695634003795773035420989)
          ·
            refine ⟨5135862751423414888282871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13695634003795773035420989 5135862751423414888282871)
            ·
              refine ⟨7703794127135122332424307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5135862751423414888282871 7703794127135122332424307)
              ·
                refine ⟨11555691190702683498636461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7703794127135122332424307 11555691190702683498636461)
                ·
                  refine ⟨4333384196513506311988673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11555691190702683498636461 4333384196513506311988673)
                  ·
                    refine ⟨3250038147385129733991505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4333384196513506311988673 3250038147385129733991505)
                    ·
                      refine ⟨2437528610538847300493629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3250038147385129733991505 2437528610538847300493629)
                      ·
                        rfl

theorem cell23_4747070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_4747070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747070 prefixEnd_4747070 := by exact prefixLift 4747070
  have htrace : WordTrace (prefixWord ++ tailWord_4747070) baseStart_4747070 baseEnd_4747070 := by
    simpa [prefixWord, tailWord_4747070, baseEnd_4747070] using wordTrace_append hprefix tailTrace_4747070
  have hstable : (prefixWord ++ tailWord_4747070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747070).length < 2 ^ (prefixWord ++ tailWord_4747070).sum := by decide
  have hdescent : baseEnd_4747070 < baseStart_4747070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747122 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 2, 3, 6]
def baseStart_4747122 : Nat := 118140960795 + 4747122 * 2 ^ 59
def prefixEnd_4747122 : Nat := 4983230072969 + 3 ^ 40 * 4747122 * 2
def baseEnd_4747122 : Nat := 2437555311532881097043389

theorem tailTrace_4747122 : CollatzResearch.WordTrace tailWord_4747122 prefixEnd_4747122 2437555311532881097043389 := by
  unfold tailWord_4747122
  simp only [CollatzResearch.WordTrace]
  refine ⟨43285440876998803184022905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115427842338663475157394413 43285440876998803184022905)
  ·
    refine ⟨32464080657749102388017179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43285440876998803184022905 32464080657749102388017179)
    ·
      refine ⟨48696120986623653582025769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32464080657749102388017179 48696120986623653582025769)
      ·
        refine ⟨36522090739967740186519327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48696120986623653582025769 36522090739967740186519327)
        ·
          refine ⟨54783136109951610279778991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36522090739967740186519327 54783136109951610279778991)
          ·
            refine ⟨82174704164927415419668487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54783136109951610279778991 82174704164927415419668487)
            ·
              refine ⟨123262056247391123129502731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82174704164927415419668487 123262056247391123129502731)
              ·
                refine ⟨184893084371086684694254097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123262056247391123129502731 184893084371086684694254097)
                ·
                  refine ⟨138669813278315013520690573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184893084371086684694254097 138669813278315013520690573)
                  ·
                    refine ⟨52001179979368130070258965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 138669813278315013520690573 52001179979368130070258965)
                    ·
                      refine ⟨2437555311532881097043389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52001179979368130070258965 2437555311532881097043389)
                      ·
                        rfl

theorem cell23_4747122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_4747122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747122 prefixEnd_4747122 := by exact prefixLift 4747122
  have htrace : WordTrace (prefixWord ++ tailWord_4747122) baseStart_4747122 baseEnd_4747122 := by
    simpa [prefixWord, tailWord_4747122, baseEnd_4747122] using wordTrace_append hprefix tailTrace_4747122
  have hstable : (prefixWord ++ tailWord_4747122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747122).length < 2 ^ (prefixWord ++ tailWord_4747122).sum := by decide
  have hdescent : baseEnd_4747122 < baseStart_4747122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747139 : List Nat := [1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 4]
def baseStart_4747139 : Nat := 118140960795 + 4747139 * 2 ^ 59
def prefixEnd_4747139 : Nat := 4983230072969 + 3 ^ 40 * 4747139 * 2
def baseEnd_4747139 : Nat := 2437564040704007530530811

theorem tailTrace_4747139 : CollatzResearch.WordTrace tailWord_4747139 prefixEnd_4747139 2437564040704007530530811 := by
  unfold tailWord_4747139
  simp only [CollatzResearch.WordTrace]
  refine ⟨173142383548933624639460471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115428255699289083092973647 173142383548933624639460471)
  ·
    refine ⟨259713575323400436959190707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173142383548933624639460471 259713575323400436959190707)
    ·
      refine ⟨389570362985100655438786061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259713575323400436959190707 389570362985100655438786061)
      ·
        refine ⟨146088886119412745789544773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 389570362985100655438786061 146088886119412745789544773)
        ·
          refine ⟨27391666147389889835539645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146088886119412745789544773 27391666147389889835539645)
          ·
            refine ⟨10271874805271208688327367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27391666147389889835539645 10271874805271208688327367)
            ·
              refine ⟨15407812207906813032491051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10271874805271208688327367 15407812207906813032491051)
              ·
                refine ⟨23111718311860219548736577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15407812207906813032491051 23111718311860219548736577)
                ·
                  refine ⟨17333788733895164661552433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23111718311860219548736577 17333788733895164661552433)
                  ·
                    refine ⟨13000341550421373496164325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17333788733895164661552433 13000341550421373496164325)
                    ·
                      refine ⟨2437564040704007530530811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13000341550421373496164325 2437564040704007530530811)
                      ·
                        rfl

theorem cell23_4747139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_4747139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747139 prefixEnd_4747139 := by exact prefixLift 4747139
  have htrace : WordTrace (prefixWord ++ tailWord_4747139) baseStart_4747139 baseEnd_4747139 := by
    simpa [prefixWord, tailWord_4747139, baseEnd_4747139] using wordTrace_append hprefix tailTrace_4747139
  have hstable : (prefixWord ++ tailWord_4747139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747139).length < 2 ^ (prefixWord ++ tailWord_4747139).sum := by decide
  have hdescent : baseEnd_4747139 < baseStart_4747139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747143 : List Nat := [1, 1, 4, 2, 4, 1, 2, 1, 1, 4, 2]
def baseStart_4747143 : Nat := 118140960795 + 4747143 * 2 ^ 59
def prefixEnd_4747143 : Nat := 4983230072969 + 3 ^ 40 * 4747143 * 2
def baseEnd_4747143 : Nat := 2437566094626625514880793

theorem tailTrace_4747143 : CollatzResearch.WordTrace tailWord_4747143 prefixEnd_4747143 2437566094626625514880793 := by
  unfold tailWord_4747143
  simp only [CollatzResearch.WordTrace]
  refine ⟨173142529440919133322606083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115428352960612755548404055 173142529440919133322606083)
  ·
    refine ⟨259713794161378699983909125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173142529440919133322606083 259713794161378699983909125)
    ·
      refine ⟨48696336405258506246982961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 259713794161378699983909125 48696336405258506246982961)
      ·
        refine ⟨36522252303943879685237221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48696336405258506246982961 36522252303943879685237221)
        ·
          refine ⟨6847922306989477440981979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36522252303943879685237221 6847922306989477440981979)
          ·
            refine ⟨10271883460484216161472969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6847922306989477440981979 10271883460484216161472969)
            ·
              refine ⟨7703912595363162121104727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10271883460484216161472969 7703912595363162121104727)
              ·
                refine ⟨11555868893044743181657091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7703912595363162121104727 11555868893044743181657091)
                ·
                  refine ⟨17333803339567114772485637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11555868893044743181657091 17333803339567114772485637)
                  ·
                    refine ⟨3250088126168834019841057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17333803339567114772485637 3250088126168834019841057)
                    ·
                      refine ⟨2437566094626625514880793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3250088126168834019841057 2437566094626625514880793)
                      ·
                        rfl

theorem cell23_4747143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_4747143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747143 prefixEnd_4747143 := by exact prefixLift 4747143
  have htrace : WordTrace (prefixWord ++ tailWord_4747143) baseStart_4747143 baseEnd_4747143 := by
    simpa [prefixWord, tailWord_4747143, baseEnd_4747143] using wordTrace_append hprefix tailTrace_4747143
  have hstable : (prefixWord ++ tailWord_4747143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747143).length < 2 ^ (prefixWord ++ tailWord_4747143).sum := by decide
  have hdescent : baseEnd_4747143 < baseStart_4747143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747236 : List Nat := [2, 3, 1, 1, 1, 1, 5, 2, 2, 2, 3]
def baseStart_4747236 : Nat := 118140960795 + 4747236 * 2 ^ 59
def prefixEnd_4747236 : Nat := 4983230072969 + 3 ^ 40 * 4747236 * 2
def baseEnd_4747236 : Nat := 2437613848327493651017865

theorem tailTrace_4747236 : CollatzResearch.WordTrace tailWord_4747236 prefixEnd_4747236 2437613848327493651017865 := by
  unfold tailWord_4747236
  simp only [CollatzResearch.WordTrace]
  refine ⟨86572960714791105102870781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115430614286388140137161041 86572960714791105102870781)
  ·
    refine ⟨32464860268046664413576543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86572960714791105102870781 32464860268046664413576543)
    ·
      refine ⟨48697290402069996620364815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32464860268046664413576543 48697290402069996620364815)
      ·
        refine ⟨73045935603104994930547223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48697290402069996620364815 73045935603104994930547223)
        ·
          refine ⟨109568903404657492395820835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73045935603104994930547223 109568903404657492395820835)
          ·
            refine ⟨164353355106986238593731253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109568903404657492395820835 164353355106986238593731253)
            ·
              refine ⟨15408127041279959868162305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 164353355106986238593731253 15408127041279959868162305)
              ·
                refine ⟨11556095280959969901121729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15408127041279959868162305 11556095280959969901121729)
                ·
                  refine ⟨8667071460719977425841297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11556095280959969901121729 8667071460719977425841297)
                  ·
                    refine ⟨6500303595539983069380973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8667071460719977425841297 6500303595539983069380973)
                    ·
                      refine ⟨2437613848327493651017865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6500303595539983069380973 2437613848327493651017865)
                      ·
                        rfl

theorem cell23_4747236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_4747236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747236 prefixEnd_4747236 := by exact prefixLift 4747236
  have htrace : WordTrace (prefixWord ++ tailWord_4747236) baseStart_4747236 baseEnd_4747236 := by
    simpa [prefixWord, tailWord_4747236, baseEnd_4747236] using wordTrace_append hprefix tailTrace_4747236
  have hstable : (prefixWord ++ tailWord_4747236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747236).length < 2 ^ (prefixWord ++ tailWord_4747236).sum := by decide
  have hdescent : baseEnd_4747236 < baseStart_4747236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747256 : List Nat := [2, 1, 2, 1, 1, 3, 6, 1, 6]
def baseStart_4747256 : Nat := 118140960795 + 4747256 * 2 ^ 59
def prefixEnd_4747256 : Nat := 4983230072969 + 3 ^ 40 * 4747256 * 2
def baseEnd_4747256 : Nat := 270847124215620396974197

theorem tailTrace_4747256 : CollatzResearch.WordTrace tailWord_4747256 prefixEnd_4747256 270847124215620396974197 := by
  unfold tailWord_4747256
  simp only [CollatzResearch.WordTrace]
  refine ⟨86573325444754876810734811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115431100593006502414313081 86573325444754876810734811)
  ·
    refine ⟨129859988167132315216102217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86573325444754876810734811 129859988167132315216102217)
    ·
      refine ⟨97394991125349236412076663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129859988167132315216102217 97394991125349236412076663)
      ·
        refine ⟨146092486688023854618114995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97394991125349236412076663 146092486688023854618114995)
        ·
          refine ⟨219138730032035781927172493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146092486688023854618114995 219138730032035781927172493)
          ·
            refine ⟨82177023762013418222689685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 219138730032035781927172493 82177023762013418222689685)
            ·
              refine ⟨3852047988844378979188579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 82177023762013418222689685 3852047988844378979188579)
              ·
                refine ⟨5778071983266568468782869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3852047988844378979188579 5778071983266568468782869)
                ·
                  refine ⟨270847124215620396974197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5778071983266568468782869 270847124215620396974197)
                  ·
                    rfl

theorem cell23_4747256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 6].length) (baseStart_4747256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747256 prefixEnd_4747256 := by exact prefixLift 4747256
  have htrace : WordTrace (prefixWord ++ tailWord_4747256) baseStart_4747256 baseEnd_4747256 := by
    simpa [prefixWord, tailWord_4747256, baseEnd_4747256] using wordTrace_append hprefix tailTrace_4747256
  have hstable : (prefixWord ++ tailWord_4747256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747256).length < 2 ^ (prefixWord ++ tailWord_4747256).sum := by decide
  have hdescent : baseEnd_4747256 < baseStart_4747256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747299 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 3, 6]
def baseStart_4747299 : Nat := 118140960795 + 4747299 * 2 ^ 59
def prefixEnd_4747299 : Nat := 4983230072969 + 3 ^ 40 * 4747299 * 2
def baseEnd_4747299 : Nat := 812548732536242301510025

theorem tailTrace_4747299 : CollatzResearch.WordTrace tailWord_4747299 prefixEnd_4747299 812548732536242301510025 := by
  unfold tailWord_4747299
  simp only [CollatzResearch.WordTrace]
  refine ⟨173148219228353971965284951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115432146152235981310189967 173148219228353971965284951)
  ·
    refine ⟨259722328842530957947927427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173148219228353971965284951 259722328842530957947927427)
    ·
      refine ⟨389583493263796436921891141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259722328842530957947927427 389583493263796436921891141)
      ·
        refine ⟨73046904986961831922854589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 389583493263796436921891141 73046904986961831922854589)
        ·
          refine ⟨27392589370110686971070471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73046904986961831922854589 27392589370110686971070471)
          ·
            refine ⟨41088884055166030456605707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27392589370110686971070471 41088884055166030456605707)
            ·
              refine ⟨61633326082749045684908561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41088884055166030456605707 61633326082749045684908561)
              ·
                refine ⟨46224994562061784263681421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61633326082749045684908561 46224994562061784263681421)
                ·
                  refine ⟨17334372960773169098880533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46224994562061784263681421 17334372960773169098880533)
                  ·
                    refine ⟨812548732536242301510025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17334372960773169098880533 812548732536242301510025)
                    ·
                      rfl

theorem cell23_4747299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 6].length) (baseStart_4747299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747299 prefixEnd_4747299 := by exact prefixLift 4747299
  have htrace : WordTrace (prefixWord ++ tailWord_4747299) baseStart_4747299 baseEnd_4747299 := by
    simpa [prefixWord, tailWord_4747299, baseEnd_4747299] using wordTrace_append hprefix tailTrace_4747299
  have hstable : (prefixWord ++ tailWord_4747299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747299).length < 2 ^ (prefixWord ++ tailWord_4747299).sum := by decide
  have hdescent : baseEnd_4747299 < baseStart_4747299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747319 : List Nat := [1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 6]
def baseStart_4747319 : Nat := 118140960795 + 4747319 * 2 ^ 59
def prefixEnd_4747319 : Nat := 4983230072969 + 3 ^ 40 * 4747319 * 2
def baseEnd_4747319 : Nat := 2437656467221816826279983

theorem tailTrace_4747319 : CollatzResearch.WordTrace tailWord_4747319 prefixEnd_4747319 2437656467221816826279983 := by
  unfold tailWord_4747319
  simp only [CollatzResearch.WordTrace]
  refine ⟨173148948688281515381013011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115432632458854343587342007 173148948688281515381013011)
  ·
    refine ⟨259723423032422273071519517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173148948688281515381013011 259723423032422273071519517)
    ·
      refine ⟨97396283637158352401819819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 259723423032422273071519517 97396283637158352401819819)
      ·
        refine ⟨146094425455737528602729729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97396283637158352401819819 146094425455737528602729729)
        ·
          refine ⟨109570819091803146452047297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146094425455737528602729729 109570819091803146452047297)
          ·
            refine ⟨82178114318852359839035473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109570819091803146452047297 82178114318852359839035473)
            ·
              refine ⟨61633585739139269879276605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82178114318852359839035473 61633585739139269879276605)
              ·
                refine ⟨23112594652177226204728727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61633585739139269879276605 23112594652177226204728727)
                ·
                  refine ⟨34668891978265839307093091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23112594652177226204728727 34668891978265839307093091)
                  ·
                    refine ⟨52003337967398758960639637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34668891978265839307093091 52003337967398758960639637)
                    ·
                      refine ⟨2437656467221816826279983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52003337967398758960639637 2437656467221816826279983)
                      ·
                        rfl

theorem cell23_4747319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_4747319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747319 prefixEnd_4747319 := by exact prefixLift 4747319
  have htrace : WordTrace (prefixWord ++ tailWord_4747319) baseStart_4747319 baseEnd_4747319 := by
    simpa [prefixWord, tailWord_4747319, baseEnd_4747319] using wordTrace_append hprefix tailTrace_4747319
  have hstable : (prefixWord ++ tailWord_4747319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747319).length < 2 ^ (prefixWord ++ tailWord_4747319).sum := by decide
  have hdescent : baseEnd_4747319 < baseStart_4747319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747323 : List Nat := [1, 1, 1, 1, 1, 2, 1, 8, 3, 2, 2]
def baseStart_4747323 : Nat := 118140960795 + 4747323 * 2 ^ 59
def prefixEnd_4747323 : Nat := 4983230072969 + 3 ^ 40 * 4747323 * 2
def baseEnd_4747323 : Nat := 2437658521144434810629965

theorem tailTrace_4747323 : CollatzResearch.WordTrace tailWord_4747323 prefixEnd_4747323 2437658521144434810629965 := by
  unfold tailWord_4747323
  simp only [CollatzResearch.WordTrace]
  refine ⟨173149094580267024064158623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115432729720178016042772415 173149094580267024064158623)
  ·
    refine ⟨259723641870400536096237935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173149094580267024064158623 259723641870400536096237935)
    ·
      refine ⟨389585462805600804144356903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259723641870400536096237935 389585462805600804144356903)
      ·
        refine ⟨584378194208401206216535355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389585462805600804144356903 584378194208401206216535355)
        ·
          refine ⟨876567291312601809324803033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 584378194208401206216535355 876567291312601809324803033)
          ·
            refine ⟨657425468484451356993602275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 876567291312601809324803033 657425468484451356993602275)
            ·
              refine ⟨986138202726677035490403413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 657425468484451356993602275 986138202726677035490403413)
              ·
                refine ⟨11556307063203246509653165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 986138202726677035490403413 11556307063203246509653165)
                ·
                  refine ⟨4333615148701217441119937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11556307063203246509653165 4333615148701217441119937)
                  ·
                    refine ⟨3250211361525913080839953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4333615148701217441119937 3250211361525913080839953)
                    ·
                      refine ⟨2437658521144434810629965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3250211361525913080839953 2437658521144434810629965)
                      ·
                        rfl

theorem cell23_4747323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3, 2, 2].length) (baseStart_4747323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747323 prefixEnd_4747323 := by exact prefixLift 4747323
  have htrace : WordTrace (prefixWord ++ tailWord_4747323) baseStart_4747323 baseEnd_4747323 := by
    simpa [prefixWord, tailWord_4747323, baseEnd_4747323] using wordTrace_append hprefix tailTrace_4747323
  have hstable : (prefixWord ++ tailWord_4747323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747323).length < 2 ^ (prefixWord ++ tailWord_4747323).sum := by decide
  have hdescent : baseEnd_4747323 < baseStart_4747323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747334 : List Nat := [6, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3]
def baseStart_4747334 : Nat := 118140960795 + 4747334 * 2 ^ 59
def prefixEnd_4747334 : Nat := 4983230072969 + 3 ^ 40 * 4747334 * 2
def baseEnd_4747334 : Nat := 2437664169431634267592415

theorem tailTrace_4747334 : CollatzResearch.WordTrace tailWord_4747334 prefixEnd_4747334 2437664169431634267592415 := by
  unfold tailWord_4747334
  simp only [CollatzResearch.WordTrace]
  refine ⟨5410921743225849154462783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 115432997188818115295206037 5410921743225849154462783)
  ·
    refine ⟨8116382614838773731694175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5410921743225849154462783 8116382614838773731694175)
    ·
      refine ⟨12174573922258160597541263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8116382614838773731694175 12174573922258160597541263)
      ·
        refine ⟨18261860883387240896311895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12174573922258160597541263 18261860883387240896311895)
        ·
          refine ⟨27392791325080861344467843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18261860883387240896311895 27392791325080861344467843)
          ·
            refine ⟨41089186987621292016701765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27392791325080861344467843 41089186987621292016701765)
            ·
              refine ⟨7704222560178992253131581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41089186987621292016701765 7704222560178992253131581)
              ·
                refine ⟨2889083460067122094924343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7704222560178992253131581 2889083460067122094924343)
                ·
                  refine ⟨4333625190100683142386515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2889083460067122094924343 4333625190100683142386515)
                  ·
                    refine ⟨6500437785151024713579773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4333625190100683142386515 6500437785151024713579773)
                    ·
                      refine ⟨2437664169431634267592415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6500437785151024713579773 2437664169431634267592415)
                      ·
                        rfl

theorem cell23_4747334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_4747334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747334 prefixEnd_4747334 := by exact prefixLift 4747334
  have htrace : WordTrace (prefixWord ++ tailWord_4747334) baseStart_4747334 baseEnd_4747334 := by
    simpa [prefixWord, tailWord_4747334, baseEnd_4747334] using wordTrace_append hprefix tailTrace_4747334
  have hstable : (prefixWord ++ tailWord_4747334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747334).length < 2 ^ (prefixWord ++ tailWord_4747334).sum := by decide
  have hdescent : baseEnd_4747334 < baseStart_4747334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747346 : List Nat := [3, 2, 2, 1, 4, 1, 10]
def baseStart_4747346 : Nat := 118140960795 + 4747346 * 2 ^ 59
def prefixEnd_4747346 : Nat := 4983230072969 + 3 ^ 40 * 4747346 * 2
def baseEnd_4747346 : Nat := 30094695446907261983239

theorem tailTrace_4747346 : CollatzResearch.WordTrace tailWord_4747346 prefixEnd_4747346 30094695446907261983239 := by
  unfold tailWord_4747346
  simp only [CollatzResearch.WordTrace]
  refine ⟨43287483364795924748061473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115433288972789132661497261 43287483364795924748061473)
  ·
    refine ⟨32465612523596943561046105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43287483364795924748061473 32465612523596943561046105)
    ·
      refine ⟨24349209392697707670784579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32465612523596943561046105 24349209392697707670784579)
      ·
        refine ⟨36523814089046561506176869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24349209392697707670784579 36523814089046561506176869)
        ·
          refine ⟨6848215141696230282408163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36523814089046561506176869 6848215141696230282408163)
          ·
            refine ⟨10272322712544345423612245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6848215141696230282408163 10272322712544345423612245)
            ·
              refine ⟨30094695446907261983239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10272322712544345423612245 30094695446907261983239)
              ·
                rfl

theorem cell23_4747346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 10].length) (baseStart_4747346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747346 prefixEnd_4747346 := by exact prefixLift 4747346
  have htrace : WordTrace (prefixWord ++ tailWord_4747346) baseStart_4747346 baseEnd_4747346 := by
    simpa [prefixWord, tailWord_4747346, baseEnd_4747346] using wordTrace_append hprefix tailTrace_4747346
  have hstable : (prefixWord ++ tailWord_4747346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747346).length < 2 ^ (prefixWord ++ tailWord_4747346).sum := by decide
  have hdescent : baseEnd_4747346 < baseStart_4747346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747357 : List Nat := [1, 4, 4, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_4747357 : Nat := 118140960795 + 4747357 * 2 ^ 59
def prefixEnd_4747357 : Nat := 4983230072969 + 3 ^ 40 * 4747357 * 2
def baseEnd_4747357 : Nat := 2437675979486687677604809

theorem tailTrace_4747357 : CollatzResearch.WordTrace tailWord_4747357 prefixEnd_4747357 2437675979486687677604809 := by
  unfold tailWord_4747357
  simp only [CollatzResearch.WordTrace]
  refine ⟨173150334662143847870896325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115433556441429231913930883 173150334662143847870896325)
  ·
    refine ⟨32465687749151971475793061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173150334662143847870896325 32465687749151971475793061)
    ·
      refine ⟨6087316452965994651711199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32465687749151971475793061 6087316452965994651711199)
      ·
        refine ⟨9130974679448991977566799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6087316452965994651711199 9130974679448991977566799)
        ·
          refine ⟨13696462019173487966350199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9130974679448991977566799 13696462019173487966350199)
          ·
            refine ⟨20544693028760231949525299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13696462019173487966350199 20544693028760231949525299)
            ·
              refine ⟨30817039543140347924287949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20544693028760231949525299 30817039543140347924287949)
              ·
                refine ⟨11556389828677630471607981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30817039543140347924287949 11556389828677630471607981)
                ·
                  refine ⟨4333646185754111426852993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11556389828677630471607981 4333646185754111426852993)
                  ·
                    refine ⟨3250234639315583570139745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4333646185754111426852993 3250234639315583570139745)
                    ·
                      refine ⟨2437675979486687677604809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3250234639315583570139745 2437675979486687677604809)
                      ·
                        rfl

theorem cell23_4747357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_4747357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747357 prefixEnd_4747357 := by exact prefixLift 4747357
  have htrace : WordTrace (prefixWord ++ tailWord_4747357) baseStart_4747357 baseEnd_4747357 := by
    simpa [prefixWord, tailWord_4747357, baseEnd_4747357] using wordTrace_append hprefix tailTrace_4747357
  have hstable : (prefixWord ++ tailWord_4747357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747357).length < 2 ^ (prefixWord ++ tailWord_4747357).sum := by decide
  have hdescent : baseEnd_4747357 < baseStart_4747357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747359 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 2, 7]
def baseStart_4747359 : Nat := 118140960795 + 4747359 * 2 ^ 59
def prefixEnd_4747359 : Nat := 4983230072969 + 3 ^ 40 * 4747359 * 2
def baseEnd_4747359 : Nat := 812559002149332223259933

theorem tailTrace_4747359 : CollatzResearch.WordTrace tailWord_4747359 prefixEnd_4747359 812559002149332223259933 := by
  unfold tailWord_4747359
  simp only [CollatzResearch.WordTrace]
  refine ⟨173150407608136602212469131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115433605072091068141646087 173150407608136602212469131)
  ·
    refine ⟨259725611412204903318703697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173150407608136602212469131 259725611412204903318703697)
    ·
      refine ⟨194794208559153677489027773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259725611412204903318703697 194794208559153677489027773)
      ·
        refine ⟨73047828209682629058385415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194794208559153677489027773 73047828209682629058385415)
        ·
          refine ⟨109571742314523943587578123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73047828209682629058385415 109571742314523943587578123)
          ·
            refine ⟨164357613471785915381367185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109571742314523943587578123 164357613471785915381367185)
            ·
              refine ⟨123268210103839436536025389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164357613471785915381367185 123268210103839436536025389)
              ·
                refine ⟨46225578788939788701009521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123268210103839436536025389 46225578788939788701009521)
                ·
                  refine ⟨34669184091704841525757141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46225578788939788701009521 34669184091704841525757141)
                  ·
                    refine ⟨812559002149332223259933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34669184091704841525757141 812559002149332223259933)
                    ·
                      rfl

theorem cell23_4747359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 7].length) (baseStart_4747359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747359 prefixEnd_4747359 := by exact prefixLift 4747359
  have htrace : WordTrace (prefixWord ++ tailWord_4747359) baseStart_4747359 baseEnd_4747359 := by
    simpa [prefixWord, tailWord_4747359, baseEnd_4747359] using wordTrace_append hprefix tailTrace_4747359
  have hstable : (prefixWord ++ tailWord_4747359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747359).length < 2 ^ (prefixWord ++ tailWord_4747359).sum := by decide
  have hdescent : baseEnd_4747359 < baseStart_4747359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747370 : List Nat := [3, 1, 3, 2, 3, 2, 1, 1, 1, 2, 4]
def baseStart_4747370 : Nat := 118140960795 + 4747370 * 2 ^ 59
def prefixEnd_4747370 : Nat := 4983230072969 + 3 ^ 40 * 4747370 * 2
def baseEnd_4747370 : Nat := 2437682654735196126742249

theorem tailTrace_4747370 : CollatzResearch.WordTrace tailWord_4747370 prefixEnd_4747370 2437682654735196126742249 := by
  unfold tailWord_4747370
  simp only [CollatzResearch.WordTrace]
  refine ⟨43287702202774187772779891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115433872540731167394079709 43287702202774187772779891)
  ·
    refine ⟨64931553304161281659169837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43287702202774187772779891 64931553304161281659169837)
    ·
      refine ⟨24349332489060480622188689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64931553304161281659169837 24349332489060480622188689)
      ·
        refine ⟨18261999366795360466641517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24349332489060480622188689 18261999366795360466641517)
        ·
          refine ⟨6848249762548260174990569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18261999366795360466641517 6848249762548260174990569)
          ·
            refine ⟨5136187321911195131242927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6848249762548260174990569 5136187321911195131242927)
            ·
              refine ⟨7704280982866792696864391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5136187321911195131242927 7704280982866792696864391)
              ·
                refine ⟨11556421474300189045296587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7704280982866792696864391 11556421474300189045296587)
                ·
                  refine ⟨17334632211450283567944881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11556421474300189045296587 17334632211450283567944881)
                  ·
                    refine ⟨13000974158587712675958661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17334632211450283567944881 13000974158587712675958661)
                    ·
                      refine ⟨2437682654735196126742249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13000974158587712675958661 2437682654735196126742249)
                      ·
                        rfl

theorem cell23_4747370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_4747370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747370 prefixEnd_4747370 := by exact prefixLift 4747370
  have htrace : WordTrace (prefixWord ++ tailWord_4747370) baseStart_4747370 baseEnd_4747370 := by
    simpa [prefixWord, tailWord_4747370, baseEnd_4747370] using wordTrace_append hprefix tailTrace_4747370
  have hstable : (prefixWord ++ tailWord_4747370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747370).length < 2 ^ (prefixWord ++ tailWord_4747370).sum := by decide
  have hdescent : baseEnd_4747370 < baseStart_4747370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747414 : List Nat := [5, 3, 2, 1, 1, 1, 2, 8]
def baseStart_4747414 : Nat := 118140960795 + 4747414 * 2 ^ 59
def prefixEnd_4747414 : Nat := 4983230072969 + 3 ^ 40 * 4747414 * 2
def baseEnd_4747414 : Nat := 90285379551259035355261

theorem tailTrace_4747414 : CollatzResearch.WordTrace tailWord_4747414 prefixEnd_4747414 90285379551259035355261 := by
  unfold tailWord_4747414
  simp only [CollatzResearch.WordTrace]
  refine ⟨10822025851433584162857581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115434942415291564403814197 10822025851433584162857581)
  ·
    refine ⟨4058259694287594061071593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10822025851433584162857581 4058259694287594061071593)
    ·
      refine ⟨3043694770715695545803695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4058259694287594061071593 3043694770715695545803695)
      ·
        refine ⟨4565542156073543318705543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3043694770715695545803695 4565542156073543318705543)
        ·
          refine ⟨6848313234110314978058315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4565542156073543318705543 6848313234110314978058315)
          ·
            refine ⟨10272469851165472467087473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6848313234110314978058315 10272469851165472467087473)
            ·
              refine ⟨7704352388374104350315605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10272469851165472467087473 7704352388374104350315605)
              ·
                refine ⟨90285379551259035355261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7704352388374104350315605 90285379551259035355261)
                ·
                  rfl

theorem cell23_4747414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_4747414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747414 prefixEnd_4747414 := by exact prefixLift 4747414
  have htrace : WordTrace (prefixWord ++ tailWord_4747414) baseStart_4747414 baseEnd_4747414 := by
    simpa [prefixWord, tailWord_4747414, baseEnd_4747414] using wordTrace_append hprefix tailTrace_4747414
  have hstable : (prefixWord ++ tailWord_4747414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747414).length < 2 ^ (prefixWord ++ tailWord_4747414).sum := by decide
  have hdescent : baseEnd_4747414 < baseStart_4747414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747419 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 11]
def baseStart_4747419 : Nat := 118140960795 + 4747419 * 2 ^ 59
def prefixEnd_4747419 : Nat := 4983230072969 + 3 ^ 40 * 4747419 * 2
def baseEnd_4747419 : Nat := 270856423920807381669947

theorem tailTrace_4747419 : CollatzResearch.WordTrace tailWord_4747419 prefixEnd_4747419 270856423920807381669947 := by
  unfold tailWord_4747419
  simp only [CollatzResearch.WordTrace]
  refine ⟨173152595987919232459653311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115435063991946154973102207 173152595987919232459653311)
  ·
    refine ⟨259728893981878848689479967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173152595987919232459653311 259728893981878848689479967)
    ·
      refine ⟨389593340972818273034219951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259728893981878848689479967 389593340972818273034219951)
      ·
        refine ⟨584390011459227409551329927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389593340972818273034219951 584390011459227409551329927)
        ·
          refine ⟨876585017188841114326994891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 584390011459227409551329927 876585017188841114326994891)
          ·
            refine ⟨1314877525783261671490492337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876585017188841114326994891 1314877525783261671490492337)
            ·
              refine ⟨986158144337446253617869253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1314877525783261671490492337 986158144337446253617869253)
              ·
                refine ⟨184904652063271172553350485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 986158144337446253617869253 184904652063271172553350485)
                ·
                  refine ⟨270856423920807381669947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 184904652063271172553350485 270856423920807381669947)
                  ·
                    rfl

theorem cell23_4747419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 11].length) (baseStart_4747419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747419 prefixEnd_4747419 := by exact prefixLift 4747419
  have htrace : WordTrace (prefixWord ++ tailWord_4747419) baseStart_4747419 baseEnd_4747419 := by
    simpa [prefixWord, tailWord_4747419, baseEnd_4747419] using wordTrace_append hprefix tailTrace_4747419
  have hstable : (prefixWord ++ tailWord_4747419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747419).length < 2 ^ (prefixWord ++ tailWord_4747419).sum := by decide
  have hdescent : baseEnd_4747419 < baseStart_4747419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747453 : List Nat := [1, 4, 1, 2, 1, 1, 1, 7, 5]
def baseStart_4747453 : Nat := 118140960795 + 4747453 * 2 ^ 59
def prefixEnd_4747453 : Nat := 4983230072969 + 3 ^ 40 * 4747453 * 2
def baseEnd_4747453 : Nat := 270858363736613255778263

theorem tailTrace_4747453 : CollatzResearch.WordTrace tailWord_4747453 prefixEnd_4747453 270858363736613255778263 := by
  unfold tailWord_4747453
  simp only [CollatzResearch.WordTrace]
  refine ⟨173153836069796056266391013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115435890713197370844260675 173153836069796056266391013)
  ·
    refine ⟨32466344263086760549948315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173153836069796056266391013 32466344263086760549948315)
    ·
      refine ⟨48699516394630140824922473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32466344263086760549948315 48699516394630140824922473)
      ·
        refine ⟨36524637295972605618691855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48699516394630140824922473 36524637295972605618691855)
        ·
          refine ⟨54786955943958908428037783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36524637295972605618691855 54786955943958908428037783)
          ·
            refine ⟨82180433915938362642056675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54786955943958908428037783 82180433915938362642056675)
            ·
              refine ⟨123270650873907543963085013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82180433915938362642056675 123270650873907543963085013)
              ·
                refine ⟨2889155879857208061634805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 123270650873907543963085013 2889155879857208061634805)
                ·
                  refine ⟨270858363736613255778263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2889155879857208061634805 270858363736613255778263)
                  ·
                    rfl

theorem cell23_4747453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7, 5].length) (baseStart_4747453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747453 prefixEnd_4747453 := by exact prefixLift 4747453
  have htrace : WordTrace (prefixWord ++ tailWord_4747453) baseStart_4747453 baseEnd_4747453 := by
    simpa [prefixWord, tailWord_4747453, baseEnd_4747453] using wordTrace_append hprefix tailTrace_4747453
  have hstable : (prefixWord ++ tailWord_4747453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747453).length < 2 ^ (prefixWord ++ tailWord_4747453).sum := by decide
  have hdescent : baseEnd_4747453 < baseStart_4747453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747470 : List Nat := [4, 1, 1, 1, 4, 2, 1, 4, 5]
def baseStart_4747470 : Nat := 118140960795 + 4747470 * 2 ^ 59
def prefixEnd_4747470 : Nat := 4983230072969 + 3 ^ 40 * 4747470 * 2
def baseEnd_4747470 : Nat := 270859333644516192832421

theorem tailTrace_4747470 : CollatzResearch.WordTrace tailWord_4747470 prefixEnd_4747470 270859333644516192832421 := by
  unfold tailWord_4747470
  simp only [CollatzResearch.WordTrace]
  refine ⟨21644307013841808521219983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115436304073822978779839909 21644307013841808521219983)
  ·
    refine ⟨32466460520762712781829975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21644307013841808521219983 32466460520762712781829975)
    ·
      refine ⟨48699690781144069172744963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32466460520762712781829975 48699690781144069172744963)
      ·
        refine ⟨73049536171716103759117445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48699690781144069172744963 73049536171716103759117445)
        ·
          refine ⟨13696788032196769454834521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73049536171716103759117445 13696788032196769454834521)
          ·
            refine ⟨10272591024147577091125891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13696788032196769454834521 10272591024147577091125891)
            ·
              refine ⟨15408886536221365636688837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10272591024147577091125891 15408886536221365636688837)
              ·
                refine ⟨2889166225541506056879157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15408886536221365636688837 2889166225541506056879157)
                ·
                  refine ⟨270859333644516192832421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2889166225541506056879157 270859333644516192832421)
                  ·
                    rfl

theorem cell23_4747470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4, 5].length) (baseStart_4747470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747470 prefixEnd_4747470 := by exact prefixLift 4747470
  have htrace : WordTrace (prefixWord ++ tailWord_4747470) baseStart_4747470 baseEnd_4747470 := by
    simpa [prefixWord, tailWord_4747470, baseEnd_4747470] using wordTrace_append hprefix tailTrace_4747470
  have hstable : (prefixWord ++ tailWord_4747470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747470).length < 2 ^ (prefixWord ++ tailWord_4747470).sum := by decide
  have hdescent : baseEnd_4747470 < baseStart_4747470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747473 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 2, 5, 2]
def baseStart_4747473 : Nat := 118140960795 + 4747473 * 2 ^ 59
def prefixEnd_4747473 : Nat := 4983230072969 + 3 ^ 40 * 4747473 * 2
def baseEnd_4747473 : Nat := 2437735543242609223754275

theorem tailTrace_4747473 : CollatzResearch.WordTrace tailWord_4747473 prefixEnd_4747473 2437735543242609223754275 := by
  unfold tailWord_4747473
  simp only [CollatzResearch.WordTrace]
  refine ⟨173154565529723599682119073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115436377019815733121412715 173154565529723599682119073)
  ·
    refine ⟨129865924147292699761589305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173154565529723599682119073 129865924147292699761589305)
    ·
      refine ⟨97399443110469524821191979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129865924147292699761589305 97399443110469524821191979)
      ·
        refine ⟨146099164665704287231787969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97399443110469524821191979 146099164665704287231787969)
        ·
          refine ⟨109574373499278215423840977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146099164665704287231787969 109574373499278215423840977)
          ·
            refine ⟨82180780124458661567880733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109574373499278215423840977 82180780124458661567880733)
            ·
              refine ⟨30817792546671998087955275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82180780124458661567880733 30817792546671998087955275)
              ·
                refine ⟨46226688820007997131932913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30817792546671998087955275 46226688820007997131932913)
                ·
                  refine ⟨34670016615005997848949685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46226688820007997131932913 34670016615005997848949685)
                  ·
                    refine ⟨3250314057656812298339033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34670016615005997848949685 3250314057656812298339033)
                    ·
                      refine ⟨2437735543242609223754275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3250314057656812298339033 2437735543242609223754275)
                      ·
                        rfl

theorem cell23_4747473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 5, 2].length) (baseStart_4747473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747473 prefixEnd_4747473 := by exact prefixLift 4747473
  have htrace : WordTrace (prefixWord ++ tailWord_4747473) baseStart_4747473 baseEnd_4747473 := by
    simpa [prefixWord, tailWord_4747473, baseEnd_4747473] using wordTrace_append hprefix tailTrace_4747473
  have hstable : (prefixWord ++ tailWord_4747473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747473).length < 2 ^ (prefixWord ++ tailWord_4747473).sum := by decide
  have hdescent : baseEnd_4747473 < baseStart_4747473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747503 : List Nat := [1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 4]
def baseStart_4747503 : Nat := 118140960795 + 4747503 * 2 ^ 59
def prefixEnd_4747503 : Nat := 4983230072969 + 3 ^ 40 * 4747503 * 2
def baseEnd_4747503 : Nat := 2437750947662244106379137

theorem tailTrace_4747503 : CollatzResearch.WordTrace tailWord_4747503 prefixEnd_4747503 2437750947662244106379137 := by
  unfold tailWord_4747503
  simp only [CollatzResearch.WordTrace]
  refine ⟨173155659719614914805711163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115437106479743276537140775 173155659719614914805711163)
  ·
    refine ⟨259733489579422372208566745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173155659719614914805711163 259733489579422372208566745)
    ·
      refine ⟨194800117184566779156425059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259733489579422372208566745 194800117184566779156425059)
      ·
        refine ⟨292200175776850168734637589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194800117184566779156425059 292200175776850168734637589)
        ·
          refine ⟨13696883239539851659436137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 292200175776850168734637589 13696883239539851659436137)
          ·
            refine ⟨10272662429654888744577103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13696883239539851659436137 10272662429654888744577103)
            ·
              refine ⟨15408993644482333116865655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10272662429654888744577103 15408993644482333116865655)
              ·
                refine ⟨23113490466723499675298483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15408993644482333116865655 23113490466723499675298483)
                ·
                  refine ⟨34670235700085249512947725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23113490466723499675298483 34670235700085249512947725)
                  ·
                    refine ⟨13001338387531968567355397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34670235700085249512947725 13001338387531968567355397)
                    ·
                      refine ⟨2437750947662244106379137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13001338387531968567355397 2437750947662244106379137)
                      ·
                        rfl

theorem cell23_4747503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 4].length) (baseStart_4747503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747503 prefixEnd_4747503 := by exact prefixLift 4747503
  have htrace : WordTrace (prefixWord ++ tailWord_4747503) baseStart_4747503 baseEnd_4747503 := by
    simpa [prefixWord, tailWord_4747503, baseEnd_4747503] using wordTrace_append hprefix tailTrace_4747503
  have hstable : (prefixWord ++ tailWord_4747503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747503).length < 2 ^ (prefixWord ++ tailWord_4747503).sum := by decide
  have hdescent : baseEnd_4747503 < baseStart_4747503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747523 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 4, 2, 3]
def baseStart_4747523 : Nat := 118140960795 + 4747523 * 2 ^ 59
def prefixEnd_4747523 : Nat := 4983230072969 + 3 ^ 40 * 4747523 * 2
def baseEnd_4747523 : Nat := 2437761217275334028129045

theorem tailTrace_4747523 : CollatzResearch.WordTrace tailWord_4747523 prefixEnd_4747523 2437761217275334028129045 := by
  unfold tailWord_4747523
  simp only [CollatzResearch.WordTrace]
  refine ⟨173156389179542458221439223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115437592786361638814292815 173156389179542458221439223)
  ·
    refine ⟨259734583769313687332158835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173156389179542458221439223 259734583769313687332158835)
    ·
      refine ⟨389601875653970530998238253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259734583769313687332158835 389601875653970530998238253)
      ·
        refine ⟨146100703370238949124339345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 389601875653970530998238253 146100703370238949124339345)
        ·
          refine ⟨109575527527679211843254509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146100703370238949124339345 109575527527679211843254509)
          ·
            refine ⟨41090822822879704441220441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109575527527679211843254509 41090822822879704441220441)
            ·
              refine ⟨30818117117159778330915331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41090822822879704441220441 30818117117159778330915331)
              ·
                refine ⟨46227175675739667496372997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30818117117159778330915331 46227175675739667496372997)
                ·
                  refine ⟨8667595439201187655569937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46227175675739667496372997 8667595439201187655569937)
                  ·
                    refine ⟨6500696579400890741677453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8667595439201187655569937 6500696579400890741677453)
                    ·
                      refine ⟨2437761217275334028129045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6500696579400890741677453 2437761217275334028129045)
                      ·
                        rfl

theorem cell23_4747523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2, 3].length) (baseStart_4747523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747523 prefixEnd_4747523 := by exact prefixLift 4747523
  have htrace : WordTrace (prefixWord ++ tailWord_4747523) baseStart_4747523 baseEnd_4747523 := by
    simpa [prefixWord, tailWord_4747523, baseEnd_4747523] using wordTrace_append hprefix tailTrace_4747523
  have hstable : (prefixWord ++ tailWord_4747523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747523).length < 2 ^ (prefixWord ++ tailWord_4747523).sum := by decide
  have hdescent : baseEnd_4747523 < baseStart_4747523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747587 : List Nat := [1, 1, 1, 3, 1, 3, 2, 6, 1, 1, 3]
def baseStart_4747587 : Nat := 118140960795 + 4747587 * 2 ^ 59
def prefixEnd_4747587 : Nat := 4983230072969 + 3 ^ 40 * 4747587 * 2
def baseEnd_4747587 : Nat := 2437794080037221777728751

theorem tailTrace_4747587 : CollatzResearch.WordTrace tailWord_4747587 prefixEnd_4747587 2437794080037221777728751 := by
  unfold tailWord_4747587
  simp only [CollatzResearch.WordTrace]
  refine ⟨173158723451310597151769015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115439148967540398101179343 173158723451310597151769015)
  ·
    refine ⟨259738085176965895727653523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173158723451310597151769015 259738085176965895727653523)
    ·
      refine ⟨389607127765448843591480285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259738085176965895727653523 389607127765448843591480285)
      ·
        refine ⟨146102672912043316346805107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 389607127765448843591480285 146102672912043316346805107)
        ·
          refine ⟨219154009368064974520207661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146102672912043316346805107 219154009368064974520207661)
          ·
            refine ⟨82182753513024365445077873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 219154009368064974520207661 82182753513024365445077873)
            ·
              refine ⟨61637065134768274083808405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82182753513024365445077873 61637065134768274083808405)
              ·
                refine ⟨2889237428192262847678519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61637065134768274083808405 2889237428192262847678519)
                ·
                  refine ⟨4333856142288394271517779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2889237428192262847678519 4333856142288394271517779)
                  ·
                    refine ⟨6500784213432591407276669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4333856142288394271517779 6500784213432591407276669)
                    ·
                      refine ⟨2437794080037221777728751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6500784213432591407276669 2437794080037221777728751)
                      ·
                        rfl

theorem cell23_4747587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6, 1, 1, 3].length) (baseStart_4747587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747587 prefixEnd_4747587 := by exact prefixLift 4747587
  have htrace : WordTrace (prefixWord ++ tailWord_4747587) baseStart_4747587 baseEnd_4747587 := by
    simpa [prefixWord, tailWord_4747587, baseEnd_4747587] using wordTrace_append hprefix tailTrace_4747587
  have hstable : (prefixWord ++ tailWord_4747587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747587).length < 2 ^ (prefixWord ++ tailWord_4747587).sum := by decide
  have hdescent : baseEnd_4747587 < baseStart_4747587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747593 : List Nat := [1, 2, 1, 1, 2, 3, 1, 4, 3, 1, 4]
def baseStart_4747593 : Nat := 118140960795 + 4747593 * 2 ^ 59
def prefixEnd_4747593 : Nat := 4983230072969 + 3 ^ 40 * 4747593 * 2
def baseEnd_4747593 : Nat := 2437797160921148754253723

theorem tailTrace_4747593 : CollatzResearch.WordTrace tailWord_4747593 prefixEnd_4747593 2437797160921148754253723 := by
  unfold tailWord_4747593
  simp only [CollatzResearch.WordTrace]
  refine ⟨173158942289288860176487433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115439294859525906784324955 173158942289288860176487433)
  ·
    refine ⟨129869206716966645132365575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173158942289288860176487433 129869206716966645132365575)
    ·
      refine ⟨194803810075449967698548363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129869206716966645132365575 194803810075449967698548363)
      ·
        refine ⟨292205715113174951547822545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194803810075449967698548363 292205715113174951547822545)
        ·
          refine ⟨219154286334881213660866909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292205715113174951547822545 219154286334881213660866909)
          ·
            refine ⟨82182857375580455122825091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 219154286334881213660866909 82182857375580455122825091)
            ·
              refine ⟨123274286063370682684237637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82182857375580455122825091 123274286063370682684237637)
              ·
                refine ⟨23113928636882003003294557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123274286063370682684237637 23113928636882003003294557)
                ·
                  refine ⟨8667723238830751126235459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23113928636882003003294557 8667723238830751126235459)
                  ·
                    refine ⟨13001584858246126689353189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8667723238830751126235459 13001584858246126689353189)
                    ·
                      refine ⟨2437797160921148754253723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13001584858246126689353189 2437797160921148754253723)
                      ·
                        rfl

theorem cell23_4747593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 1, 4].length) (baseStart_4747593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747593 prefixEnd_4747593 := by exact prefixLift 4747593
  have htrace : WordTrace (prefixWord ++ tailWord_4747593) baseStart_4747593 baseEnd_4747593 := by
    simpa [prefixWord, tailWord_4747593, baseEnd_4747593] using wordTrace_append hprefix tailTrace_4747593
  have hstable : (prefixWord ++ tailWord_4747593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747593).length < 2 ^ (prefixWord ++ tailWord_4747593).sum := by decide
  have hdescent : baseEnd_4747593 < baseStart_4747593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747603 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 6, 4]
def baseStart_4747603 : Nat := 118140960795 + 4747603 * 2 ^ 59
def prefixEnd_4747603 : Nat := 4983230072969 + 3 ^ 40 * 4747603 * 2
def baseEnd_4747603 : Nat := 812600765242564571709559

theorem tailTrace_4747603 : CollatzResearch.WordTrace tailWord_4747603 prefixEnd_4747603 812600765242564571709559 := by
  unfold tailWord_4747603
  simp only [CollatzResearch.WordTrace]
  refine ⟨173159307019252631884351463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115439538012835087922900975 173159307019252631884351463)
  ·
    refine ⟨259738960528878947826527195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173159307019252631884351463 259738960528878947826527195)
    ·
      refine ⟨389608440793318421739790793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259738960528878947826527195 389608440793318421739790793)
      ·
        refine ⟨292206330594988816304843095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 389608440793318421739790793 292206330594988816304843095)
        ·
          refine ⟨438309495892483224457264643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292206330594988816304843095 438309495892483224457264643)
          ·
            refine ⟨657464243838724836685896965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438309495892483224457264643 657464243838724836685896965)
            ·
              refine ⟨123274545719760906878605681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 657464243838724836685896965 123274545719760906878605681)
              ·
                refine ⟨92455909289820680158954261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123274545719760906878605681 92455909289820680158954261)
                ·
                  refine ⟨4333870747960344382450981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 92455909289820680158954261 4333870747960344382450981)
                  ·
                    refine ⟨812600765242564571709559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4333870747960344382450981 812600765242564571709559)
                    ·
                      rfl

theorem cell23_4747603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6, 4].length) (baseStart_4747603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747603 prefixEnd_4747603 := by exact prefixLift 4747603
  have htrace : WordTrace (prefixWord ++ tailWord_4747603) baseStart_4747603 baseEnd_4747603 := by
    simpa [prefixWord, tailWord_4747603, baseEnd_4747603] using wordTrace_append hprefix tailTrace_4747603
  have hstable : (prefixWord ++ tailWord_4747603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747603).length < 2 ^ (prefixWord ++ tailWord_4747603).sum := by decide
  have hdescent : baseEnd_4747603 < baseStart_4747603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747637 : List Nat := [1, 3, 4, 1, 2, 1, 1, 4, 2, 4]
def baseStart_4747637 : Nat := 118140960795 + 4747637 * 2 ^ 59
def prefixEnd_4747637 : Nat := 4983230072969 + 3 ^ 40 * 4747637 * 2
def baseEnd_4747637 : Nat := 812606584689982194034507

theorem tailTrace_4747637 : CollatzResearch.WordTrace tailWord_4747637 prefixEnd_4747637 812606584689982194034507 := by
  unfold tailWord_4747637
  simp only [CollatzResearch.WordTrace]
  refine ⟨173160547101129455691089165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115440364734086303794059443 173160547101129455691089165)
  ·
    refine ⟨64935205162923545884158437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173160547101129455691089165 64935205162923545884158437)
    ·
      refine ⟨12175350968048164853279707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64935205162923545884158437 12175350968048164853279707)
      ·
        refine ⟨18263026452072247279919561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12175350968048164853279707 18263026452072247279919561)
        ·
          refine ⟨13697269839054185459939671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18263026452072247279919561 13697269839054185459939671)
          ·
            refine ⟨20545904758581278189909507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13697269839054185459939671 20545904758581278189909507)
            ·
              refine ⟨30818857137871917284864261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20545904758581278189909507 30818857137871917284864261)
              ·
                refine ⟨5778535713350984490912049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30818857137871917284864261 5778535713350984490912049)
                ·
                  refine ⟨4333901785013238368184037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5778535713350984490912049 4333901785013238368184037)
                  ·
                    refine ⟨812606584689982194034507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4333901785013238368184037 812606584689982194034507)
                    ·
                      rfl

theorem cell23_4747637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_4747637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747637 prefixEnd_4747637 := by exact prefixLift 4747637
  have htrace : WordTrace (prefixWord ++ tailWord_4747637) baseStart_4747637 baseEnd_4747637 := by
    simpa [prefixWord, tailWord_4747637, baseEnd_4747637] using wordTrace_append hprefix tailTrace_4747637
  have hstable : (prefixWord ++ tailWord_4747637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747637).length < 2 ^ (prefixWord ++ tailWord_4747637).sum := by decide
  have hdescent : baseEnd_4747637 < baseStart_4747637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747638 : List Nat := [5, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3]
def baseStart_4747638 : Nat := 118140960795 + 4747638 * 2 ^ 59
def prefixEnd_4747638 : Nat := 4983230072969 + 3 ^ 40 * 4747638 * 2
def baseEnd_4747638 : Nat := 2437820267550601078191017

theorem tailTrace_4747638 : CollatzResearch.WordTrace tailWord_4747638 prefixEnd_4747638 2437820267550601078191017 := by
  unfold tailWord_4747638
  simp only [CollatzResearch.WordTrace]
  refine ⟨10822536473382864553867223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115440389049417221907917045 10822536473382864553867223)
  ·
    refine ⟨16233804710074296830800835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10822536473382864553867223 16233804710074296830800835)
    ·
      refine ⟨24350707065111445246201253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16233804710074296830800835 24350707065111445246201253)
      ·
        refine ⟨4565757574708395983662735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24350707065111445246201253 4565757574708395983662735)
        ·
          refine ⟨6848636362062593975494103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4565757574708395983662735 6848636362062593975494103)
          ·
            refine ⟨10272954543093890963241155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6848636362062593975494103 10272954543093890963241155)
            ·
              refine ⟨15409431814640836444861733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10272954543093890963241155 15409431814640836444861733)
              ·
                refine ⟨2889268465245156833411575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15409431814640836444861733 2889268465245156833411575)
                ·
                  refine ⟨4333902697867735250117363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2889268465245156833411575 4333902697867735250117363)
                  ·
                    refine ⟨6500854046801602875176045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4333902697867735250117363 6500854046801602875176045)
                    ·
                      refine ⟨2437820267550601078191017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6500854046801602875176045 2437820267550601078191017)
                      ·
                        rfl

theorem cell23_4747638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_4747638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747638 prefixEnd_4747638 := by exact prefixLift 4747638
  have htrace : WordTrace (prefixWord ++ tailWord_4747638) baseStart_4747638 baseEnd_4747638 := by
    simpa [prefixWord, tailWord_4747638, baseEnd_4747638] using wordTrace_append hprefix tailTrace_4747638
  have hstable : (prefixWord ++ tailWord_4747638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747638).length < 2 ^ (prefixWord ++ tailWord_4747638).sum := by decide
  have hdescent : baseEnd_4747638 < baseStart_4747638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747660 : List Nat := [2, 2, 1, 2, 1, 4, 1, 3, 1, 3, 3]
def baseStart_4747660 : Nat := 118140960795 + 4747660 * 2 ^ 59
def prefixEnd_4747660 : Nat := 4983230072969 + 3 ^ 40 * 4747660 * 2
def baseEnd_4747660 : Nat := 2437831564124999992115915

theorem tailTrace_4747660 : CollatzResearch.WordTrace tailWord_4747660 prefixEnd_4747660 2437831564124999992115915 := by
  unfold tailWord_4747660
  simp only [CollatzResearch.WordTrace]
  refine ⟨86580692990023065309588217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115440923986697420412784289 86580692990023065309588217)
  ·
    refine ⟨64935519742517298982191163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86580692990023065309588217 64935519742517298982191163)
    ·
      refine ⟨97403279613775948473286745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64935519742517298982191163 97403279613775948473286745)
      ·
        refine ⟨73052459710331961354965059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97403279613775948473286745 73052459710331961354965059)
        ·
          refine ⟨109578689565497942032447589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73052459710331961354965059 109578689565497942032447589)
          ·
            refine ⟨20546004293530864131083923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109578689565497942032447589 20546004293530864131083923)
            ·
              refine ⟨30819006440296296196625885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20546004293530864131083923 30819006440296296196625885)
              ·
                refine ⟨11557127415111111073734707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30819006440296296196625885 11557127415111111073734707)
                ·
                  refine ⟨17335691122666666610602061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11557127415111111073734707 17335691122666666610602061)
                  ·
                    refine ⟨6500884170999999978975773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17335691122666666610602061 6500884170999999978975773)
                    ·
                      refine ⟨2437831564124999992115915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6500884170999999978975773 2437831564124999992115915)
                      ·
                        rfl

theorem cell23_4747660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_4747660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747660 prefixEnd_4747660 := by exact prefixLift 4747660
  have htrace : WordTrace (prefixWord ++ tailWord_4747660) baseStart_4747660 baseEnd_4747660 := by
    simpa [prefixWord, tailWord_4747660, baseEnd_4747660] using wordTrace_append hprefix tailTrace_4747660
  have hstable : (prefixWord ++ tailWord_4747660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747660).length < 2 ^ (prefixWord ++ tailWord_4747660).sum := by decide
  have hdescent : baseEnd_4747660 < baseStart_4747660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747673 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 2, 2, 5]
def baseStart_4747673 : Nat := 118140960795 + 4747673 * 2 ^ 59
def prefixEnd_4747673 : Nat := 4983230072969 + 3 ^ 40 * 4747673 * 2
def baseEnd_4747673 : Nat := 2437838239373508441253355

theorem tailTrace_4747673 : CollatzResearch.WordTrace tailWord_4747673 prefixEnd_4747673 2437838239373508441253355 := by
  unfold tailWord_4747673
  simp only [CollatzResearch.WordTrace]
  refine ⟨173161860128999033839399673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115441240085999355892933115 173161860128999033839399673)
  ·
    refine ⟨129871395096749275379549755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173161860128999033839399673 129871395096749275379549755)
    ·
      refine ⟨194807092645123913069324633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129871395096749275379549755 194807092645123913069324633)
      ·
        refine ⟨146105319483842934801993475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194807092645123913069324633 146105319483842934801993475)
        ·
          refine ⟨219157979225764402202990213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146105319483842934801993475 219157979225764402202990213)
          ·
            refine ⟨41092121104830825413060665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 219157979225764402202990213 41092121104830825413060665)
            ·
              refine ⟨30819090828623119059795499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41092121104830825413060665 30819090828623119059795499)
              ·
                refine ⟨46228636242934678589693249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30819090828623119059795499 46228636242934678589693249)
                ·
                  refine ⟨34671477182201008942269937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46228636242934678589693249 34671477182201008942269937)
                  ·
                    refine ⟨26003607886650756706702453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34671477182201008942269937 26003607886650756706702453)
                    ·
                      refine ⟨2437838239373508441253355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26003607886650756706702453 2437838239373508441253355)
                      ·
                        rfl

theorem cell23_4747673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_4747673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747673 prefixEnd_4747673 := by exact prefixLift 4747673
  have htrace : WordTrace (prefixWord ++ tailWord_4747673) baseStart_4747673 baseEnd_4747673 := by
    simpa [prefixWord, tailWord_4747673, baseEnd_4747673] using wordTrace_append hprefix tailTrace_4747673
  have hstable : (prefixWord ++ tailWord_4747673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747673).length < 2 ^ (prefixWord ++ tailWord_4747673).sum := by decide
  have hdescent : baseEnd_4747673 < baseStart_4747673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747678 : List Nat := [4, 3, 1, 2, 1, 1, 1, 5, 1, 2, 2]
def baseStart_4747678 : Nat := 118140960795 + 4747678 * 2 ^ 59
def prefixEnd_4747678 : Nat := 4983230072969 + 3 ^ 40 * 4747678 * 2
def baseEnd_4747678 : Nat := 2437840806776780921690833

theorem tailTrace_4747678 : CollatzResearch.WordTrace tailWord_4747678 prefixEnd_4747678 2437840806776780921690833 := by
  unfold tailWord_4747678
  simp only [CollatzResearch.WordTrace]
  refine ⟨21645255311747614961666461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115441361662653946462221125 21645255311747614961666461)
  ·
    refine ⟨8116970741905355610624923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21645255311747614961666461 8116970741905355610624923)
    ·
      refine ⟨12175456112858033415937385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8116970741905355610624923 12175456112858033415937385)
      ·
        refine ⟨9131592084643525061953039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12175456112858033415937385 9131592084643525061953039)
        ·
          refine ⟨13697388126965287592929559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9131592084643525061953039 13697388126965287592929559)
          ·
            refine ⟨20546082190447931389394339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13697388126965287592929559 20546082190447931389394339)
            ·
              refine ⟨30819123285671897084091509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20546082190447931389394339 30819123285671897084091509)
              ·
                refine ⟨2889292808031740351633579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30819123285671897084091509 2889292808031740351633579)
                ·
                  refine ⟨4333939212047610527450369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2889292808031740351633579 4333939212047610527450369)
                  ·
                    refine ⟨3250454409035707895587777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4333939212047610527450369 3250454409035707895587777)
                    ·
                      refine ⟨2437840806776780921690833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3250454409035707895587777 2437840806776780921690833)
                      ·
                        rfl

theorem cell23_4747678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_4747678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747678 prefixEnd_4747678 := by exact prefixLift 4747678
  have htrace : WordTrace (prefixWord ++ tailWord_4747678) baseStart_4747678 baseEnd_4747678 := by
    simpa [prefixWord, tailWord_4747678, baseEnd_4747678] using wordTrace_append hprefix tailTrace_4747678
  have hstable : (prefixWord ++ tailWord_4747678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747678).length < 2 ^ (prefixWord ++ tailWord_4747678).sum := by decide
  have hdescent : baseEnd_4747678 < baseStart_4747678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747710 : List Nat := [4, 2, 1, 1, 1, 1, 4, 1, 2, 6]
def baseStart_4747710 : Nat := 118140960795 + 4747710 * 2 ^ 59
def prefixEnd_4747710 : Nat := 4983230072969 + 3 ^ 40 * 4747710 * 2
def baseEnd_4747710 : Nat := 812619079385908265496895

theorem tailTrace_4747710 : CollatzResearch.WordTrace tailWord_4747710 prefixEnd_4747710 812619079385908265496895 := by
  unfold tailWord_4747710
  simp only [CollatzResearch.WordTrace]
  refine ⟨21645401203733123644812073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115442139753243326105664389 21645401203733123644812073)
  ·
    refine ⟨16234050902799842733609055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21645401203733123644812073 16234050902799842733609055)
    ·
      refine ⟨24351076354199764100413583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16234050902799842733609055 24351076354199764100413583)
      ·
        refine ⟨36526614531299646150620375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24351076354199764100413583 36526614531299646150620375)
        ·
          refine ⟨54789921796949469225930563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36526614531299646150620375 54789921796949469225930563)
          ·
            refine ⟨82184882695424203838895845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54789921796949469225930563 82184882695424203838895845)
            ·
              refine ⟨15409665505392038219792971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82184882695424203838895845 15409665505392038219792971)
              ·
                refine ⟨23114498258088057329689457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15409665505392038219792971 23114498258088057329689457)
                ·
                  refine ⟨17335873693566042997267093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23114498258088057329689457 17335873693566042997267093)
                  ·
                    refine ⟨812619079385908265496895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17335873693566042997267093 812619079385908265496895)
                    ·
                      rfl

theorem cell23_4747710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_4747710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747710 prefixEnd_4747710 := by exact prefixLift 4747710
  have htrace : WordTrace (prefixWord ++ tailWord_4747710) baseStart_4747710 baseEnd_4747710 := by
    simpa [prefixWord, tailWord_4747710, baseEnd_4747710] using wordTrace_append hprefix tailTrace_4747710
  have hstable : (prefixWord ++ tailWord_4747710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747710).length < 2 ^ (prefixWord ++ tailWord_4747710).sum := by decide
  have hdescent : baseEnd_4747710 < baseStart_4747710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747734 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2]
def baseStart_4747734 : Nat := 118140960795 + 4747734 * 2 ^ 59
def prefixEnd_4747734 : Nat := 4983230072969 + 3 ^ 40 * 4747734 * 2
def baseEnd_4747734 : Nat := 2437869561693432702590575

theorem tailTrace_4747734 : CollatzResearch.WordTrace tailWord_4747734 prefixEnd_4747734 2437869561693432702590575 := by
  unfold tailWord_4747734
  simp only [CollatzResearch.WordTrace]
  refine ⟨10822755311361127578585641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115442723321185360838246837 10822755311361127578585641)
  ·
    refine ⟨8117066483520845683939231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10822755311361127578585641 8117066483520845683939231)
    ·
      refine ⟨12175599725281268525908847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8117066483520845683939231 12175599725281268525908847)
      ·
        refine ⟨18263399587921902788863271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12175599725281268525908847 18263399587921902788863271)
        ·
          refine ⟨27395099381882854183294907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18263399587921902788863271 27395099381882854183294907)
          ·
            refine ⟨41092649072824281274942361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27395099381882854183294907 41092649072824281274942361)
            ·
              refine ⟨30819486804618210956206771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41092649072824281274942361 30819486804618210956206771)
              ·
                refine ⟨46229230206927316434310157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30819486804618210956206771 46229230206927316434310157)
                ·
                  refine ⟨17335961327597743662866309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46229230206927316434310157 17335961327597743662866309)
                  ·
                    refine ⟨3250492748924576936787433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17335961327597743662866309 3250492748924576936787433)
                    ·
                      refine ⟨2437869561693432702590575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3250492748924576936787433 2437869561693432702590575)
                      ·
                        rfl

theorem cell23_4747734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_4747734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747734 prefixEnd_4747734 := by exact prefixLift 4747734
  have htrace : WordTrace (prefixWord ++ tailWord_4747734) baseStart_4747734 baseEnd_4747734 := by
    simpa [prefixWord, tailWord_4747734, baseEnd_4747734] using wordTrace_append hprefix tailTrace_4747734
  have hstable : (prefixWord ++ tailWord_4747734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747734).length < 2 ^ (prefixWord ++ tailWord_4747734).sum := by decide
  have hdescent : baseEnd_4747734 < baseStart_4747734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747753 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 3, 7]
def baseStart_4747753 : Nat := 118140960795 + 4747753 * 2 ^ 59
def prefixEnd_4747753 : Nat := 4983230072969 + 3 ^ 40 * 4747753 * 2
def baseEnd_4747753 : Nat := 812626439275289376084329

theorem tailTrace_4747753 : CollatzResearch.WordTrace tailWord_4747753 prefixEnd_4747753 812626439275289376084329 := by
  unfold tailWord_4747753
  simp only [CollatzResearch.WordTrace]
  refine ⟨173164777968709207502311913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115443185312472805001541275 173164777968709207502311913)
  ·
    refine ⟨129873583476531905626733935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173164777968709207502311913 129873583476531905626733935)
    ·
      refine ⟨194810375214797858440100903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129873583476531905626733935 194810375214797858440100903)
      ·
        refine ⟨292215562822196787660151355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194810375214797858440100903 292215562822196787660151355)
        ·
          refine ⟨438323344233295181490227033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292215562822196787660151355 438323344233295181490227033)
          ·
            refine ⟨328742508174971386117670275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 438323344233295181490227033 328742508174971386117670275)
            ·
              refine ⟨493113762262457079176505413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328742508174971386117670275 493113762262457079176505413)
              ·
                refine ⟨92458830424210702345594765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 493113762262457079176505413 92458830424210702345594765)
                ·
                  refine ⟨34672061409079013379598037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92458830424210702345594765 34672061409079013379598037)
                  ·
                    refine ⟨812626439275289376084329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34672061409079013379598037 812626439275289376084329)
                    ·
                      rfl

theorem cell23_4747753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 7].length) (baseStart_4747753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747753 prefixEnd_4747753 := by exact prefixLift 4747753
  have htrace : WordTrace (prefixWord ++ tailWord_4747753) baseStart_4747753 baseEnd_4747753 := by
    simpa [prefixWord, tailWord_4747753, baseEnd_4747753] using wordTrace_append hprefix tailTrace_4747753
  have hstable : (prefixWord ++ tailWord_4747753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747753).length < 2 ^ (prefixWord ++ tailWord_4747753).sum := by decide
  have hdescent : baseEnd_4747753 < baseStart_4747753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747757 : List Nat := [1, 5, 1, 3, 1, 1, 3, 1, 7]
def baseStart_4747757 : Nat := 118140960795 + 4747757 * 2 ^ 59
def prefixEnd_4747757 : Nat := 4983230072969 + 3 ^ 40 * 4747757 * 2
def baseEnd_4747757 : Nat := 270875707972054012511441

theorem tailTrace_4747757 : CollatzResearch.WordTrace tailWord_4747757 prefixEnd_4747757 270875707972054012511441 := by
  unfold tailWord_4747757
  simp only [CollatzResearch.WordTrace]
  refine ⟨173164923860694716185457525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115443282573796477456971683 173164923860694716185457525)
  ·
    refine ⟨16234211611940129642386643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 173164923860694716185457525 16234211611940129642386643)
    ·
      refine ⟨24351317417910194463579965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16234211611940129642386643 24351317417910194463579965)
      ·
        refine ⟨9131744031716322923842487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24351317417910194463579965 9131744031716322923842487)
        ·
          refine ⟨13697616047574484385763731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9131744031716322923842487 13697616047574484385763731)
          ·
            refine ⟨20546424071361726578645597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13697616047574484385763731 20546424071361726578645597)
            ·
              refine ⟨7704909026760647466992099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20546424071361726578645597 7704909026760647466992099)
              ·
                refine ⟨11557363540140971200488149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7704909026760647466992099 11557363540140971200488149)
                ·
                  refine ⟨270875707972054012511441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11557363540140971200488149 270875707972054012511441)
                  ·
                    rfl

theorem cell23_4747757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_4747757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747757 prefixEnd_4747757 := by exact prefixLift 4747757
  have htrace : WordTrace (prefixWord ++ tailWord_4747757) baseStart_4747757 baseEnd_4747757 := by
    simpa [prefixWord, tailWord_4747757, baseEnd_4747757] using wordTrace_append hprefix tailTrace_4747757
  have hstable : (prefixWord ++ tailWord_4747757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747757).length < 2 ^ (prefixWord ++ tailWord_4747757).sum := by decide
  have hdescent : baseEnd_4747757 < baseStart_4747757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747787 : List Nat := [1, 1, 1, 1, 7, 2, 2, 1, 2, 5]
def baseStart_4747787 : Nat := 118140960795 + 4747787 * 2 ^ 59
def prefixEnd_4747787 : Nat := 4983230072969 + 3 ^ 40 * 4747787 * 2
def baseEnd_4747787 : Nat := 812632258722706998409277

theorem tailTrace_4747787 : CollatzResearch.WordTrace tailWord_4747787 prefixEnd_4747787 812632258722706998409277 := by
  unfold tailWord_4747787
  simp only [CollatzResearch.WordTrace]
  refine ⟨173166018050586031309049615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115444012033724020872699743 173166018050586031309049615)
  ·
    refine ⟨259749027075879046963574423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173166018050586031309049615 259749027075879046963574423)
    ·
      refine ⟨389623540613818570445361635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259749027075879046963574423 389623540613818570445361635)
      ·
        refine ⟨584435310920727855668042453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389623540613818570445361635 584435310920727855668042453)
        ·
          refine ⟨13697702599704559117219745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 584435310920727855668042453 13697702599704559117219745)
          ·
            refine ⟨10273276949778419337914809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13697702599704559117219745 10273276949778419337914809)
            ·
              refine ⟨7704957712333814503436107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10273276949778419337914809 7704957712333814503436107)
              ·
                refine ⟨11557436568500721755154161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7704957712333814503436107 11557436568500721755154161)
                ·
                  refine ⟨8668077426375541316365621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11557436568500721755154161 8668077426375541316365621)
                  ·
                    refine ⟨812632258722706998409277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8668077426375541316365621 812632258722706998409277)
                    ·
                      rfl

theorem cell23_4747787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 5].length) (baseStart_4747787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747787 prefixEnd_4747787 := by exact prefixLift 4747787
  have htrace : WordTrace (prefixWord ++ tailWord_4747787) baseStart_4747787 baseEnd_4747787 := by
    simpa [prefixWord, tailWord_4747787, baseEnd_4747787] using wordTrace_append hprefix tailTrace_4747787
  have hstable : (prefixWord ++ tailWord_4747787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747787).length < 2 ^ (prefixWord ++ tailWord_4747787).sum := by decide
  have hdescent : baseEnd_4747787 < baseStart_4747787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747807 : List Nat := [1, 1, 2, 4, 1, 1, 1, 4, 2, 4, 2]
def baseStart_4747807 : Nat := 118140960795 + 4747807 * 2 ^ 59
def prefixEnd_4747807 : Nat := 4983230072969 + 3 ^ 40 * 4747807 * 2
def baseEnd_4747807 : Nat := 2437907045781210916977739

theorem tailTrace_4747807 : CollatzResearch.WordTrace tailWord_4747807 prefixEnd_4747807 2437907045781210916977739 := by
  unfold tailWord_4747807
  simp only [CollatzResearch.WordTrace]
  refine ⟨173166747510513574724777675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115444498340342383149851783 173166747510513574724777675)
  ·
    refine ⟨259750121265770362087166513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173166747510513574724777675 259750121265770362087166513)
    ·
      refine ⟨194812590949327771565374885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259750121265770362087166513 194812590949327771565374885)
      ·
        refine ⟨36527360802998957168507791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 194812590949327771565374885 36527360802998957168507791)
        ·
          refine ⟨54791041204498435752761687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36527360802998957168507791 54791041204498435752761687)
          ·
            refine ⟨82186561806747653629142531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54791041204498435752761687 82186561806747653629142531)
            ·
              refine ⟨123279842710121480443713797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82186561806747653629142531 123279842710121480443713797)
              ·
                refine ⟨23114970508147777583196337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123279842710121480443713797 23114970508147777583196337)
                ·
                  refine ⟨17336227881110833187397253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23114970508147777583196337 17336227881110833187397253)
                  ·
                    refine ⟨3250542727708281222636985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17336227881110833187397253 3250542727708281222636985)
                    ·
                      refine ⟨2437907045781210916977739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3250542727708281222636985 2437907045781210916977739)
                      ·
                        rfl

theorem cell23_4747807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_4747807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747807 prefixEnd_4747807 := by exact prefixLift 4747807
  have htrace : WordTrace (prefixWord ++ tailWord_4747807) baseStart_4747807 baseEnd_4747807 := by
    simpa [prefixWord, tailWord_4747807, baseEnd_4747807] using wordTrace_append hprefix tailTrace_4747807
  have hstable : (prefixWord ++ tailWord_4747807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747807).length < 2 ^ (prefixWord ++ tailWord_4747807).sum := by decide
  have hdescent : baseEnd_4747807 < baseStart_4747807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747808 : List Nat := [2, 1, 1, 6, 3, 1, 2, 2, 5]
def baseStart_4747808 : Nat := 118140960795 + 4747808 * 2 ^ 59
def prefixEnd_4747808 : Nat := 4983230072969 + 3 ^ 40 * 4747808 * 2
def baseEnd_4747808 : Nat := 270878617695762823673915

theorem tailTrace_4747808 : CollatzResearch.WordTrace tailWord_4747808 prefixEnd_4747808 270878617695762823673915 := by
  unfold tailWord_4747808
  simp only [CollatzResearch.WordTrace]
  refine ⟨86583391991754975947782039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115444522655673301263709385 86583391991754975947782039)
  ·
    refine ⟨129875087987632463921673059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86583391991754975947782039 129875087987632463921673059)
    ·
      refine ⟨194812631981448695882509589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129875087987632463921673059 194812631981448695882509589)
      ·
        refine ⟨9131842124130407619492637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 194812631981448695882509589 9131842124130407619492637)
        ·
          refine ⟨3424440796548902857309739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9131842124130407619492637 3424440796548902857309739)
          ·
            refine ⟨5136661194823354285964609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3424440796548902857309739 5136661194823354285964609)
            ·
              refine ⟨3852495896117515714473457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5136661194823354285964609 3852495896117515714473457)
              ·
                refine ⟨2889371922088136785855093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3852495896117515714473457 2889371922088136785855093)
                ·
                  refine ⟨270878617695762823673915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2889371922088136785855093 270878617695762823673915)
                  ·
                    rfl

theorem cell23_4747808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2, 5].length) (baseStart_4747808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747808 prefixEnd_4747808 := by exact prefixLift 4747808
  have htrace : WordTrace (prefixWord ++ tailWord_4747808) baseStart_4747808 baseEnd_4747808 := by
    simpa [prefixWord, tailWord_4747808, baseEnd_4747808] using wordTrace_append hprefix tailTrace_4747808
  have hstable : (prefixWord ++ tailWord_4747808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747808).length < 2 ^ (prefixWord ++ tailWord_4747808).sum := by decide
  have hdescent : baseEnd_4747808 < baseStart_4747808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747810 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_4747810 : Nat := 118140960795 + 4747810 * 2 ^ 59
def prefixEnd_4747810 : Nat := 4983230072969 + 3 ^ 40 * 4747810 * 2
def baseEnd_4747810 : Nat := 2437908586223174405240225

theorem tailTrace_4747810 : CollatzResearch.WordTrace tailWord_4747810 prefixEnd_4747810 2437908586223174405240225 := by
  unfold tailWord_4747810
  simp only [CollatzResearch.WordTrace]
  refine ⟨43291714232375676559284221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115444571286335137491424589 43291714232375676559284221)
  ·
    refine ⟨16234392837140878709731583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43291714232375676559284221 16234392837140878709731583)
    ·
      refine ⟨24351589255711318064597375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16234392837140878709731583 24351589255711318064597375)
      ·
        refine ⟨36527383883566977096896063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24351589255711318064597375 36527383883566977096896063)
        ·
          refine ⟨54791075825350465645344095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36527383883566977096896063 54791075825350465645344095)
          ·
            refine ⟨82186613738025698468016143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54791075825350465645344095 82186613738025698468016143)
            ·
              refine ⟨123279920607038547702024215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82186613738025698468016143 123279920607038547702024215)
              ·
                refine ⟨184919880910557821553036323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123279920607038547702024215 184919880910557821553036323)
                ·
                  refine ⟨277379821365836732329554485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184919880910557821553036323 277379821365836732329554485)
                  ·
                    refine ⟨26004358253047193655895733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 277379821365836732329554485 26004358253047193655895733)
                    ·
                      refine ⟨2437908586223174405240225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26004358253047193655895733 2437908586223174405240225)
                      ·
                        rfl

theorem cell23_4747810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_4747810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747810 prefixEnd_4747810 := by exact prefixLift 4747810
  have htrace : WordTrace (prefixWord ++ tailWord_4747810) baseStart_4747810 baseEnd_4747810 := by
    simpa [prefixWord, tailWord_4747810, baseEnd_4747810] using wordTrace_append hprefix tailTrace_4747810
  have hstable : (prefixWord ++ tailWord_4747810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747810).length < 2 ^ (prefixWord ++ tailWord_4747810).sum := by decide
  have hdescent : baseEnd_4747810 < baseStart_4747810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747838 : List Nat := [4, 2, 1, 4, 2, 1, 1, 1, 2, 5]
def baseStart_4747838 : Nat := 118140960795 + 4747838 * 2 ^ 59
def prefixEnd_4747838 : Nat := 4983230072969 + 3 ^ 40 * 4747838 * 2
def baseEnd_4747838 : Nat := 812640987893833431896699

theorem tailTrace_4747838 : CollatzResearch.WordTrace tailWord_4747838 prefixEnd_4747838 812640987893833431896699 := by
  unfold tailWord_4747838
  simp only [CollatzResearch.WordTrace]
  refine ⟨21645984771675158377394521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115445252115600844679437445 21645984771675158377394521)
  ·
    refine ⟨16234488578756368783045891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21645984771675158377394521 16234488578756368783045891)
    ·
      refine ⟨24351732868134553174568837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16234488578756368783045891 24351732868134553174568837)
      ·
        refine ⟨4565949912775228720231657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24351732868134553174568837 4565949912775228720231657)
        ·
          refine ⟨3424462434581421540173743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4565949912775228720231657 3424462434581421540173743)
          ·
            refine ⟨5136693651872132310260615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3424462434581421540173743 5136693651872132310260615)
            ·
              refine ⟨7705040477808198465390923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5136693651872132310260615 7705040477808198465390923)
              ·
                refine ⟨11557560716712297698086385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7705040477808198465390923 11557560716712297698086385)
                ·
                  refine ⟨8668170537534223273564789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11557560716712297698086385 8668170537534223273564789)
                  ·
                    refine ⟨812640987893833431896699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8668170537534223273564789 812640987893833431896699)
                    ·
                      rfl

theorem cell23_4747838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_4747838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747838 prefixEnd_4747838 := by exact prefixLift 4747838
  have htrace : WordTrace (prefixWord ++ tailWord_4747838) baseStart_4747838 baseEnd_4747838 := by
    simpa [prefixWord, tailWord_4747838, baseEnd_4747838] using wordTrace_append hprefix tailTrace_4747838
  have hstable : (prefixWord ++ tailWord_4747838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747838).length < 2 ^ (prefixWord ++ tailWord_4747838).sum := by decide
  have hdescent : baseEnd_4747838 < baseStart_4747838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747907 : List Nat := [1, 1, 1, 3, 3, 1, 3, 2, 4, 4]
def baseStart_4747907 : Nat := 118140960795 + 4747907 * 2 ^ 59
def prefixEnd_4747907 : Nat := 4983230072969 + 3 ^ 40 * 4747907 * 2
def baseEnd_4747907 : Nat := 812652797948886841909093

theorem tailTrace_4747907 : CollatzResearch.WordTrace tailWord_4747907 prefixEnd_4747907 812652797948886841909093 := by
  unfold tailWord_4747907
  simp only [CollatzResearch.WordTrace]
  refine ⟨173170394810151291803417975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115446929873434194535611983 173170394810151291803417975)
  ·
    refine ⟨259755592215226937705126963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173170394810151291803417975 259755592215226937705126963)
    ·
      refine ⟨389633388322840406557690445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259755592215226937705126963 389633388322840406557690445)
      ·
        refine ⟨146112520621065152459133917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 389633388322840406557690445 146112520621065152459133917)
        ·
          refine ⟨54792195232899432172175219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146112520621065152459133917 54792195232899432172175219)
          ·
            refine ⟨82188292849349148258262829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54792195232899432172175219 82188292849349148258262829)
            ·
              refine ⟨30820609818505930596848561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82188292849349148258262829 30820609818505930596848561)
              ·
                refine ⟨23115457363879447947636421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30820609818505930596848561 23115457363879447947636421)
                ·
                  refine ⟨4334148255727396490181829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23115457363879447947636421 4334148255727396490181829)
                  ·
                    refine ⟨812652797948886841909093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4334148255727396490181829 812652797948886841909093)
                    ·
                      rfl

theorem cell23_4747907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4, 4].length) (baseStart_4747907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747907 prefixEnd_4747907 := by exact prefixLift 4747907
  have htrace : WordTrace (prefixWord ++ tailWord_4747907) baseStart_4747907 baseEnd_4747907 := by
    simpa [prefixWord, tailWord_4747907, baseEnd_4747907] using wordTrace_append hprefix tailTrace_4747907
  have hstable : (prefixWord ++ tailWord_4747907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747907).length < 2 ^ (prefixWord ++ tailWord_4747907).sum := by decide
  have hdescent : baseEnd_4747907 < baseStart_4747907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747908 : List Nat := [2, 3, 2, 1, 3, 1, 3, 3, 1, 1, 3]
def baseStart_4747908 : Nat := 118140960795 + 4747908 * 2 ^ 59
def prefixEnd_4747908 : Nat := 4983230072969 + 3 ^ 40 * 4747908 * 2
def baseEnd_4747908 : Nat := 2437958907327315021814775

theorem tailTrace_4747908 : CollatzResearch.WordTrace tailWord_4747908 prefixEnd_4747908 2437958907327315021814775 := by
  unfold tailWord_4747908
  simp only [CollatzResearch.WordTrace]
  refine ⟨86585215641573834487102189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115446954188765112649469585 86585215641573834487102189)
  ·
    refine ⟨32469455865590187932663321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86585215641573834487102189 32469455865590187932663321)
    ·
      refine ⟨24352091899192640949497491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32469455865590187932663321 24352091899192640949497491)
      ·
        refine ⟨36528137848788961424246237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24352091899192640949497491 36528137848788961424246237)
        ·
          refine ⟨13698051693295860534092339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36528137848788961424246237 13698051693295860534092339)
          ·
            refine ⟨20547077539943790801138509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13698051693295860534092339 20547077539943790801138509)
            ·
              refine ⟨7705154077478921550426941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20547077539943790801138509 7705154077478921550426941)
              ·
                refine ⟨2889432779054595581410103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7705154077478921550426941 2889432779054595581410103)
                ·
                  refine ⟨4334149168581893372115155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2889432779054595581410103 4334149168581893372115155)
                  ·
                    refine ⟨6501223752872840058172733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4334149168581893372115155 6501223752872840058172733)
                    ·
                      refine ⟨2437958907327315021814775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6501223752872840058172733 2437958907327315021814775)
                      ·
                        rfl

theorem cell23_4747908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_4747908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747908 prefixEnd_4747908 := by exact prefixLift 4747908
  have htrace : WordTrace (prefixWord ++ tailWord_4747908) baseStart_4747908 baseEnd_4747908 := by
    simpa [prefixWord, tailWord_4747908, baseEnd_4747908] using wordTrace_append hprefix tailTrace_4747908
  have hstable : (prefixWord ++ tailWord_4747908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747908).length < 2 ^ (prefixWord ++ tailWord_4747908).sum := by decide
  have hdescent : baseEnd_4747908 < baseStart_4747908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747934 : List Nat := [4, 3, 1, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_4747934 : Nat := 118140960795 + 4747934 * 2 ^ 59
def prefixEnd_4747934 : Nat := 4983230072969 + 3 ^ 40 * 4747934 * 2
def baseEnd_4747934 : Nat := 2437972257824331920089655

theorem tailTrace_4747934 : CollatzResearch.WordTrace tailWord_4747934 prefixEnd_4747934 2437972257824331920089655 := by
  unfold tailWord_4747934
  simp only [CollatzResearch.WordTrace]
  refine ⟨21646422447631684426831357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115447586387368983609767237 21646422447631684426831357)
  ·
    refine ⟨8117408417861881660061759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21646422447631684426831357 8117408417861881660061759)
    ·
      refine ⟨12176112626792822490092639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8117408417861881660061759 12176112626792822490092639)
      ·
        refine ⟨18264168940189233735138959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12176112626792822490092639 18264168940189233735138959)
        ·
          refine ⟨27396253410283850602708439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18264168940189233735138959 27396253410283850602708439)
          ·
            refine ⟨41094380115425775904062659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27396253410283850602708439 41094380115425775904062659)
            ·
              refine ⟨61641570173138663856093989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41094380115425775904062659 61641570173138663856093989)
              ·
                refine ⟨11557794407463499473017623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61641570173138663856093989 11557794407463499473017623)
                ·
                  refine ⟨17336691611195249209526435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11557794407463499473017623 17336691611195249209526435)
                  ·
                    refine ⟨26005037416792873814289653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17336691611195249209526435 26005037416792873814289653)
                    ·
                      refine ⟨2437972257824331920089655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26005037416792873814289653 2437972257824331920089655)
                      ·
                        rfl

theorem cell23_4747934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_4747934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747934 prefixEnd_4747934 := by exact prefixLift 4747934
  have htrace : WordTrace (prefixWord ++ tailWord_4747934) baseStart_4747934 baseEnd_4747934 := by
    simpa [prefixWord, tailWord_4747934, baseEnd_4747934] using wordTrace_append hprefix tailTrace_4747934
  have hstable : (prefixWord ++ tailWord_4747934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747934).length < 2 ^ (prefixWord ++ tailWord_4747934).sum := by decide
  have hdescent : baseEnd_4747934 < baseStart_4747934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747951 : List Nat := [1, 1, 2, 1, 2, 7, 1, 2, 1, 2, 3]
def baseStart_4747951 : Nat := 118140960795 + 4747951 * 2 ^ 59
def prefixEnd_4747951 : Nat := 4983230072969 + 3 ^ 40 * 4747951 * 2
def baseEnd_4747951 : Nat := 2437980986995458353577077

theorem tailTrace_4747951 : CollatzResearch.WordTrace tailWord_4747951 prefixEnd_4747951 2437980986995458353577077 := by
  unfold tailWord_4747951
  simp only [CollatzResearch.WordTrace]
  refine ⟨173171999621991887318019707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115447999747994591545346471 173171999621991887318019707)
  ·
    refine ⟨259757999432987830977029561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173171999621991887318019707 259757999432987830977029561)
    ·
      refine ⟨194818499574740873232772171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259757999432987830977029561 194818499574740873232772171)
      ·
        refine ⟨292227749362111309849158257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194818499574740873232772171 292227749362111309849158257)
        ·
          refine ⟨219170812021583482386868693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292227749362111309849158257 219170812021583482386868693)
          ·
            refine ⟨5136815906755862868442235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 219170812021583482386868693 5136815906755862868442235)
            ·
              refine ⟨7705223860133794302663353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5136815906755862868442235 7705223860133794302663353)
              ·
                refine ⟨5778917895100345726997515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7705223860133794302663353 5778917895100345726997515)
                ·
                  refine ⟨8668376842650518590496273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5778917895100345726997515 8668376842650518590496273)
                  ·
                    refine ⟨6501282631987888942872205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8668376842650518590496273 6501282631987888942872205)
                    ·
                      refine ⟨2437980986995458353577077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6501282631987888942872205 2437980986995458353577077)
                      ·
                        rfl

theorem cell23_4747951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 2, 3].length) (baseStart_4747951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747951 prefixEnd_4747951 := by exact prefixLift 4747951
  have htrace : WordTrace (prefixWord ++ tailWord_4747951) baseStart_4747951 baseEnd_4747951 := by
    simpa [prefixWord, tailWord_4747951, baseEnd_4747951] using wordTrace_append hprefix tailTrace_4747951
  have hstable : (prefixWord ++ tailWord_4747951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747951).length < 2 ^ (prefixWord ++ tailWord_4747951).sum := by decide
  have hdescent : baseEnd_4747951 < baseStart_4747951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747964 : List Nat := [2, 2, 2, 3, 1, 1, 3, 2, 1, 3, 3]
def baseStart_4747964 : Nat := 118140960795 + 4747964 * 2 ^ 59
def prefixEnd_4747964 : Nat := 4983230072969 + 3 ^ 40 * 4747964 * 2
def baseEnd_4747964 : Nat := 2437987662243966802714517

theorem tailTrace_4747964 : CollatzResearch.WordTrace tailWord_4747964 prefixEnd_4747964 2437987662243966802714517 := by
  unfold tailWord_4747964
  simp only [CollatzResearch.WordTrace]
  refine ⟨86586236885472395269121473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115448315847296527025495297 86586236885472395269121473)
  ·
    refine ⟨64939677664104296451841105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86586236885472395269121473 64939677664104296451841105)
    ·
      refine ⟨48704758248078222338880829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64939677664104296451841105 48704758248078222338880829)
      ·
        refine ⟨18264284343029333377080311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48704758248078222338880829 18264284343029333377080311)
        ·
          refine ⟨27396426514544000065620467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18264284343029333377080311 27396426514544000065620467)
          ·
            refine ⟨41094639771816000098430701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27396426514544000065620467 41094639771816000098430701)
            ·
              refine ⟨15410489914431000036911513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41094639771816000098430701 15410489914431000036911513)
              ·
                refine ⟨11557867435823250027683635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15410489914431000036911513 11557867435823250027683635)
                ·
                  refine ⟨17336801153734875041525453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11557867435823250027683635 17336801153734875041525453)
                  ·
                    refine ⟨6501300432650578140572045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17336801153734875041525453 6501300432650578140572045)
                    ·
                      refine ⟨2437987662243966802714517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6501300432650578140572045 2437987662243966802714517)
                      ·
                        rfl

theorem cell23_4747964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_4747964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747964 prefixEnd_4747964 := by exact prefixLift 4747964
  have htrace : WordTrace (prefixWord ++ tailWord_4747964) baseStart_4747964 baseEnd_4747964 := by
    simpa [prefixWord, tailWord_4747964, baseEnd_4747964] using wordTrace_append hprefix tailTrace_4747964
  have hstable : (prefixWord ++ tailWord_4747964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747964).length < 2 ^ (prefixWord ++ tailWord_4747964).sum := by decide
  have hdescent : baseEnd_4747964 < baseStart_4747964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4747982 : List Nat := [4, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2]
def baseStart_4747982 : Nat := 118140960795 + 4747982 * 2 ^ 59
def prefixEnd_4747982 : Nat := 4983230072969 + 3 ^ 40 * 4747982 * 2
def baseEnd_4747982 : Nat := 2437996904895747732289435

theorem tailTrace_4747982 : CollatzResearch.WordTrace tailWord_4747982 prefixEnd_4747982 2437996904895747732289435 := by
  unfold tailWord_4747982
  simp only [CollatzResearch.WordTrace]
  refine ⟨21646641285609947451549775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115448753523253053074932133 21646641285609947451549775)
  ·
    refine ⟨32469961928414921177324663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21646641285609947451549775 32469961928414921177324663)
    ·
      refine ⟨48704942892622381765986995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32469961928414921177324663 48704942892622381765986995)
      ·
        refine ⟨73057414338933572648980493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48704942892622381765986995 73057414338933572648980493)
        ·
          refine ⟨27396530377100089743367685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73057414338933572648980493 27396530377100089743367685)
          ·
            refine ⟨5136849445706266826881441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27396530377100089743367685 5136849445706266826881441)
            ·
              refine ⟨3852637084279700120161081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5136849445706266826881441 3852637084279700120161081)
              ·
                refine ⟨2889477813209775090120811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3852637084279700120161081 2889477813209775090120811)
                ·
                  refine ⟨4334216719814662635181217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2889477813209775090120811 4334216719814662635181217)
                  ·
                    refine ⟨3250662539860996976385913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4334216719814662635181217 3250662539860996976385913)
                    ·
                      refine ⟨2437996904895747732289435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3250662539860996976385913 2437996904895747732289435)
                      ·
                        rfl

theorem cell23_4747982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2].length) (baseStart_4747982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4747982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4747982 prefixEnd_4747982 := by exact prefixLift 4747982
  have htrace : WordTrace (prefixWord ++ tailWord_4747982) baseStart_4747982 baseEnd_4747982 := by
    simpa [prefixWord, tailWord_4747982, baseEnd_4747982] using wordTrace_append hprefix tailTrace_4747982
  have hstable : (prefixWord ++ tailWord_4747982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4747982).length < 2 ^ (prefixWord ++ tailWord_4747982).sum := by decide
  have hdescent : baseEnd_4747982 < baseStart_4747982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4747982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748017 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 1, 4, 4]
def baseStart_4748017 : Nat := 118140960795 + 4748017 * 2 ^ 59
def prefixEnd_4748017 : Nat := 4983230072969 + 3 ^ 40 * 4748017 * 2
def baseEnd_4748017 : Nat := 2438014876718655095351773

theorem tailTrace_4748017 : CollatzResearch.WordTrace tailWord_4748017 prefixEnd_4748017 2438014876718655095351773 := by
  unfold tailWord_4748017
  simp only [CollatzResearch.WordTrace]
  refine ⟨173174406839752780589922305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115449604559835187059948203 173174406839752780589922305)
  ·
    refine ⟨129880805129814585442441729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173174406839752780589922305 129880805129814585442441729)
    ·
      refine ⟨97410603847360939081831297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129880805129814585442441729 97410603847360939081831297)
      ·
        refine ⟨73057952885520704311373473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97410603847360939081831297 73057952885520704311373473)
        ·
          refine ⟨54793464664140528233530105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73057952885520704311373473 54793464664140528233530105)
          ·
            refine ⟨41095098498105396175147579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54793464664140528233530105 41095098498105396175147579)
            ·
              refine ⟨61642647747158094262721369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41095098498105396175147579 61642647747158094262721369)
              ·
                refine ⟨46231985810368570697041027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61642647747158094262721369 46231985810368570697041027)
                ·
                  refine ⟨69347978715552856045561541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46231985810368570697041027 69347978715552856045561541)
                  ·
                    refine ⟨13002746009166160508542789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69347978715552856045561541 13002746009166160508542789)
                    ·
                      refine ⟨2438014876718655095351773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13002746009166160508542789 2438014876718655095351773)
                      ·
                        rfl

theorem cell23_4748017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_4748017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748017 prefixEnd_4748017 := by exact prefixLift 4748017
  have htrace : WordTrace (prefixWord ++ tailWord_4748017) baseStart_4748017 baseEnd_4748017 := by
    simpa [prefixWord, tailWord_4748017, baseEnd_4748017] using wordTrace_append hprefix tailTrace_4748017
  have hstable : (prefixWord ++ tailWord_4748017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748017).length < 2 ^ (prefixWord ++ tailWord_4748017).sum := by decide
  have hdescent : baseEnd_4748017 < baseStart_4748017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748055 : List Nat := [1, 1, 3, 4, 4, 1, 1, 1, 1, 4, 2]
def baseStart_4748055 : Nat := 118140960795 + 4748055 * 2 ^ 59
def prefixEnd_4748055 : Nat := 4983230072969 + 3 ^ 40 * 4748055 * 2
def baseEnd_4748055 : Nat := 2438034388983525946676599

theorem tailTrace_4748055 : CollatzResearch.WordTrace tailWord_4748055 prefixEnd_4748055 2438034388983525946676599 := by
  unfold tailWord_4748055
  simp only [CollatzResearch.WordTrace]
  refine ⟨173175792813615113079805619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115450528542410075386537079 173175792813615113079805619)
  ·
    refine ⟨259763689220422669619708429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173175792813615113079805619 259763689220422669619708429)
    ·
      refine ⟨97411383457658501107390661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 259763689220422669619708429 97411383457658501107390661)
      ·
        refine ⟨18264634398310968957635749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97411383457658501107390661 18264634398310968957635749)
        ·
          refine ⟨3424618949683306679556703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18264634398310968957635749 3424618949683306679556703)
          ·
            refine ⟨5136928424524960019335055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3424618949683306679556703 5136928424524960019335055)
            ·
              refine ⟨7705392636787440029002583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5136928424524960019335055 7705392636787440029002583)
              ·
                refine ⟨11558088955181160043503875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7705392636787440029002583 11558088955181160043503875)
                ·
                  refine ⟨17337133432771740065255813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11558088955181160043503875 17337133432771740065255813)
                  ·
                    refine ⟨3250712518644701262235465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17337133432771740065255813 3250712518644701262235465)
                    ·
                      refine ⟨2438034388983525946676599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3250712518644701262235465 2438034388983525946676599)
                      ·
                        rfl

theorem cell23_4748055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_4748055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748055 prefixEnd_4748055 := by exact prefixLift 4748055
  have htrace : WordTrace (prefixWord ++ tailWord_4748055) baseStart_4748055 baseEnd_4748055 := by
    simpa [prefixWord, tailWord_4748055, baseEnd_4748055] using wordTrace_append hprefix tailTrace_4748055
  have hstable : (prefixWord ++ tailWord_4748055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748055).length < 2 ^ (prefixWord ++ tailWord_4748055).sum := by decide
  have hdescent : baseEnd_4748055 < baseStart_4748055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748057 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 6, 5]
def baseStart_4748057 : Nat := 118140960795 + 4748057 * 2 ^ 59
def prefixEnd_4748057 : Nat := 4983230072969 + 3 ^ 40 * 4748057 * 2
def baseEnd_4748057 : Nat := 812678471981611646283863

theorem tailTrace_4748057 : CollatzResearch.WordTrace tailWord_4748057 prefixEnd_4748057 812678471981611646283863 := by
  unfold tailWord_4748057
  simp only [CollatzResearch.WordTrace]
  refine ⟨173175865759607867421378425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115450577173071911614252283 173175865759607867421378425)
  ·
    refine ⟨129881899319705900566033819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173175865759607867421378425 129881899319705900566033819)
    ·
      refine ⟨194822848979558850849050729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129881899319705900566033819 194822848979558850849050729)
      ·
        refine ⟨146117136734669138136788047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194822848979558850849050729 146117136734669138136788047)
        ·
          refine ⟨219175705102003707205182071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146117136734669138136788047 219175705102003707205182071)
          ·
            refine ⟨328763557653005560807773107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219175705102003707205182071 328763557653005560807773107)
            ·
              refine ⟨493145336479508341211659661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328763557653005560807773107 493145336479508341211659661)
              ·
                refine ⟨184929501179815627954372373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 493145336479508341211659661 184929501179815627954372373)
                ·
                  refine ⟨8668570367803857560361205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 184929501179815627954372373 8668570367803857560361205)
                  ·
                    refine ⟨812678471981611646283863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8668570367803857560361205 812678471981611646283863)
                    ·
                      rfl

theorem cell23_4748057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 5].length) (baseStart_4748057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748057 prefixEnd_4748057 := by exact prefixLift 4748057
  have htrace : WordTrace (prefixWord ++ tailWord_4748057) baseStart_4748057 baseEnd_4748057 := by
    simpa [prefixWord, tailWord_4748057, baseEnd_4748057] using wordTrace_append hprefix tailTrace_4748057
  have hstable : (prefixWord ++ tailWord_4748057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748057).length < 2 ^ (prefixWord ++ tailWord_4748057).sum := by decide
  have hdescent : baseEnd_4748057 < baseStart_4748057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748067 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 5]
def baseStart_4748067 : Nat := 118140960795 + 4748067 * 2 ^ 59
def prefixEnd_4748067 : Nat := 4983230072969 + 3 ^ 40 * 4748067 * 2
def baseEnd_4748067 : Nat := 2438040550751379899726543

theorem tailTrace_4748067 : CollatzResearch.WordTrace tailWord_4748067 prefixEnd_4748067 2438040550751379899726543 := by
  unfold tailWord_4748067
  simp only [CollatzResearch.WordTrace]
  refine ⟨173176230489571639129242455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115450820326381092752828303 173176230489571639129242455)
  ·
    refine ⟨259764345734357458693863683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173176230489571639129242455 259764345734357458693863683)
    ·
      refine ⟨389646518601536188040795525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259764345734357458693863683 389646518601536188040795525)
      ·
        refine ⟨73058722237788035257649161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 389646518601536188040795525 73058722237788035257649161)
        ·
          refine ⟨54794041678341026443236871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73058722237788035257649161 54794041678341026443236871)
          ·
            refine ⟨82191062517511539664855307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54794041678341026443236871 82191062517511539664855307)
            ·
              refine ⟨123286593776267309497282961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82191062517511539664855307 123286593776267309497282961)
              ·
                refine ⟨92464945332200482122962221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123286593776267309497282961 92464945332200482122962221)
                ·
                  refine ⟨34674354499575180796110833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92464945332200482122962221 34674354499575180796110833)
                  ·
                    refine ⟨26005765874681385597083125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34674354499575180796110833 26005765874681385597083125)
                    ·
                      refine ⟨2438040550751379899726543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26005765874681385597083125 2438040550751379899726543)
                      ·
                        rfl

theorem cell23_4748067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_4748067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748067 prefixEnd_4748067 := by exact prefixLift 4748067
  have htrace : WordTrace (prefixWord ++ tailWord_4748067) baseStart_4748067 baseEnd_4748067 := by
    simpa [prefixWord, tailWord_4748067, baseEnd_4748067] using wordTrace_append hprefix tailTrace_4748067
  have hstable : (prefixWord ++ tailWord_4748067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748067).length < 2 ^ (prefixWord ++ tailWord_4748067).sum := by decide
  have hdescent : baseEnd_4748067 < baseStart_4748067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748078 : List Nat := [4, 1, 3, 2, 1, 1, 3, 3, 5]
def baseStart_4748078 : Nat := 118140960795 + 4748078 * 2 ^ 59
def prefixEnd_4748078 : Nat := 4983230072969 + 3 ^ 40 * 4748078 * 2
def baseEnd_4748078 : Nat := 270894022115397706298777

theorem tailTrace_4748078 : CollatzResearch.WordTrace tailWord_4748078 prefixEnd_4748078 270894022115397706298777 := by
  unfold tailWord_4748078
  simp only [CollatzResearch.WordTrace]
  refine ⟨21647078961566473500986611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115451087795021192005261925 21647078961566473500986611)
  ·
    refine ⟨32470618442349710251479917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21647078961566473500986611 32470618442349710251479917)
    ·
      refine ⟨12176481915881141344304969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32470618442349710251479917 12176481915881141344304969)
      ·
        refine ⟨9132361436910856008228727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12176481915881141344304969 9132361436910856008228727)
        ·
          refine ⟨13698542155366284012343091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9132361436910856008228727 13698542155366284012343091)
          ·
            refine ⟨20547813233049426018514637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13698542155366284012343091 20547813233049426018514637)
            ·
              refine ⟨7705429962393534756942989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20547813233049426018514637 7705429962393534756942989)
              ·
                refine ⟨2889536235897575533853621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7705429962393534756942989 2889536235897575533853621)
                ·
                  refine ⟨270894022115397706298777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2889536235897575533853621 270894022115397706298777)
                  ·
                    rfl

theorem cell23_4748078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3, 5].length) (baseStart_4748078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748078 prefixEnd_4748078 := by exact prefixLift 4748078
  have htrace : WordTrace (prefixWord ++ tailWord_4748078) baseStart_4748078 baseEnd_4748078 := by
    simpa [prefixWord, tailWord_4748078, baseEnd_4748078] using wordTrace_append hprefix tailTrace_4748078
  have hstable : (prefixWord ++ tailWord_4748078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748078).length < 2 ^ (prefixWord ++ tailWord_4748078).sum := by decide
  have hdescent : baseEnd_4748078 < baseStart_4748078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748131 : List Nat := [1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 3]
def baseStart_4748131 : Nat := 118140960795 + 4748131 * 2 ^ 59
def prefixEnd_4748131 : Nat := 4983230072969 + 3 ^ 40 * 4748131 * 2
def baseEnd_4748131 : Nat := 2438073413513267649326249

theorem tailTrace_4748131 : CollatzResearch.WordTrace tailWord_4748131 prefixEnd_4748131 2438073413513267649326249 := by
  unfold tailWord_4748131
  simp only [CollatzResearch.WordTrace]
  refine ⟨173178564761339778059572247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115452376507559852039714831 173178564761339778059572247)
  ·
    refine ⟨259767847142009667089358371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173178564761339778059572247 259767847142009667089358371)
    ·
      refine ⟨389651770713014500634037557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259767847142009667089358371 389651770713014500634037557)
      ·
        refine ⟨36529853504345109434441021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 389651770713014500634037557 36529853504345109434441021)
        ·
          refine ⟨13698695064129416037915383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36529853504345109434441021 13698695064129416037915383)
          ·
            refine ⟨20548042596194124056873075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13698695064129416037915383 20548042596194124056873075)
            ·
              refine ⟨30822063894291186085309613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20548042596194124056873075 30822063894291186085309613)
              ·
                refine ⟨11558273960359194781991105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30822063894291186085309613 11558273960359194781991105)
                ·
                  refine ⟨8668705470269396086493329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11558273960359194781991105 8668705470269396086493329)
                  ·
                    refine ⟨6501529102702047064869997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8668705470269396086493329 6501529102702047064869997)
                    ·
                      refine ⟨2438073413513267649326249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6501529102702047064869997 2438073413513267649326249)
                      ·
                        rfl

theorem cell23_4748131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_4748131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748131 prefixEnd_4748131 := by exact prefixLift 4748131
  have htrace : WordTrace (prefixWord ++ tailWord_4748131) baseStart_4748131 baseEnd_4748131 := by
    simpa [prefixWord, tailWord_4748131, baseEnd_4748131] using wordTrace_append hprefix tailTrace_4748131
  have hstable : (prefixWord ++ tailWord_4748131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748131).length < 2 ^ (prefixWord ++ tailWord_4748131).sum := by decide
  have hdescent : baseEnd_4748131 < baseStart_4748131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748137 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 8]
def baseStart_4748137 : Nat := 118140960795 + 4748137 * 2 ^ 59
def prefixEnd_4748137 : Nat := 4983230072969 + 3 ^ 40 * 4748137 * 2
def baseEnd_4748137 : Nat := 2438076494397194625851221

theorem tailTrace_4748137 : CollatzResearch.WordTrace tailWord_4748137 prefixEnd_4748137 2438076494397194625851221 := by
  unfold tailWord_4748137
  simp only [CollatzResearch.WordTrace]
  refine ⟨173178783599318041084290665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115452522399545360722860443 173178783599318041084290665)
  ·
    refine ⟨129884087699488530813217999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173178783599318041084290665 129884087699488530813217999)
    ·
      refine ⟨194826131549232796219826999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129884087699488530813217999 194826131549232796219826999)
      ·
        refine ⟨292239197323849194329740499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194826131549232796219826999 292239197323849194329740499)
        ·
          refine ⟨438358795985773791494610749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292239197323849194329740499 438358795985773791494610749)
          ·
            refine ⟨164384548494665171810479031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 438358795985773791494610749 164384548494665171810479031)
            ·
              refine ⟨246576822741997757715718547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164384548494665171810479031 246576822741997757715718547)
              ·
                refine ⟨369865234112996636573577821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246576822741997757715718547 369865234112996636573577821)
                ·
                  refine ⟨138699462792373738715091683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 369865234112996636573577821 138699462792373738715091683)
                  ·
                    refine ⟨208049194188560608072637525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 138699462792373738715091683 208049194188560608072637525)
                    ·
                      refine ⟨2438076494397194625851221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 208049194188560608072637525 2438076494397194625851221)
                      ·
                        rfl

theorem cell23_4748137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_4748137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748137 prefixEnd_4748137 := by exact prefixLift 4748137
  have htrace : WordTrace (prefixWord ++ tailWord_4748137) baseStart_4748137 baseEnd_4748137 := by
    simpa [prefixWord, tailWord_4748137, baseEnd_4748137] using wordTrace_append hprefix tailTrace_4748137
  have hstable : (prefixWord ++ tailWord_4748137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748137).length < 2 ^ (prefixWord ++ tailWord_4748137).sum := by decide
  have hdescent : baseEnd_4748137 < baseStart_4748137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748162 : List Nat := [3, 4, 2, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_4748162 : Nat := 118140960795 + 4748162 * 2 ^ 59
def prefixEnd_4748162 : Nat := 4983230072969 + 3 ^ 40 * 4748162 * 2
def baseEnd_4748162 : Nat := 2438089331413557028038607

theorem tailTrace_4748162 : CollatzResearch.WordTrace tailWord_4748162 prefixEnd_4748162 2438089331413557028038607 := by
  unfold tailWord_4748162
  simp only [CollatzResearch.WordTrace]
  refine ⟨43294923856056867588487685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115453130282818313569300493 43294923856056867588487685)
  ·
    refine ⟨8117798223010662672841441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43294923856056867588487685 8117798223010662672841441)
    ·
      refine ⟨6088348667257997004631081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8117798223010662672841441 6088348667257997004631081)
      ·
        refine ⟨4566261500443497753473311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6088348667257997004631081 4566261500443497753473311)
        ·
          refine ⟨6849392250665246630209967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4566261500443497753473311 6849392250665246630209967)
          ·
            refine ⟨10274088375997869945314951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6849392250665246630209967 10274088375997869945314951)
            ·
              refine ⟨15411132563996804917972427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10274088375997869945314951 15411132563996804917972427)
              ·
                refine ⟨23116698845995207376958641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15411132563996804917972427 23116698845995207376958641)
                ·
                  refine ⟨17337524134496405532718981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23116698845995207376958641 17337524134496405532718981)
                  ·
                    refine ⟨3250785775218076037384809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17337524134496405532718981 3250785775218076037384809)
                    ·
                      refine ⟨2438089331413557028038607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3250785775218076037384809 2438089331413557028038607)
                      ·
                        rfl

theorem cell23_4748162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_4748162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748162 prefixEnd_4748162 := by exact prefixLift 4748162
  have htrace : WordTrace (prefixWord ++ tailWord_4748162) baseStart_4748162 baseEnd_4748162 := by
    simpa [prefixWord, tailWord_4748162, baseEnd_4748162] using wordTrace_append hprefix tailTrace_4748162
  have hstable : (prefixWord ++ tailWord_4748162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748162).length < 2 ^ (prefixWord ++ tailWord_4748162).sum := by decide
  have hdescent : baseEnd_4748162 < baseStart_4748162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748171 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 4, 3, 2]
def baseStart_4748171 : Nat := 118140960795 + 4748171 * 2 ^ 59
def prefixEnd_4748171 : Nat := 4983230072969 + 3 ^ 40 * 4748171 * 2
def baseEnd_4748171 : Nat := 2438093952739447492826065

theorem tailTrace_4748171 : CollatzResearch.WordTrace tailWord_4748171 prefixEnd_4748171 2438093952739447492826065 := by
  unfold tailWord_4748171
  simp only [CollatzResearch.WordTrace]
  refine ⟨173180023681194864891028367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115453349120796576594018911 173180023681194864891028367)
  ·
    refine ⟨259770035521792297336542551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173180023681194864891028367 259770035521792297336542551)
    ·
      refine ⟨389655053282688446004813827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259770035521792297336542551 389655053282688446004813827)
      ·
        refine ⟨584482579924032669007220741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389655053282688446004813827 584482579924032669007220741)
        ·
          refine ⟨109590483735756125438853889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 584482579924032669007220741 109590483735756125438853889)
          ·
            refine ⟨82192862801817094079140417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109590483735756125438853889 82192862801817094079140417)
            ·
              refine ⟨61644647101362820559355313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82192862801817094079140417 61644647101362820559355313)
              ·
                refine ⟨46233485326022115419516485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61644647101362820559355313 46233485326022115419516485)
                ·
                  refine ⟨8668778498629146641159341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46233485326022115419516485 8668778498629146641159341)
                  ·
                    refine ⟨3250791936985929990434753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8668778498629146641159341 3250791936985929990434753)
                    ·
                      refine ⟨2438093952739447492826065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3250791936985929990434753 2438093952739447492826065)
                      ·
                        rfl

theorem cell23_4748171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 3, 2].length) (baseStart_4748171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748171 prefixEnd_4748171 := by exact prefixLift 4748171
  have htrace : WordTrace (prefixWord ++ tailWord_4748171) baseStart_4748171 baseEnd_4748171 := by
    simpa [prefixWord, tailWord_4748171, baseEnd_4748171] using wordTrace_append hprefix tailTrace_4748171
  have hstable : (prefixWord ++ tailWord_4748171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748171).length < 2 ^ (prefixWord ++ tailWord_4748171).sum := by decide
  have hdescent : baseEnd_4748171 < baseStart_4748171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748182 : List Nat := [5, 3, 1, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_4748182 : Nat := 118140960795 + 4748182 * 2 ^ 59
def prefixEnd_4748182 : Nat := 4983230072969 + 3 ^ 40 * 4748182 * 2
def baseEnd_4748182 : Nat := 2438099601026646949788515

theorem tailTrace_4748182 : CollatzResearch.WordTrace tailWord_4748182 prefixEnd_4748182 2438099601026646949788515 := by
  unfold tailWord_4748182
  simp only [CollatzResearch.WordTrace]
  refine ⟨10823776555259688360604925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115453616589436675846452533 10823776555259688360604925)
  ·
    refine ⟨4058916208222383135226847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10823776555259688360604925 4058916208222383135226847)
    ·
      refine ⟨6088374312333574702840271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4058916208222383135226847 6088374312333574702840271)
      ·
        refine ⟨9132561468500362054260407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6088374312333574702840271 9132561468500362054260407)
        ·
          refine ⟨13698842202750543081390611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9132561468500362054260407 13698842202750543081390611)
          ·
            refine ⟨20548263304125814622085917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13698842202750543081390611 20548263304125814622085917)
            ·
              refine ⟨7705598739047180483282219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20548263304125814622085917 7705598739047180483282219)
              ·
                refine ⟨11558398108570770724923329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7705598739047180483282219 11558398108570770724923329)
                ·
                  refine ⟨8668798581428078043692497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11558398108570770724923329 8668798581428078043692497)
                  ·
                    refine ⟨6501598936071058532769373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8668798581428078043692497 6501598936071058532769373)
                    ·
                      refine ⟨2438099601026646949788515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6501598936071058532769373 2438099601026646949788515)
                      ·
                        rfl

theorem cell23_4748182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_4748182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748182 prefixEnd_4748182 := by exact prefixLift 4748182
  have htrace : WordTrace (prefixWord ++ tailWord_4748182) baseStart_4748182 baseEnd_4748182 := by
    simpa [prefixWord, tailWord_4748182, baseEnd_4748182] using wordTrace_append hprefix tailTrace_4748182
  have hstable : (prefixWord ++ tailWord_4748182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748182).length < 2 ^ (prefixWord ++ tailWord_4748182).sum := by decide
  have hdescent : baseEnd_4748182 < baseStart_4748182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748201 : List Nat := [1, 2, 1, 1, 1, 1, 7, 3, 1, 1, 4]
def baseStart_4748201 : Nat := 118140960795 + 4748201 * 2 ^ 59
def prefixEnd_4748201 : Nat := 4983230072969 + 3 ^ 40 * 4748201 * 2
def baseEnd_4748201 : Nat := 2438109357159082375450927

theorem tailTrace_4748201 : CollatzResearch.WordTrace tailWord_4748201 prefixEnd_4748201 2438109357159082375450927 := by
  unfold tailWord_4748201
  simp only [CollatzResearch.WordTrace]
  refine ⟨173181117871086180014620457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115454078580724120009746971 173181117871086180014620457)
  ·
    refine ⟨129885838403314635010965343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173181117871086180014620457 129885838403314635010965343)
    ·
      refine ⟨194828757604971952516448015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129885838403314635010965343 194828757604971952516448015)
      ·
        refine ⟨292243136407457928774672023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194828757604971952516448015 292243136407457928774672023)
        ·
          refine ⟨438364704611186893162008035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292243136407457928774672023 438364704611186893162008035)
          ·
            refine ⟨657547056916780339743012053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438364704611186893162008035 657547056916780339743012053)
            ·
              refine ⟨15411259146487039212726845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 657547056916780339743012053 15411259146487039212726845)
              ·
                refine ⟨5779222179932639704772567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15411259146487039212726845 5779222179932639704772567)
                ·
                  refine ⟨8668833269898959557158851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5779222179932639704772567 8668833269898959557158851)
                  ·
                    refine ⟨13003249904848439335738277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8668833269898959557158851 13003249904848439335738277)
                    ·
                      refine ⟨2438109357159082375450927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13003249904848439335738277 2438109357159082375450927)
                      ·
                        rfl

theorem cell23_4748201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 1, 4].length) (baseStart_4748201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748201 prefixEnd_4748201 := by exact prefixLift 4748201
  have htrace : WordTrace (prefixWord ++ tailWord_4748201) baseStart_4748201 baseEnd_4748201 := by
    simpa [prefixWord, tailWord_4748201, baseEnd_4748201] using wordTrace_append hprefix tailTrace_4748201
  have hstable : (prefixWord ++ tailWord_4748201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748201).length < 2 ^ (prefixWord ++ tailWord_4748201).sum := by decide
  have hdescent : baseEnd_4748201 < baseStart_4748201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748211 : List Nat := [1, 1, 1, 2, 3, 1, 2, 6, 2, 4]
def baseStart_4748211 : Nat := 118140960795 + 4748211 * 2 ^ 59
def prefixEnd_4748211 : Nat := 4983230072969 + 3 ^ 40 * 4748211 * 2
def baseEnd_4748211 : Nat := 812704830655209112108627

theorem tailTrace_4748211 : CollatzResearch.WordTrace tailWord_4748211 prefixEnd_4748211 812704830655209112108627 := by
  unfold tailWord_4748211
  simp only [CollatzResearch.WordTrace]
  refine ⟨173181482601049951722484487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115454321734033301148322991 173181482601049951722484487)
  ·
    refine ⟨259772223901574927583726731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173181482601049951722484487 259772223901574927583726731)
    ·
      refine ⟨389658335852362391375590097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259772223901574927583726731 389658335852362391375590097)
      ·
        refine ⟨292243751889271793531692573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 389658335852362391375590097 292243751889271793531692573)
        ·
          refine ⟨109591406958476922574384715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 292243751889271793531692573 109591406958476922574384715)
          ·
            refine ⟨164387110437715383861577073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109591406958476922574384715 164387110437715383861577073)
            ·
              refine ⟨123290332828286537896182805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164387110437715383861577073 123290332828286537896182805)
              ·
                refine ⟨5779234351325931463883569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 123290332828286537896182805 5779234351325931463883569)
                ·
                  refine ⟨4334425763494448597912677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5779234351325931463883569 4334425763494448597912677)
                  ·
                    refine ⟨812704830655209112108627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4334425763494448597912677 812704830655209112108627)
                    ·
                      rfl

theorem cell23_4748211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2, 4].length) (baseStart_4748211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748211 prefixEnd_4748211 := by exact prefixLift 4748211
  have htrace : WordTrace (prefixWord ++ tailWord_4748211) baseStart_4748211 baseEnd_4748211 := by
    simpa [prefixWord, tailWord_4748211, baseEnd_4748211] using wordTrace_append hprefix tailTrace_4748211
  have hstable : (prefixWord ++ tailWord_4748211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748211).length < 2 ^ (prefixWord ++ tailWord_4748211).sum := by decide
  have hdescent : baseEnd_4748211 < baseStart_4748211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748212 : List Nat := [2, 5, 2, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_4748212 : Nat := 118140960795 + 4748212 * 2 ^ 59
def prefixEnd_4748212 : Nat := 4983230072969 + 3 ^ 40 * 4748212 * 2
def baseEnd_4748212 : Nat := 2438115005446281832413377

theorem tailTrace_4748212 : CollatzResearch.WordTrace tailWord_4748212 prefixEnd_4748212 2438115005446281832413377 := by
  unfold tailWord_4748212
  simp only [CollatzResearch.WordTrace]
  refine ⟨86590759537023164446635445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115454346049364219262180593 86590759537023164446635445)
  ·
    refine ⟨8117883706595921666872073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86590759537023164446635445 8117883706595921666872073)
    ·
      refine ⟨6088412779946941250154055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8117883706595921666872073 6088412779946941250154055)
      ·
        refine ⟨9132619169920411875231083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6088412779946941250154055 9132619169920411875231083)
        ·
          refine ⟨13698928754880617812846625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9132619169920411875231083 13698928754880617812846625)
          ·
            refine ⟨10274196566160463359634969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13698928754880617812846625 10274196566160463359634969)
            ·
              refine ⟨7705647424620347519726227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10274196566160463359634969 7705647424620347519726227)
              ·
                refine ⟨11558471136930521279589341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7705647424620347519726227 11558471136930521279589341)
                ·
                  refine ⟨4334426676348945479846003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11558471136930521279589341 4334426676348945479846003)
                  ·
                    refine ⟨6501640014523418219769005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4334426676348945479846003 6501640014523418219769005)
                    ·
                      refine ⟨2438115005446281832413377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6501640014523418219769005 2438115005446281832413377)
                      ·
                        rfl

theorem cell23_4748212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_4748212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748212 prefixEnd_4748212 := by exact prefixLift 4748212
  have htrace : WordTrace (prefixWord ++ tailWord_4748212) baseStart_4748212 baseEnd_4748212 := by
    simpa [prefixWord, tailWord_4748212, baseEnd_4748212] using wordTrace_append hprefix tailTrace_4748212
  have hstable : (prefixWord ++ tailWord_4748212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748212).length < 2 ^ (prefixWord ++ tailWord_4748212).sum := by decide
  have hdescent : baseEnd_4748212 < baseStart_4748212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748231 : List Nat := [1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 4]
def baseStart_4748231 : Nat := 118140960795 + 4748231 * 2 ^ 59
def prefixEnd_4748231 : Nat := 4983230072969 + 3 ^ 40 * 4748231 * 2
def baseEnd_4748231 : Nat := 2438124761578717258075789

theorem tailTrace_4748231 : CollatzResearch.WordTrace tailWord_4748231 prefixEnd_4748231 2438124761578717258075789 := by
  unfold tailWord_4748231
  simp only [CollatzResearch.WordTrace]
  refine ⟨173182212060977495138212547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115454808040651663425475031 173182212060977495138212547)
  ·
    refine ⟨259773318091466242707318821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173182212060977495138212547 259773318091466242707318821)
    ·
      refine ⟨48707497142149920507622279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 259773318091466242707318821 48707497142149920507622279)
      ·
        refine ⟨73061245713224880761433419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48707497142149920507622279 73061245713224880761433419)
        ·
          refine ⟨109591868569837321142150129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73061245713224880761433419 109591868569837321142150129)
          ·
            refine ⟨82193901427377990856612597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109591868569837321142150129 82193901427377990856612597)
            ·
              refine ⟨7705678258816686642807431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82193901427377990856612597 7705678258816686642807431)
              ·
                refine ⟨11558517388225029964211147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7705678258816686642807431 11558517388225029964211147)
                ·
                  refine ⟨17337776082337544946316721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11558517388225029964211147 17337776082337544946316721)
                  ·
                    refine ⟨13003332061753158709737541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17337776082337544946316721 13003332061753158709737541)
                    ·
                      refine ⟨2438124761578717258075789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13003332061753158709737541 2438124761578717258075789)
                      ·
                        rfl

theorem cell23_4748231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_4748231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748231 prefixEnd_4748231 := by exact prefixLift 4748231
  have htrace : WordTrace (prefixWord ++ tailWord_4748231) baseStart_4748231 baseEnd_4748231 := by
    simpa [prefixWord, tailWord_4748231, baseEnd_4748231] using wordTrace_append hprefix tailTrace_4748231
  have hstable : (prefixWord ++ tailWord_4748231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748231).length < 2 ^ (prefixWord ++ tailWord_4748231).sum := by decide
  have hdescent : baseEnd_4748231 < baseStart_4748231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748238 : List Nat := [4, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3]
def baseStart_4748238 : Nat := 118140960795 + 4748238 * 2 ^ 59
def prefixEnd_4748238 : Nat := 4983230072969 + 3 ^ 40 * 4748238 * 2
def baseEnd_4748238 : Nat := 2438128355943298730688257

theorem tailTrace_4748238 : CollatzResearch.WordTrace tailWord_4748238 prefixEnd_4748238 2438128355943298730688257 := by
  unfold tailWord_4748238
  simp only [CollatzResearch.WordTrace]
  refine ⟨21647808421494016916714671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115454978247968090222478245 21647808421494016916714671)
  ·
    refine ⟨32471712632241025375072007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21647808421494016916714671 32471712632241025375072007)
    ·
      refine ⟨48707568948361538062608011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32471712632241025375072007 48707568948361538062608011)
      ·
        refine ⟨73061353422542307093912017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48707568948361538062608011 73061353422542307093912017)
        ·
          refine ⟨54796015066906730320434013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73061353422542307093912017 54796015066906730320434013)
          ·
            refine ⟨20548505650090023870162755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54796015066906730320434013 20548505650090023870162755)
            ·
              refine ⟨30822758475135035805244133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20548505650090023870162755 30822758475135035805244133)
              ·
                refine ⟨5779267214087819213483275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30822758475135035805244133 5779267214087819213483275)
                ·
                  refine ⟨8668900821131728820224913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5779267214087819213483275 8668900821131728820224913)
                  ·
                    refine ⟨6501675615848796615168685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8668900821131728820224913 6501675615848796615168685)
                    ·
                      refine ⟨2438128355943298730688257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6501675615848796615168685 2438128355943298730688257)
                      ·
                        rfl

theorem cell23_4748238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_4748238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748238 prefixEnd_4748238 := by exact prefixLift 4748238
  have htrace : WordTrace (prefixWord ++ tailWord_4748238) baseStart_4748238 baseEnd_4748238 := by
    simpa [prefixWord, tailWord_4748238, baseEnd_4748238] using wordTrace_append hprefix tailTrace_4748238
  have hstable : (prefixWord ++ tailWord_4748238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748238).length < 2 ^ (prefixWord ++ tailWord_4748238).sum := by decide
  have hdescent : baseEnd_4748238 < baseStart_4748238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748258 : List Nat := [3, 3, 3, 1, 1, 3, 9]
def baseStart_4748258 : Nat := 118140960795 + 4748258 * 2 ^ 59
def prefixEnd_4748258 : Nat := 4983230072969 + 3 ^ 40 * 4748258 * 2
def baseEnd_4748258 : Nat := 30100476858720847560965

theorem tailTrace_4748258 : CollatzResearch.WordTrace tailWord_4748258 prefixEnd_4748258 30100476858720847560965 := by
  unfold tailWord_4748258
  simp only [CollatzResearch.WordTrace]
  refine ⟨43295799207969919687361357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115455464554586452499630285 43295799207969919687361357)
  ·
    refine ⟨16235924702988719882760509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43295799207969919687361357 16235924702988719882760509)
    ·
      refine ⟨6088471763620769956035191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16235924702988719882760509 6088471763620769956035191)
      ·
        refine ⟨9132707645431154934052787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6088471763620769956035191 9132707645431154934052787)
        ·
          refine ⟨13699061468146732401079181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9132707645431154934052787 13699061468146732401079181)
          ·
            refine ⟨5137148050555024650404693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13699061468146732401079181 5137148050555024650404693)
            ·
              refine ⟨30100476858720847560965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5137148050555024650404693 30100476858720847560965)
              ·
                rfl

theorem cell23_4748258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 9].length) (baseStart_4748258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748258 prefixEnd_4748258 := by exact prefixLift 4748258
  have htrace : WordTrace (prefixWord ++ tailWord_4748258) baseStart_4748258 baseEnd_4748258 := by
    simpa [prefixWord, tailWord_4748258, baseEnd_4748258] using wordTrace_append hprefix tailTrace_4748258
  have hstable : (prefixWord ++ tailWord_4748258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748258).length < 2 ^ (prefixWord ++ tailWord_4748258).sum := by decide
  have hdescent : baseEnd_4748258 < baseStart_4748258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748306 : List Nat := [3, 2, 5, 1, 1, 1, 3, 1, 1, 2, 3]
def baseStart_4748306 : Nat := 118140960795 + 4748306 * 2 ^ 59
def prefixEnd_4748306 : Nat := 4983230072969 + 3 ^ 40 * 4748306 * 2
def baseEnd_4748306 : Nat := 2438163272627804464637945

theorem tailTrace_4748306 : CollatzResearch.WordTrace tailWord_4748306 prefixEnd_4748306 2438163272627804464637945 := by
  unfold tailWord_4748306
  simp only [CollatzResearch.WordTrace]
  refine ⟨43296236883926445736798193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115456631690470521964795181 43296236883926445736798193)
  ·
    refine ⟨32472177662944834302598645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43296236883926445736798193 32472177662944834302598645)
    ·
      refine ⟨3044266655901078215868623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32472177662944834302598645 3044266655901078215868623)
      ·
        refine ⟨4566399983851617323802935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3044266655901078215868623 4566399983851617323802935)
        ·
          refine ⟨6849599975777425985704403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4566399983851617323802935 6849599975777425985704403)
          ·
            refine ⟨10274399963666138978556605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6849599975777425985704403 10274399963666138978556605)
            ·
              refine ⟨3852899986374802116958727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10274399963666138978556605 3852899986374802116958727)
              ·
                refine ⟨5779349979562203175438091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3852899986374802116958727 5779349979562203175438091)
                ·
                  refine ⟨8669024969343304763157137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5779349979562203175438091 8669024969343304763157137)
                  ·
                    refine ⟨6501768727007478572367853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8669024969343304763157137 6501768727007478572367853)
                    ·
                      refine ⟨2438163272627804464637945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6501768727007478572367853 2438163272627804464637945)
                      ·
                        rfl

theorem cell23_4748306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_4748306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748306 prefixEnd_4748306 := by exact prefixLift 4748306
  have htrace : WordTrace (prefixWord ++ tailWord_4748306) baseStart_4748306 baseEnd_4748306 := by
    simpa [prefixWord, tailWord_4748306, baseEnd_4748306] using wordTrace_append hprefix tailTrace_4748306
  have hstable : (prefixWord ++ tailWord_4748306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748306).length < 2 ^ (prefixWord ++ tailWord_4748306).sum := by decide
  have hdescent : baseEnd_4748306 < baseStart_4748306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748312 : List Nat := [2, 1, 2, 3, 2, 3, 3, 1, 1, 3, 2]
def baseStart_4748312 : Nat := 118140960795 + 4748312 * 2 ^ 59
def prefixEnd_4748312 : Nat := 4983230072969 + 3 ^ 40 * 4748312 * 2
def baseEnd_4748312 : Nat := 2438166353511731441162917

theorem tailTrace_4748312 : CollatzResearch.WordTrace tailWord_4748312 prefixEnd_4748312 2438166353511731441162917 := by
  unfold tailWord_4748312
  simp only [CollatzResearch.WordTrace]
  refine ⟨86592583186842022985955595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115456777582456030647940793 86592583186842022985955595)
  ·
    refine ⟨129888874780263034478933393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86592583186842022985955595 129888874780263034478933393)
    ·
      refine ⟨97416656085197275859200045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129888874780263034478933393 97416656085197275859200045)
      ·
        refine ⟨36531246031948978447200017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97416656085197275859200045 36531246031948978447200017)
        ·
          refine ⟨27398434523961733835400013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36531246031948978447200017 27398434523961733835400013)
          ·
            refine ⟨10274412946485650188275005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27398434523961733835400013 10274412946485650188275005)
            ·
              refine ⟨3852904854932118820603127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10274412946485650188275005 3852904854932118820603127)
              ·
                refine ⟨5779357282398178230904691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3852904854932118820603127 5779357282398178230904691)
                ·
                  refine ⟨8669035923597267346357037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5779357282398178230904691 8669035923597267346357037)
                  ·
                    refine ⟨3250888471348975254883889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8669035923597267346357037 3250888471348975254883889)
                    ·
                      refine ⟨2438166353511731441162917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3250888471348975254883889 2438166353511731441162917)
                      ·
                        rfl

theorem cell23_4748312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_4748312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748312 prefixEnd_4748312 := by exact prefixLift 4748312
  have htrace : WordTrace (prefixWord ++ tailWord_4748312) baseStart_4748312 baseEnd_4748312 := by
    simpa [prefixWord, tailWord_4748312, baseEnd_4748312] using wordTrace_append hprefix tailTrace_4748312
  have hstable : (prefixWord ++ tailWord_4748312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748312).length < 2 ^ (prefixWord ++ tailWord_4748312).sum := by decide
  have hdescent : baseEnd_4748312 < baseStart_4748312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748342 : List Nat := [5, 1, 2, 1, 1, 3, 2, 1, 1, 4, 2]
def baseStart_4748342 : Nat := 118140960795 + 4748342 * 2 ^ 59
def prefixEnd_4748342 : Nat := 4983230072969 + 3 ^ 40 * 4748342 * 2
def baseEnd_4748342 : Nat := 2438181757931366323787779

theorem tailTrace_4748342 : CollatzResearch.WordTrace tailWord_4748342 prefixEnd_4748342 2438181757931366323787779 := by
  unfold tailWord_4748342
  simp only [CollatzResearch.WordTrace]
  refine ⟨10824141285223460068468955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115457507042383574063668853 10824141285223460068468955)
  ·
    refine ⟨16236211927835190102703433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10824141285223460068468955 16236211927835190102703433)
    ·
      refine ⟨12177158945876392577027575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16236211927835190102703433 12177158945876392577027575)
      ·
        refine ⟨18265738418814588865541363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12177158945876392577027575 18265738418814588865541363)
        ·
          refine ⟨27398607628221883298312045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18265738418814588865541363 27398607628221883298312045)
          ·
            refine ⟨10274477860583206236867017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27398607628221883298312045 10274477860583206236867017)
            ·
              refine ⟨7705858395437404677650263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10274477860583206236867017 7705858395437404677650263)
              ·
                refine ⟨11558787593156107016475395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7705858395437404677650263 11558787593156107016475395)
                ·
                  refine ⟨17338181389734160524713093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11558787593156107016475395 17338181389734160524713093)
                  ·
                    refine ⟨3250909010575155098383705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17338181389734160524713093 3250909010575155098383705)
                    ·
                      refine ⟨2438181757931366323787779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3250909010575155098383705 2438181757931366323787779)
                      ·
                        rfl

theorem cell23_4748342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_4748342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748342 prefixEnd_4748342 := by exact prefixLift 4748342
  have htrace : WordTrace (prefixWord ++ tailWord_4748342) baseStart_4748342 baseEnd_4748342 := by
    simpa [prefixWord, tailWord_4748342, baseEnd_4748342] using wordTrace_append hprefix tailTrace_4748342
  have hstable : (prefixWord ++ tailWord_4748342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748342).length < 2 ^ (prefixWord ++ tailWord_4748342).sum := by decide
  have hdescent : baseEnd_4748342 < baseStart_4748342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748361 : List Nat := [1, 2, 1, 1, 2, 2, 2, 5, 2, 5]
def baseStart_4748361 : Nat := 118140960795 + 4748361 * 2 ^ 59
def prefixEnd_4748361 : Nat := 4983230072969 + 3 ^ 40 * 4748361 * 2
def baseEnd_4748361 : Nat := 812730504687933916483397

theorem tailTrace_4748361 : CollatzResearch.WordTrace tailWord_4748361 prefixEnd_4748361 812730504687933916483397 := by
  unfold tailWord_4748361
  simp only [CollatzResearch.WordTrace]
  refine ⟨173186953550506527340444937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115457969033671018226963291 173186953550506527340444937)
  ·
    refine ⟨129890215162879895505333703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173186953550506527340444937 129890215162879895505333703)
    ·
      refine ⟨194835322744319843258000555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129890215162879895505333703 194835322744319843258000555)
      ·
        refine ⟨292252984116479764887000833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194835322744319843258000555 292252984116479764887000833)
        ·
          refine ⟨219189738087359823665250625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292252984116479764887000833 219189738087359823665250625)
          ·
            refine ⟨164392303565519867748937969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219189738087359823665250625 164392303565519867748937969)
            ·
              refine ⟨123294227674139900811703477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164392303565519867748937969 123294227674139900811703477)
              ·
                refine ⟨11558833844450615701097201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 123294227674139900811703477 11558833844450615701097201)
                ·
                  refine ⟨8669125383337961775822901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11558833844450615701097201 8669125383337961775822901)
                  ·
                    refine ⟨812730504687933916483397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8669125383337961775822901 812730504687933916483397)
                    ·
                      rfl

theorem cell23_4748361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 5].length) (baseStart_4748361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748361 prefixEnd_4748361 := by exact prefixLift 4748361
  have htrace : WordTrace (prefixWord ++ tailWord_4748361) baseStart_4748361 baseEnd_4748361 := by
    simpa [prefixWord, tailWord_4748361, baseEnd_4748361] using wordTrace_append hprefix tailTrace_4748361
  have hstable : (prefixWord ++ tailWord_4748361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748361).length < 2 ^ (prefixWord ++ tailWord_4748361).sum := by decide
  have hdescent : baseEnd_4748361 < baseStart_4748361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748365 : List Nat := [1, 6, 1, 1, 1, 2, 1, 5, 5]
def baseStart_4748365 : Nat := 118140960795 + 4748365 * 2 ^ 59
def prefixEnd_4748365 : Nat := 4983230072969 + 3 ^ 40 * 4748365 * 2
def baseEnd_4748365 : Nat := 270910396442935525977797

theorem tailTrace_4748365 : CollatzResearch.WordTrace tailWord_4748365 prefixEnd_4748365 270910396442935525977797 := by
  unfold tailWord_4748365
  simp only [CollatzResearch.WordTrace]
  refine ⟨173187099442492036023590549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115458066294994690682393699 173187099442492036023590549)
  ·
    refine ⟨8118145286366814188605807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 173187099442492036023590549 8118145286366814188605807)
    ·
      refine ⟨12177217929550221282908711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8118145286366814188605807 12177217929550221282908711)
      ·
        refine ⟨18265826894325331924363067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12177217929550221282908711 18265826894325331924363067)
        ·
          refine ⟨27398740341487997886544601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18265826894325331924363067 27398740341487997886544601)
          ·
            refine ⟨20549055256115998414908451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27398740341487997886544601 20549055256115998414908451)
            ·
              refine ⟨30823582884173997622362677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20549055256115998414908451 30823582884173997622362677)
              ·
                refine ⟨2889710895391312277096501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30823582884173997622362677 2889710895391312277096501)
                ·
                  refine ⟨270910396442935525977797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2889710895391312277096501 270910396442935525977797)
                  ·
                    rfl

theorem cell23_4748365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_4748365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748365 prefixEnd_4748365 := by exact prefixLift 4748365
  have htrace : WordTrace (prefixWord ++ tailWord_4748365) baseStart_4748365 baseEnd_4748365 := by
    simpa [prefixWord, tailWord_4748365, baseEnd_4748365] using wordTrace_append hprefix tailTrace_4748365
  have hstable : (prefixWord ++ tailWord_4748365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748365).length < 2 ^ (prefixWord ++ tailWord_4748365).sum := by decide
  have hdescent : baseEnd_4748365 < baseStart_4748365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748382 : List Nat := [4, 4, 1, 1, 1, 2, 2, 1, 7]
def baseStart_4748382 : Nat := 118140960795 + 4748382 * 2 ^ 59
def prefixEnd_4748382 : Nat := 4983230072969 + 3 ^ 40 * 4748382 * 2
def baseEnd_4748382 : Nat := 270911366350838463031955

theorem tailTrace_4748382 : CollatzResearch.WordTrace tailWord_4748382 prefixEnd_4748382 270911366350838463031955 := by
  unfold tailWord_4748382
  simp only [CollatzResearch.WordTrace]
  refine ⟨21648464935428805990869925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115458479655620298617972933 21648464935428805990869925)
  ·
    refine ⟨4059087175392901123288111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21648464935428805990869925 4059087175392901123288111)
    ·
      refine ⟨6088630763089351684932167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4059087175392901123288111 6088630763089351684932167)
      ·
        refine ⟨9132946144634027527398251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6088630763089351684932167 9132946144634027527398251)
        ·
          refine ⟨13699419216951041291097377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9132946144634027527398251 13699419216951041291097377)
          ·
            refine ⟨10274564412713280968323033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13699419216951041291097377 10274564412713280968323033)
            ·
              refine ⟨7705923309534960726242275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10274564412713280968323033 7705923309534960726242275)
              ·
                refine ⟨11558884964302441089363413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7705923309534960726242275 11558884964302441089363413)
                ·
                  refine ⟨270911366350838463031955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11558884964302441089363413 270911366350838463031955)
                  ·
                    rfl

theorem cell23_4748382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_4748382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748382 prefixEnd_4748382 := by exact prefixLift 4748382
  have htrace : WordTrace (prefixWord ++ tailWord_4748382) baseStart_4748382 baseEnd_4748382 := by
    simpa [prefixWord, tailWord_4748382, baseEnd_4748382] using wordTrace_append hprefix tailTrace_4748382
  have hstable : (prefixWord ++ tailWord_4748382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748382).length < 2 ^ (prefixWord ++ tailWord_4748382).sum := by decide
  have hdescent : baseEnd_4748382 < baseStart_4748382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748398 : List Nat := [4, 1, 2, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_4748398 : Nat := 118140960795 + 4748398 * 2 ^ 59
def prefixEnd_4748398 : Nat := 4983230072969 + 3 ^ 40 * 4748398 * 2
def baseEnd_4748398 : Nat := 2438210512848018104687521

theorem tailTrace_4748398 : CollatzResearch.WordTrace tailWord_4748398 prefixEnd_4748398 2438210512848018104687521 := by
  unfold tailWord_4748398
  simp only [CollatzResearch.WordTrace]
  refine ⟨21648537881421560332442731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115458868700914988439694565 21648537881421560332442731)
  ·
    refine ⟨32472806822132340498664097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21648537881421560332442731 32472806822132340498664097)
    ·
      refine ⟨24354605116599255373998073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32472806822132340498664097 24354605116599255373998073)
      ·
        refine ⟨18265953837449441530498555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24354605116599255373998073 18265953837449441530498555)
        ·
          refine ⟨27398930756174162295747833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18265953837449441530498555 27398930756174162295747833)
          ·
            refine ⟨20549198067130621721810875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27398930756174162295747833 20549198067130621721810875)
            ·
              refine ⟨30823797100695932582716313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20549198067130621721810875 30823797100695932582716313)
              ·
                refine ⟨23117847825521949437037235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30823797100695932582716313 23117847825521949437037235)
                ·
                  refine ⟨34676771738282924155555853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23117847825521949437037235 34676771738282924155555853)
                  ·
                    refine ⟨13003789401856096558333445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34676771738282924155555853 13003789401856096558333445)
                    ·
                      refine ⟨2438210512848018104687521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13003789401856096558333445 2438210512848018104687521)
                      ·
                        rfl

theorem cell23_4748398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_4748398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748398 prefixEnd_4748398 := by exact prefixLift 4748398
  have htrace : WordTrace (prefixWord ++ tailWord_4748398) baseStart_4748398 baseEnd_4748398 := by
    simpa [prefixWord, tailWord_4748398, baseEnd_4748398] using wordTrace_append hprefix tailTrace_4748398
  have hstable : (prefixWord ++ tailWord_4748398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748398).length < 2 ^ (prefixWord ++ tailWord_4748398).sum := by decide
  have hdescent : baseEnd_4748398 < baseStart_4748398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748408 : List Nat := [2, 1, 2, 1, 1, 1, 6, 2, 3, 4]
def baseStart_4748408 : Nat := 118140960795 + 4748408 * 2 ^ 59
def prefixEnd_4748408 : Nat := 4983230072969 + 3 ^ 40 * 4748408 * 2
def baseEnd_4748408 : Nat := 812738549218187688520825

theorem tailTrace_4748408 : CollatzResearch.WordTrace tailWord_4748408 prefixEnd_4748408 812738549218187688520825 := by
  unfold tailWord_4748408
  simp only [CollatzResearch.WordTrace]
  refine ⟨86594333890668127183702939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115459111854224169578270585 86594333890668127183702939)
  ·
    refine ⟨129891500836002190775554409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86594333890668127183702939 129891500836002190775554409)
    ·
      refine ⟨97418625627001643081665807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129891500836002190775554409 97418625627001643081665807)
      ·
        refine ⟨146127938440502464622498711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97418625627001643081665807 146127938440502464622498711)
        ·
          refine ⟨219191907660753696933748067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146127938440502464622498711 219191907660753696933748067)
          ·
            refine ⟨328787861491130545400622101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219191907660753696933748067 328787861491130545400622101)
            ·
              refine ⟨15411931007396744315654161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 328787861491130545400622101 15411931007396744315654161)
              ·
                refine ⟨11558948255547558236740621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15411931007396744315654161 11558948255547558236740621)
                ·
                  refine ⟨4334605595830334338777733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11558948255547558236740621 4334605595830334338777733)
                  ·
                    refine ⟨812738549218187688520825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4334605595830334338777733 812738549218187688520825)
                    ·
                      rfl

theorem cell23_4748408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 3, 4].length) (baseStart_4748408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748408 prefixEnd_4748408 := by exact prefixLift 4748408
  have htrace : WordTrace (prefixWord ++ tailWord_4748408) baseStart_4748408 baseEnd_4748408 := by
    simpa [prefixWord, tailWord_4748408, baseEnd_4748408] using wordTrace_append hprefix tailTrace_4748408
  have hstable : (prefixWord ++ tailWord_4748408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748408).length < 2 ^ (prefixWord ++ tailWord_4748408).sum := by decide
  have hdescent : baseEnd_4748408 < baseStart_4748408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748442 : List Nat := [3, 1, 1, 5, 1, 3, 1, 1, 3, 4]
def baseStart_4748442 : Nat := 118140960795 + 4748442 * 2 ^ 59
def prefixEnd_4748442 : Nat := 4983230072969 + 3 ^ 40 * 4748442 * 2
def baseEnd_4748442 : Nat := 812744368665605310845773

theorem tailTrace_4748442 : CollatzResearch.WordTrace tailWord_4748442 prefixEnd_4748442 812744368665605310845773 := by
  unfold tailWord_4748442
  simp only [CollatzResearch.WordTrace]
  refine ⟨43297476965803269543535895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115459938575475385449429053 43297476965803269543535895)
  ·
    refine ⟨64946215448704904315303843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43297476965803269543535895 64946215448704904315303843)
    ·
      refine ⟨97419323173057356472955765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64946215448704904315303843 97419323173057356472955765)
      ·
        refine ⟨9133061547474127169339603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97419323173057356472955765 9133061547474127169339603)
        ·
          refine ⟨13699592321211190754009405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9133061547474127169339603 13699592321211190754009405)
          ·
            refine ⟨5137347120454196532753527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13699592321211190754009405 5137347120454196532753527)
            ·
              refine ⟨7706020680681294799130291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5137347120454196532753527 7706020680681294799130291)
              ·
                refine ⟨11559031021021942198695437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7706020680681294799130291 11559031021021942198695437)
                ·
                  refine ⟨4334636632883228324510789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11559031021021942198695437 4334636632883228324510789)
                  ·
                    refine ⟨812744368665605310845773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4334636632883228324510789 812744368665605310845773)
                    ·
                      rfl

theorem cell23_4748442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 3, 4].length) (baseStart_4748442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748442 prefixEnd_4748442 := by exact prefixLift 4748442
  have htrace : WordTrace (prefixWord ++ tailWord_4748442) baseStart_4748442 baseEnd_4748442 := by
    simpa [prefixWord, tailWord_4748442, baseEnd_4748442] using wordTrace_append hprefix tailTrace_4748442
  have hstable : (prefixWord ++ tailWord_4748442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748442).length < 2 ^ (prefixWord ++ tailWord_4748442).sum := by decide
  have hdescent : baseEnd_4748442 < baseStart_4748442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748455 : List Nat := [1, 1, 6, 2, 1, 2, 1, 3, 6]
def baseStart_4748455 : Nat := 118140960795 + 4748455 * 2 ^ 59
def prefixEnd_4748455 : Nat := 4983230072969 + 3 ^ 40 * 4748455 * 2
def baseEnd_4748455 : Nat := 270915531249480486852751

theorem tailTrace_4748455 : CollatzResearch.WordTrace tailWord_4748455 prefixEnd_4748455 270915531249480486852751 := by
  unfold tailWord_4748455
  simp only [CollatzResearch.WordTrace]
  refine ⟨173190382012165981394366819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115460254674777320929577879 173190382012165981394366819)
  ·
    refine ⟨259785573018248972091550229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173190382012165981394366819 259785573018248972091550229)
    ·
      refine ⟨12177448735230420566791417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 259785573018248972091550229 12177448735230420566791417)
      ·
        refine ⟨9133086551422815425093563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12177448735230420566791417 9133086551422815425093563)
        ·
          refine ⟨13699629827134223137640345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9133086551422815425093563 13699629827134223137640345)
          ·
            refine ⟨10274722370350667353230259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13699629827134223137640345 10274722370350667353230259)
            ·
              refine ⟨15412083555526001029845389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10274722370350667353230259 15412083555526001029845389)
              ·
                refine ⟨5779531333322250386192021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15412083555526001029845389 5779531333322250386192021)
                ·
                  refine ⟨270915531249480486852751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5779531333322250386192021 270915531249480486852751)
                  ·
                    rfl

theorem cell23_4748455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 6].length) (baseStart_4748455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748455 prefixEnd_4748455 := by exact prefixLift 4748455
  have htrace : WordTrace (prefixWord ++ tailWord_4748455) baseStart_4748455 baseEnd_4748455 := by
    simpa [prefixWord, tailWord_4748455, baseEnd_4748455] using wordTrace_append hprefix tailTrace_4748455
  have hstable : (prefixWord ++ tailWord_4748455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748455).length < 2 ^ (prefixWord ++ tailWord_4748455).sum := by decide
  have hdescent : baseEnd_4748455 < baseStart_4748455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748498 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 3, 6]
def baseStart_4748498 : Nat := 118140960795 + 4748498 * 2 ^ 59
def prefixEnd_4748498 : Nat := 4983230072969 + 3 ^ 40 * 4748498 * 2
def baseEnd_4748498 : Nat := 812753953637822571145687

theorem tailTrace_4748498 : CollatzResearch.WordTrace tailWord_4748498 prefixEnd_4748498 812753953637822571145687 := by
  unfold tailWord_4748498
  simp only [CollatzResearch.WordTrace]
  refine ⟨43297987587752549934545537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115461300234006799825454765 43297987587752549934545537)
  ·
    refine ⟨32473490690814412450909153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43297987587752549934545537 32473490690814412450909153)
    ·
      refine ⟨24355118018110809338181865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32473490690814412450909153 24355118018110809338181865)
      ·
        refine ⟨18266338513583107003636399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24355118018110809338181865 18266338513583107003636399)
        ·
          refine ⟨27399507770374660505454599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18266338513583107003636399 27399507770374660505454599)
          ·
            refine ⟨41099261655561990758181899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27399507770374660505454599 41099261655561990758181899)
            ·
              refine ⟨61648892483342986137272849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41099261655561990758181899 61648892483342986137272849)
              ·
                refine ⟨46236669362507239602954637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61648892483342986137272849 46236669362507239602954637)
                ·
                  refine ⟨17338751010940214851107989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46236669362507239602954637 17338751010940214851107989)
                  ·
                    refine ⟨812753953637822571145687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17338751010940214851107989 812753953637822571145687)
                    ·
                      rfl

theorem cell23_4748498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_4748498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748498 prefixEnd_4748498 := by exact prefixLift 4748498
  have htrace : WordTrace (prefixWord ++ tailWord_4748498) baseStart_4748498 baseEnd_4748498 := by
    simpa [prefixWord, tailWord_4748498, baseEnd_4748498] using wordTrace_append hprefix tailTrace_4748498
  have hstable : (prefixWord ++ tailWord_4748498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748498).length < 2 ^ (prefixWord ++ tailWord_4748498).sum := by decide
  have hdescent : baseEnd_4748498 < baseStart_4748498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748522 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 5, 2, 2]
def baseStart_4748522 : Nat := 118140960795 + 4748522 * 2 ^ 59
def prefixEnd_4748522 : Nat := 4983230072969 + 3 ^ 40 * 4748522 * 2
def baseEnd_4748522 : Nat := 2438274184449175619536951

theorem tailTrace_4748522 : CollatzResearch.WordTrace tailWord_4748522 prefixEnd_4748522 2438274184449175619536951 := by
  unfold tailWord_4748522
  simp only [CollatzResearch.WordTrace]
  refine ⟨43298206425730812959263955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115461883801948834558037213 43298206425730812959263955)
  ·
    refine ⟨64947309638596219438895933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43298206425730812959263955 64947309638596219438895933)
    ·
      refine ⟨24355241114473582289585975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64947309638596219438895933 24355241114473582289585975)
      ·
        refine ⟨36532861671710373434378963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24355241114473582289585975 36532861671710373434378963)
        ·
          refine ⟨54799292507565560151568445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36532861671710373434378963 54799292507565560151568445)
          ·
            refine ⟨20549734690337085056838167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54799292507565560151568445 20549734690337085056838167)
            ·
              refine ⟨30824602035505627585257251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20549734690337085056838167 30824602035505627585257251)
              ·
                refine ⟨46236903053258441377885877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30824602035505627585257251 46236903053258441377885877)
                ·
                  refine ⟨4334709661242978879176801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46236903053258441377885877 4334709661242978879176801)
                  ·
                    refine ⟨3251032245932234159382601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4334709661242978879176801 3251032245932234159382601)
                    ·
                      refine ⟨2438274184449175619536951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3251032245932234159382601 2438274184449175619536951)
                      ·
                        rfl

theorem cell23_4748522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_4748522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748522 prefixEnd_4748522 := by exact prefixLift 4748522
  have htrace : WordTrace (prefixWord ++ tailWord_4748522) baseStart_4748522 baseEnd_4748522 := by
    simpa [prefixWord, tailWord_4748522, baseEnd_4748522] using wordTrace_append hprefix tailTrace_4748522
  have hstable : (prefixWord ++ tailWord_4748522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748522).length < 2 ^ (prefixWord ++ tailWord_4748522).sum := by decide
  have hdescent : baseEnd_4748522 < baseStart_4748522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748572 : List Nat := [2, 2, 3, 1, 1, 1, 2, 5, 2, 1, 3]
def baseStart_4748572 : Nat := 118140960795 + 4748572 * 2 ^ 59
def prefixEnd_4748572 : Nat := 4983230072969 + 3 ^ 40 * 4748572 * 2
def baseEnd_4748572 : Nat := 2438299858481900423911721

theorem tailTrace_4748572 : CollatzResearch.WordTrace tailWord_4748572 prefixEnd_4748572 2438299858481900423911721 := by
  unfold tailWord_4748572
  simp only [CollatzResearch.WordTrace]
  refine ⟨86597324676371055188187985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115463099568494740250917313 86597324676371055188187985)
  ·
    refine ⟨64947993507278291391140989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86597324676371055188187985 64947993507278291391140989)
    ·
      refine ⟨24355497565229359271677871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64947993507278291391140989 24355497565229359271677871)
      ·
        refine ⟨36533246347844038907516807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24355497565229359271677871 36533246347844038907516807)
        ·
          refine ⟨54799869521766058361275211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36533246347844038907516807 54799869521766058361275211)
          ·
            refine ⟨82199804282649087541912817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54799869521766058361275211 82199804282649087541912817)
            ·
              refine ⟨61649853211986815656434613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82199804282649087541912817 61649853211986815656434613)
              ·
                refine ⟨5779673738623763967790745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61649853211986815656434613 5779673738623763967790745)
                ·
                  refine ⟨4334755303967822975843059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5779673738623763967790745 4334755303967822975843059)
                  ·
                    refine ⟨6502132955951734463764589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4334755303967822975843059 6502132955951734463764589)
                    ·
                      refine ⟨2438299858481900423911721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6502132955951734463764589 2438299858481900423911721)
                      ·
                        rfl

theorem cell23_4748572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_4748572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748572 prefixEnd_4748572 := by exact prefixLift 4748572
  have htrace : WordTrace (prefixWord ++ tailWord_4748572) baseStart_4748572 baseEnd_4748572 := by
    simpa [prefixWord, tailWord_4748572, baseEnd_4748572] using wordTrace_append hprefix tailTrace_4748572
  have hstable : (prefixWord ++ tailWord_4748572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748572).length < 2 ^ (prefixWord ++ tailWord_4748572).sum := by decide
  have hdescent : baseEnd_4748572 < baseStart_4748572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748589 : List Nat := [1, 5, 3, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_4748589 : Nat := 118140960795 + 4748589 * 2 ^ 59
def prefixEnd_4748589 : Nat := 4983230072969 + 3 ^ 40 * 4748589 * 2
def baseEnd_4748589 : Nat := 2438308587653026857399143

theorem tailTrace_4748589 : CollatzResearch.WordTrace tailWord_4748589 prefixEnd_4748589 2438308587653026857399143 := by
  unfold tailWord_4748589
  simp only [CollatzResearch.WordTrace]
  refine ⟨173195269393680522279744821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115463512929120348186496547 173195269393680522279744821)
  ·
    refine ⟨16237056505657548963726077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 173195269393680522279744821 16237056505657548963726077)
    ·
      refine ⟨6088896189621580861397279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16237056505657548963726077 6088896189621580861397279)
      ·
        refine ⟨9133344284432371292095919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6088896189621580861397279 9133344284432371292095919)
        ·
          refine ⟨13700016426648556938143879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9133344284432371292095919 13700016426648556938143879)
          ·
            refine ⟨20550024639972835407215819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13700016426648556938143879 20550024639972835407215819)
            ·
              refine ⟨30825036959959253110823729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20550024639972835407215819 30825036959959253110823729)
              ·
                refine ⟨23118777719969439833117797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30825036959959253110823729 23118777719969439833117797)
                ·
                  refine ⟨4334770822494269968709587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23118777719969439833117797 4334770822494269968709587)
                  ·
                    refine ⟨6502156233741404953064381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4334770822494269968709587 6502156233741404953064381)
                    ·
                      refine ⟨2438308587653026857399143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6502156233741404953064381 2438308587653026857399143)
                      ·
                        rfl

theorem cell23_4748589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_4748589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748589 prefixEnd_4748589 := by exact prefixLift 4748589
  have htrace : WordTrace (prefixWord ++ tailWord_4748589) baseStart_4748589 baseEnd_4748589 := by
    simpa [prefixWord, tailWord_4748589, baseEnd_4748589] using wordTrace_append hprefix tailTrace_4748589
  have hstable : (prefixWord ++ tailWord_4748589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748589).length < 2 ^ (prefixWord ++ tailWord_4748589).sum := by decide
  have hdescent : baseEnd_4748589 < baseStart_4748589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748665 : List Nat := [1, 2, 1, 3, 2, 1, 4, 2, 2, 5]
def baseStart_4748665 : Nat := 118140960795 + 4748665 * 2 ^ 59
def prefixEnd_4748665 : Nat := 4983230072969 + 3 ^ 40 * 4748665 * 2
def baseEnd_4748665 : Nat := 812782537394256186682931

theorem tailTrace_4748665 : CollatzResearch.WordTrace tailWord_4748665 prefixEnd_4748665 812782537394256186682931 := by
  unfold tailWord_4748665
  simp only [CollatzResearch.WordTrace]
  refine ⟨173198041341405187259511449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115465360894270124839674299 173198041341405187259511449)
  ·
    refine ⟨129898531006053890444633587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173198041341405187259511449 129898531006053890444633587)
    ·
      refine ⟨194847796509080835666950381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129898531006053890444633587 194847796509080835666950381)
      ·
        refine ⟨73067923690905313375106393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194847796509080835666950381 73067923690905313375106393)
        ·
          refine ⟨54800942768178985031329795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73067923690905313375106393 54800942768178985031329795)
          ·
            refine ⟨82201414152268477546994693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54800942768178985031329795 82201414152268477546994693)
            ·
              refine ⟨15412765153550339540061505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82201414152268477546994693 15412765153550339540061505)
              ·
                refine ⟨11559573865162754655046129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15412765153550339540061505 11559573865162754655046129)
                ·
                  refine ⟨8669680398872065991284597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11559573865162754655046129 8669680398872065991284597)
                  ·
                    refine ⟨812782537394256186682931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8669680398872065991284597 812782537394256186682931)
                    ·
                      rfl

theorem cell23_4748665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 5].length) (baseStart_4748665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748665 prefixEnd_4748665 := by exact prefixLift 4748665
  have htrace : WordTrace (prefixWord ++ tailWord_4748665) baseStart_4748665 baseEnd_4748665 := by
    simpa [prefixWord, tailWord_4748665, baseEnd_4748665] using wordTrace_append hprefix tailTrace_4748665
  have hstable : (prefixWord ++ tailWord_4748665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748665).length < 2 ^ (prefixWord ++ tailWord_4748665).sum := by decide
  have hdescent : baseEnd_4748665 < baseStart_4748665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748675 : List Nat := [1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 5]
def baseStart_4748675 : Nat := 118140960795 + 4748675 * 2 ^ 59
def prefixEnd_4748675 : Nat := 4983230072969 + 3 ^ 40 * 4748675 * 2
def baseEnd_4748675 : Nat := 2438352746989313520923747

theorem tailTrace_4748675 : CollatzResearch.WordTrace tailWord_4748675 prefixEnd_4748675 2438352746989313520923747 := by
  unfold tailWord_4748675
  simp only [CollatzResearch.WordTrace]
  refine ⟨173198406071368958967375479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115465604047579305978250319 173198406071368958967375479)
  ·
    refine ⟨259797609107053438451063219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173198406071368958967375479 259797609107053438451063219)
    ·
      refine ⟨389696413660580157676594829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259797609107053438451063219 389696413660580157676594829)
      ·
        refine ⟨146136155122717559128723061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 389696413660580157676594829 146136155122717559128723061)
        ·
          refine ⟨13700264542754771168317787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 146136155122717559128723061 13700264542754771168317787)
          ·
            refine ⟨20550396814132156752476681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13700264542754771168317787 20550396814132156752476681)
            ·
              refine ⟨15412797610599117564357511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20550396814132156752476681 15412797610599117564357511)
              ·
                refine ⟨23119196415898676346536267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15412797610599117564357511 23119196415898676346536267)
                ·
                  refine ⟨34678794623848014519804401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23119196415898676346536267 34678794623848014519804401)
                  ·
                    refine ⟨26009095967886010889853301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34678794623848014519804401 26009095967886010889853301)
                    ·
                      refine ⟨2438352746989313520923747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26009095967886010889853301 2438352746989313520923747)
                      ·
                        rfl

theorem cell23_4748675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_4748675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748675 prefixEnd_4748675 := by exact prefixLift 4748675
  have htrace : WordTrace (prefixWord ++ tailWord_4748675) baseStart_4748675 baseEnd_4748675 := by
    simpa [prefixWord, tailWord_4748675, baseEnd_4748675] using wordTrace_append hprefix tailTrace_4748675
  have hstable : (prefixWord ++ tailWord_4748675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748675).length < 2 ^ (prefixWord ++ tailWord_4748675).sum := by decide
  have hdescent : baseEnd_4748675 < baseStart_4748675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748729 : List Nat := [1, 2, 1, 4, 4, 1, 2, 1, 3, 4]
def baseStart_4748729 : Nat := 118140960795 + 4748729 * 2 ^ 59
def prefixEnd_4748729 : Nat := 4983230072969 + 3 ^ 40 * 4748729 * 2
def baseEnd_4748729 : Nat := 812793491648218769882833

theorem tailTrace_4748729 : CollatzResearch.WordTrace tailWord_4748729 prefixEnd_4748729 812793491648218769882833 := by
  unfold tailWord_4748729
  simp only [CollatzResearch.WordTrace]
  refine ⟨173200375613173326189841241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115466917075448884126560827 173200375613173326189841241)
  ·
    refine ⟨129900281709879994642380931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173200375613173326189841241 129900281709879994642380931)
    ·
      refine ⟨194850422564819991963571397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129900281709879994642380931 194850422564819991963571397)
      ·
        refine ⟨36534454230903748493169637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 194850422564819991963571397 36534454230903748493169637)
        ·
          refine ⟨6850210168294452842469307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36534454230903748493169637 6850210168294452842469307)
          ·
            refine ⟨10275315252441679263703961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6850210168294452842469307 10275315252441679263703961)
            ·
              refine ⟨7706486439331259447777971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10275315252441679263703961 7706486439331259447777971)
              ·
                refine ⟨11559729658996889171666957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7706486439331259447777971 11559729658996889171666957)
                ·
                  refine ⟨4334898622123833439375109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11559729658996889171666957 4334898622123833439375109)
                  ·
                    refine ⟨812793491648218769882833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4334898622123833439375109 812793491648218769882833)
                    ·
                      rfl

theorem cell23_4748729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3, 4].length) (baseStart_4748729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748729 prefixEnd_4748729 := by exact prefixLift 4748729
  have htrace : WordTrace (prefixWord ++ tailWord_4748729) baseStart_4748729 baseEnd_4748729 := by
    simpa [prefixWord, tailWord_4748729, baseEnd_4748729] using wordTrace_append hprefix tailTrace_4748729
  have hstable : (prefixWord ++ tailWord_4748729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748729).length < 2 ^ (prefixWord ++ tailWord_4748729).sum := by decide
  have hdescent : baseEnd_4748729 < baseStart_4748729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748786 : List Nat := [3, 2, 1, 4, 1, 1, 3, 1, 3, 1, 3]
def baseStart_4748786 : Nat := 118140960795 + 4748786 * 2 ^ 59
def prefixEnd_4748786 : Nat := 4983230072969 + 3 ^ 40 * 4748786 * 2
def baseEnd_4748786 : Nat := 2438409743341962586635737

theorem tailTrace_4748786 : CollatzResearch.WordTrace tailWord_4748786 prefixEnd_4748786 2438409743341962586635737 := by
  unfold tailWord_4748786
  simp only [CollatzResearch.WordTrace]
  refine ⟨43300613643491706231166553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115468303049311216616444141 43300613643491706231166553)
  ·
    refine ⟨32475460232618779673374915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43300613643491706231166553 32475460232618779673374915)
    ·
      refine ⟨48713190348928169510062373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32475460232618779673374915 48713190348928169510062373)
      ·
        refine ⟨9133723190424031783136695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48713190348928169510062373 9133723190424031783136695)
        ·
          refine ⟨13700584785636047674705043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9133723190424031783136695 13700584785636047674705043)
          ·
            refine ⟨20550877178454071512057565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13700584785636047674705043 20550877178454071512057565)
            ·
              refine ⟨7706578941920276817021587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20550877178454071512057565 7706578941920276817021587)
              ·
                refine ⟨11559868412880415225532381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7706578941920276817021587 11559868412880415225532381)
                ·
                  refine ⟨4334950654830155709574643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11559868412880415225532381 4334950654830155709574643)
                  ·
                    refine ⟨6502425982245233564361965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4334950654830155709574643 6502425982245233564361965)
                    ·
                      refine ⟨2438409743341962586635737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6502425982245233564361965 2438409743341962586635737)
                      ·
                        rfl

theorem cell23_4748786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_4748786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748786 prefixEnd_4748786 := by exact prefixLift 4748786
  have htrace : WordTrace (prefixWord ++ tailWord_4748786) baseStart_4748786 baseEnd_4748786 := by
    simpa [prefixWord, tailWord_4748786, baseEnd_4748786] using wordTrace_append hprefix tailTrace_4748786
  have hstable : (prefixWord ++ tailWord_4748786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748786).length < 2 ^ (prefixWord ++ tailWord_4748786).sum := by decide
  have hdescent : baseEnd_4748786 < baseStart_4748786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748809 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 5, 2, 2]
def baseStart_4748809 : Nat := 118140960795 + 4748809 * 2 ^ 59
def prefixEnd_4748809 : Nat := 4983230072969 + 3 ^ 40 * 4748809 * 2
def baseEnd_4748809 : Nat := 2438421553397015996648131

theorem tailTrace_4748809 : CollatzResearch.WordTrace tailWord_4748809 prefixEnd_4748809 2438421553397015996648131 := by
  unfold tailWord_4748809
  simp only [CollatzResearch.WordTrace]
  refine ⟨173203293452883499852753481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115468862301922333235168987 173203293452883499852753481)
  ·
    refine ⟨129902470089662624889565111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173203293452883499852753481 129902470089662624889565111)
    ·
      refine ⟨194853705134493937334347667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129902470089662624889565111 194853705134493937334347667)
      ·
        refine ⟨292280557701740906001521501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194853705134493937334347667 292280557701740906001521501)
        ·
          refine ⟨109605209138152839750570563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 292280557701740906001521501 109605209138152839750570563)
          ·
            refine ⟨164407813707229259625855845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109605209138152839750570563 164407813707229259625855845)
            ·
              refine ⟨30826465070105486179847971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 164407813707229259625855845 30826465070105486179847971)
              ·
                refine ⟨46239697605158229269771957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30826465070105486179847971 46239697605158229269771957)
                ·
                  refine ⟨4334971650483583994041121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46239697605158229269771957 4334971650483583994041121)
                  ·
                    refine ⟨3251228737862687995530841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4334971650483583994041121 3251228737862687995530841)
                    ·
                      refine ⟨2438421553397015996648131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3251228737862687995530841 2438421553397015996648131)
                      ·
                        rfl

theorem cell23_4748809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 2, 2].length) (baseStart_4748809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748809 prefixEnd_4748809 := by exact prefixLift 4748809
  have htrace : WordTrace (prefixWord ++ tailWord_4748809) baseStart_4748809 baseEnd_4748809 := by
    simpa [prefixWord, tailWord_4748809, baseEnd_4748809] using wordTrace_append hprefix tailTrace_4748809
  have hstable : (prefixWord ++ tailWord_4748809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748809).length < 2 ^ (prefixWord ++ tailWord_4748809).sum := by decide
  have hdescent : baseEnd_4748809 < baseStart_4748809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748869 : List Nat := [1, 3, 1, 1, 1, 4, 1, 3, 3, 3, 2]
def baseStart_4748869 : Nat := 118140960795 + 4748869 * 2 ^ 59
def prefixEnd_4748869 : Nat := 4983230072969 + 3 ^ 40 * 4748869 * 2
def baseEnd_4748869 : Nat := 2438452362236285761897855

theorem tailTrace_4748869 : CollatzResearch.WordTrace tailWord_4748869 prefixEnd_4748869 2438452362236285761897855 := by
  unfold tailWord_4748869
  simp only [CollatzResearch.WordTrace]
  refine ⟨173205481832666130099937661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115470321221777420066625107 173205481832666130099937661)
  ·
    refine ⟨64952055687249798787476623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173205481832666130099937661 64952055687249798787476623)
    ·
      refine ⟨97428083530874698181214935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64952055687249798787476623 97428083530874698181214935)
      ·
        refine ⟨146142125296312047271822403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97428083530874698181214935 146142125296312047271822403)
        ·
          refine ⟨219213187944468070907733605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146142125296312047271822403 219213187944468070907733605)
          ·
            refine ⟨41102472739587763295200051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 219213187944468070907733605 41102472739587763295200051)
            ·
              refine ⟨61653709109381644942800077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41102472739587763295200051 61653709109381644942800077)
              ·
                refine ⟨23120140916018116853550029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61653709109381644942800077 23120140916018116853550029)
                ·
                  refine ⟨8670052843506793820081261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23120140916018116853550029 8670052843506793820081261)
                  ·
                    refine ⟨3251269816315047682530473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8670052843506793820081261 3251269816315047682530473)
                    ·
                      refine ⟨2438452362236285761897855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3251269816315047682530473 2438452362236285761897855)
                      ·
                        rfl

theorem cell23_4748869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 3, 2].length) (baseStart_4748869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748869 prefixEnd_4748869 := by exact prefixLift 4748869
  have htrace : WordTrace (prefixWord ++ tailWord_4748869) baseStart_4748869 baseEnd_4748869 := by
    simpa [prefixWord, tailWord_4748869, baseEnd_4748869] using wordTrace_append hprefix tailTrace_4748869
  have hstable : (prefixWord ++ tailWord_4748869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748869).length < 2 ^ (prefixWord ++ tailWord_4748869).sum := by decide
  have hdescent : baseEnd_4748869 < baseStart_4748869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748875 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 3, 8]
def baseStart_4748875 : Nat := 118140960795 + 4748875 * 2 ^ 59
def prefixEnd_4748875 : Nat := 4983230072969 + 3 ^ 40 * 4748875 * 2
def baseEnd_4748875 : Nat := 812818481040070912807609

theorem tailTrace_4748875 : CollatzResearch.WordTrace tailWord_4748875 prefixEnd_4748875 812818481040070912807609 := by
  unfold tailWord_4748875
  simp only [CollatzResearch.WordTrace]
  refine ⟨173205700670644393124656079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115470467113762928749770719 173205700670644393124656079)
  ·
    refine ⟨259808551005966589686984119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173205700670644393124656079 259808551005966589686984119)
    ·
      refine ⟨389712826508949884530476179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259808551005966589686984119 389712826508949884530476179)
      ·
        refine ⟨584569239763424826795714269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389712826508949884530476179 584569239763424826795714269)
        ·
          refine ⟨219213464911284310048392851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 584569239763424826795714269 219213464911284310048392851)
          ·
            refine ⟨328820197366926465072589277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219213464911284310048392851 328820197366926465072589277)
            ·
              refine ⟨123307574012597424402220979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 328820197366926465072589277 123307574012597424402220979)
              ·
                refine ⟨184961361018896136603331469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123307574012597424402220979 184961361018896136603331469)
                ·
                  refine ⟨69360510382086051226249301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 184961361018896136603331469 69360510382086051226249301)
                  ·
                    refine ⟨812818481040070912807609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69360510382086051226249301 812818481040070912807609)
                    ·
                      rfl

theorem cell23_4748875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 8].length) (baseStart_4748875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748875 prefixEnd_4748875 := by exact prefixLift 4748875
  have htrace : WordTrace (prefixWord ++ tailWord_4748875) baseStart_4748875 baseEnd_4748875 := by
    simpa [prefixWord, tailWord_4748875, baseEnd_4748875] using wordTrace_append hprefix tailTrace_4748875
  have hstable : (prefixWord ++ tailWord_4748875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748875).length < 2 ^ (prefixWord ++ tailWord_4748875).sum := by decide
  have hdescent : baseEnd_4748875 < baseStart_4748875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748877 : List Nat := [1, 6, 1, 1, 3, 1, 2, 3, 1, 2, 2]
def baseStart_4748877 : Nat := 118140960795 + 4748877 * 2 ^ 59
def prefixEnd_4748877 : Nat := 4983230072969 + 3 ^ 40 * 4748877 * 2
def baseEnd_4748877 : Nat := 2438456470081521730597819

theorem tailTrace_4748877 : CollatzResearch.WordTrace tailWord_4748877 prefixEnd_4748877 2438456470081521730597819 := by
  unfold tailWord_4748877
  simp only [CollatzResearch.WordTrace]
  refine ⟨173205773616637147466228885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115470515744424764977485923 173205773616637147466228885)
  ·
    refine ⟨8119020638279866287479479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 173205773616637147466228885 8119020638279866287479479)
    ·
      refine ⟨12178530957419799431219219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8119020638279866287479479 12178530957419799431219219)
      ·
        refine ⟨18267796436129699146828829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12178530957419799431219219 18267796436129699146828829)
        ·
          refine ⟨6850423663548637180060811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18267796436129699146828829 6850423663548637180060811)
          ·
            refine ⟨10275635495322955770091217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6850423663548637180060811 10275635495322955770091217)
            ·
              refine ⟨7706726621492216827568413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10275635495322955770091217 7706726621492216827568413)
              ·
                refine ⟨2890022483059581310338155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7706726621492216827568413 2890022483059581310338155)
                ·
                  refine ⟨4335033724589371965507233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2890022483059581310338155 4335033724589371965507233)
                  ·
                    refine ⟨3251275293442028974130425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4335033724589371965507233 3251275293442028974130425)
                    ·
                      refine ⟨2438456470081521730597819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3251275293442028974130425 2438456470081521730597819)
                      ·
                        rfl

theorem cell23_4748877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_4748877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748877 prefixEnd_4748877 := by exact prefixLift 4748877
  have htrace : WordTrace (prefixWord ++ tailWord_4748877) baseStart_4748877 baseEnd_4748877 := by
    simpa [prefixWord, tailWord_4748877, baseEnd_4748877] using wordTrace_append hprefix tailTrace_4748877
  have hstable : (prefixWord ++ tailWord_4748877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748877).length < 2 ^ (prefixWord ++ tailWord_4748877).sum := by decide
  have hdescent : baseEnd_4748877 < baseStart_4748877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748910 : List Nat := [4, 1, 2, 2, 3, 1, 3, 1, 2, 1, 3]
def baseStart_4748910 : Nat := 118140960795 + 4748910 * 2 ^ 59
def prefixEnd_4748910 : Nat := 4983230072969 + 3 ^ 40 * 4748910 * 2
def baseEnd_4748910 : Nat := 2438473414943120101485167

theorem tailTrace_4748910 : CollatzResearch.WordTrace tailWord_4748910 prefixEnd_4748910 2438473414943120101485167 := by
  unfold tailWord_4748910
  simp only [CollatzResearch.WordTrace]
  refine ⟨21650872153189699262772523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115471318150345062734786789 21650872153189699262772523)
  ·
    refine ⟨32476308229784548894158785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21650872153189699262772523 32476308229784548894158785)
    ·
      refine ⟨24357231172338411670619089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32476308229784548894158785 24357231172338411670619089)
      ·
        refine ⟨18267923379253808752964317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24357231172338411670619089 18267923379253808752964317)
        ·
          refine ⟨6850471267220178282361619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18267923379253808752964317 6850471267220178282361619)
          ·
            refine ⟨10275706900830267423542429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6850471267220178282361619 10275706900830267423542429)
            ·
              refine ⟨3853390087811350283828411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10275706900830267423542429 3853390087811350283828411)
              ·
                refine ⟨5780085131717025425742617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3853390087811350283828411 5780085131717025425742617)
                ·
                  refine ⟨4335063848787769069306963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5780085131717025425742617 4335063848787769069306963)
                  ·
                    refine ⟨6502595773181653603960445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4335063848787769069306963 6502595773181653603960445)
                    ·
                      refine ⟨2438473414943120101485167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6502595773181653603960445 2438473414943120101485167)
                      ·
                        rfl

theorem cell23_4748910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_4748910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748910 prefixEnd_4748910 := by exact prefixLift 4748910
  have htrace : WordTrace (prefixWord ++ tailWord_4748910) baseStart_4748910 baseEnd_4748910 := by
    simpa [prefixWord, tailWord_4748910, baseEnd_4748910] using wordTrace_append hprefix tailTrace_4748910
  have hstable : (prefixWord ++ tailWord_4748910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748910).length < 2 ^ (prefixWord ++ tailWord_4748910).sum := by decide
  have hdescent : baseEnd_4748910 < baseStart_4748910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748936 : List Nat := [2, 1, 3, 5, 1, 1, 1, 1, 2, 1, 5]
def baseStart_4748936 : Nat := 118140960795 + 4748936 * 2 ^ 59
def prefixEnd_4748936 : Nat := 4983230072969 + 3 ^ 40 * 4748936 * 2
def baseEnd_4748936 : Nat := 2438486765440136999760047

theorem tailTrace_4748936 : CollatzResearch.WordTrace tailWord_4748936 prefixEnd_4748936 2438486765440136999760047 := by
  unfold tailWord_4748936
  simp only [CollatzResearch.WordTrace]
  refine ⟨86603962761711700271313331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115471950348948933695084441 86603962761711700271313331)
  ·
    refine ⟨129905944142567550406969997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86603962761711700271313331 129905944142567550406969997)
    ·
      refine ⟨48714729053462831402613749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129905944142567550406969997 48714729053462831402613749)
      ·
        refine ⟨4567005848762140443995039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48714729053462831402613749 4567005848762140443995039)
        ·
          refine ⟨6850508773143210665992559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4567005848762140443995039 6850508773143210665992559)
          ·
            refine ⟨10275763159714815998988839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6850508773143210665992559 10275763159714815998988839)
            ·
              refine ⟨15413644739572223998483259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10275763159714815998988839 15413644739572223998483259)
              ·
                refine ⟨23120467109358335997724889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15413644739572223998483259 23120467109358335997724889)
                ·
                  refine ⟨17340350332018751998293667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23120467109358335997724889 17340350332018751998293667)
                  ·
                    refine ⟨26010525498028127997440501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17340350332018751998293667 26010525498028127997440501)
                    ·
                      refine ⟨2438486765440136999760047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26010525498028127997440501 2438486765440136999760047)
                      ·
                        rfl

theorem cell23_4748936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_4748936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748936 prefixEnd_4748936 := by exact prefixLift 4748936
  have htrace : WordTrace (prefixWord ++ tailWord_4748936) baseStart_4748936 baseEnd_4748936 := by
    simpa [prefixWord, tailWord_4748936, baseEnd_4748936] using wordTrace_append hprefix tailTrace_4748936
  have hstable : (prefixWord ++ tailWord_4748936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748936).length < 2 ^ (prefixWord ++ tailWord_4748936).sum := by decide
  have hdescent : baseEnd_4748936 < baseStart_4748936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4748956 : List Nat := [2, 2, 3, 2, 3, 2, 1, 1, 7]
def baseStart_4748956 : Nat := 118140960795 + 4748956 * 2 ^ 59
def prefixEnd_4748956 : Nat := 4983230072969 + 3 ^ 40 * 4748956 * 2
def baseEnd_4748956 : Nat := 270944115005914102389995

theorem tailTrace_4748956 : CollatzResearch.WordTrace tailWord_4748956 prefixEnd_4748956 270944115005914102389995 := by
  unfold tailWord_4748956
  simp only [CollatzResearch.WordTrace]
  refine ⟨86604327491675471979177361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115472436655567295972236481 86604327491675471979177361)
  ·
    refine ⟨64953245618756603984383021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86604327491675471979177361 64953245618756603984383021)
    ·
      refine ⟨24357467107033726494143633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64953245618756603984383021 24357467107033726494143633)
      ·
        refine ⟨18268100330275294870607725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24357467107033726494143633 18268100330275294870607725)
        ·
          refine ⟨6850537623853235576477897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18268100330275294870607725 6850537623853235576477897)
          ·
            refine ⟨5137903217889926682358423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6850537623853235576477897 5137903217889926682358423)
            ·
              refine ⟨7706854826834890023537635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5137903217889926682358423 7706854826834890023537635)
              ·
                refine ⟨11560282240252335035306453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7706854826834890023537635 11560282240252335035306453)
                ·
                  refine ⟨270944115005914102389995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11560282240252335035306453 270944115005914102389995)
                  ·
                    rfl

theorem cell23_4748956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 7].length) (baseStart_4748956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4748956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4748956 prefixEnd_4748956 := by exact prefixLift 4748956
  have htrace : WordTrace (prefixWord ++ tailWord_4748956) baseStart_4748956 baseEnd_4748956 := by
    simpa [prefixWord, tailWord_4748956, baseEnd_4748956] using wordTrace_append hprefix tailTrace_4748956
  have hstable : (prefixWord ++ tailWord_4748956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4748956).length < 2 ^ (prefixWord ++ tailWord_4748956).sum := by decide
  have hdescent : baseEnd_4748956 < baseStart_4748956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4748956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749006 : List Nat := [4, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2]
def baseStart_4749006 : Nat := 118140960795 + 4749006 * 2 ^ 59
def prefixEnd_4749006 : Nat := 4983230072969 + 3 ^ 40 * 4749006 * 2
def baseEnd_4749006 : Nat := 2438522709085951725884725

theorem tailTrace_4749006 : CollatzResearch.WordTrace tailWord_4749006 prefixEnd_4749006 2438522709085951725884725 := by
  unfold tailWord_4749006
  simp only [CollatzResearch.WordTrace]
  refine ⟨21651309829146225312209359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115473652422113201665116581 21651309829146225312209359)
  ·
    refine ⟨32476964743719337968314039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21651309829146225312209359 32476964743719337968314039)
    ·
      refine ⟨48715447115579006952471059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32476964743719337968314039 48715447115579006952471059)
      ·
        refine ⟨73073170673368510428706589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48715447115579006952471059 73073170673368510428706589)
        ·
          refine ⟨27402439002513191410764971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73073170673368510428706589 27402439002513191410764971)
          ·
            refine ⟨41103658503769787116147457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27402439002513191410764971 41103658503769787116147457)
            ·
              refine ⟨30827743877827340337110593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41103658503769787116147457 30827743877827340337110593)
              ·
                refine ⟨23120807908370505252832945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30827743877827340337110593 23120807908370505252832945)
                ·
                  refine ⟨17340605931277878939624709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23120807908370505252832945 17340605931277878939624709)
                  ·
                    refine ⟨3251363612114602301179633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17340605931277878939624709 3251363612114602301179633)
                    ·
                      refine ⟨2438522709085951725884725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3251363612114602301179633 2438522709085951725884725)
                      ·
                        rfl

theorem cell23_4749006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2].length) (baseStart_4749006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749006 prefixEnd_4749006 := by exact prefixLift 4749006
  have htrace : WordTrace (prefixWord ++ tailWord_4749006) baseStart_4749006 baseEnd_4749006 := by
    simpa [prefixWord, tailWord_4749006, baseEnd_4749006] using wordTrace_append hprefix tailTrace_4749006
  have hstable : (prefixWord ++ tailWord_4749006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749006).length < 2 ^ (prefixWord ++ tailWord_4749006).sum := by decide
  have hdescent : baseEnd_4749006 < baseStart_4749006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749029 : List Nat := [1, 3, 1, 4, 1, 1, 1, 5, 6]
def baseStart_4749029 : Nat := 118140960795 + 4749029 * 2 ^ 59
def prefixEnd_4749029 : Nat := 4983230072969 + 3 ^ 40 * 4749029 * 2
def baseEnd_4749029 : Nat := 270948279904556126210791

theorem tailTrace_4749029 : CollatzResearch.WordTrace tailWord_4749029 prefixEnd_4749029 270948279904556126210791 := by
  unfold tailWord_4749029
  simp only [CollatzResearch.WordTrace]
  refine ⟨173211317512086477425762141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115474211674724318283841427 173211317512086477425762141)
  ·
    refine ⟨64954244067032429034660803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173211317512086477425762141 64954244067032429034660803)
    ·
      refine ⟨97431366100548643551991205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64954244067032429034660803 97431366100548643551991205)
      ·
        refine ⟨18268381143852870665998351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97431366100548643551991205 18268381143852870665998351)
        ·
          refine ⟨27402571715779305998997527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18268381143852870665998351 27402571715779305998997527)
          ·
            refine ⟨41103857573668958998496291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27402571715779305998997527 41103857573668958998496291)
            ·
              refine ⟨61655786360503438497744437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41103857573668958998496291 61655786360503438497744437)
              ·
                refine ⟨5780229971297197359163541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61655786360503438497744437 5780229971297197359163541)
                ·
                  refine ⟨270948279904556126210791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5780229971297197359163541 270948279904556126210791)
                  ·
                    rfl

theorem cell23_4749029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 6].length) (baseStart_4749029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749029 prefixEnd_4749029 := by exact prefixLift 4749029
  have htrace : WordTrace (prefixWord ++ tailWord_4749029) baseStart_4749029 baseEnd_4749029 := by
    simpa [prefixWord, tailWord_4749029, baseEnd_4749029] using wordTrace_append hprefix tailTrace_4749029
  have hstable : (prefixWord ++ tailWord_4749029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749029).length < 2 ^ (prefixWord ++ tailWord_4749029).sum := by decide
  have hdescent : baseEnd_4749029 < baseStart_4749029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749063 : List Nat := [1, 1, 4, 4, 2, 2, 1, 2, 6]
def baseStart_4749063 : Nat := 118140960795 + 4749063 * 2 ^ 59
def prefixEnd_4749063 : Nat := 4983230072969 + 3 ^ 40 * 4749063 * 2
def baseEnd_4749063 : Nat := 270950219720362000319107

theorem tailTrace_4749063 : CollatzResearch.WordTrace tailWord_4749063 prefixEnd_4749063 270950219720362000319107 := by
  unfold tailWord_4749063
  simp only [CollatzResearch.WordTrace]
  refine ⟨173212557593963301232499843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115475038395975534154999895 173212557593963301232499843)
  ·
    refine ⟨259818836390944951848749765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173212557593963301232499843 259818836390944951848749765)
    ·
      refine ⟨48716031823302178471640581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 259818836390944951848749765 48716031823302178471640581)
      ·
        refine ⟨9134255966869158463432609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48716031823302178471640581 9134255966869158463432609)
        ·
          refine ⟨6850691975151868847574457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9134255966869158463432609 6850691975151868847574457)
          ·
            refine ⟨5138018981363901635680843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6850691975151868847574457 5138018981363901635680843)
            ·
              refine ⟨7707028472045852453521265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5138018981363901635680843 7707028472045852453521265)
              ·
                refine ⟨5780271354034389340140949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7707028472045852453521265 5780271354034389340140949)
                ·
                  refine ⟨270950219720362000319107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5780271354034389340140949 270950219720362000319107)
                  ·
                    rfl

theorem cell23_4749063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 6].length) (baseStart_4749063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749063 prefixEnd_4749063 := by exact prefixLift 4749063
  have htrace : WordTrace (prefixWord ++ tailWord_4749063) baseStart_4749063 baseEnd_4749063 := by
    simpa [prefixWord, tailWord_4749063, baseEnd_4749063] using wordTrace_append hprefix tailTrace_4749063
  have hstable : (prefixWord ++ tailWord_4749063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749063).length < 2 ^ (prefixWord ++ tailWord_4749063).sum := by decide
  have hdescent : baseEnd_4749063 < baseStart_4749063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749106 : List Nat := [3, 2, 1, 1, 3, 2, 1, 2, 4, 4]
def baseStart_4749106 : Nat := 118140960795 + 4749106 * 2 ^ 59
def prefixEnd_4749106 : Nat := 4983230072969 + 3 ^ 40 * 4749106 * 2
def baseEnd_4749106 : Nat := 812858019050467111544755

theorem tailTrace_4749106 : CollatzResearch.WordTrace tailWord_4749106 prefixEnd_4749106 812858019050467111544755 := by
  unfold tailWord_4749106
  simp only [CollatzResearch.WordTrace]
  refine ⟨43303531483201879894078793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115476083955205013050876781 43303531483201879894078793)
  ·
    refine ⟨32477648612401409920559095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43303531483201879894078793 32477648612401409920559095)
    ·
      refine ⟨48716472918602114880838643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32477648612401409920559095 48716472918602114880838643)
      ·
        refine ⟨73074709377903172321257965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48716472918602114880838643 73074709377903172321257965)
        ·
          refine ⟨27403016016713689620471737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73074709377903172321257965 27403016016713689620471737)
          ·
            refine ⟨20552262012535267215353803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27403016016713689620471737 20552262012535267215353803)
            ·
              refine ⟨30828393018802900823030705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20552262012535267215353803 30828393018802900823030705)
              ·
                refine ⟨23121294764102175617273029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30828393018802900823030705 23121294764102175617273029)
                ·
                  refine ⟨4335242768269157928238693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23121294764102175617273029 4335242768269157928238693)
                  ·
                    refine ⟨812858019050467111544755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4335242768269157928238693 812858019050467111544755)
                    ·
                      rfl

theorem cell23_4749106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_4749106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749106 prefixEnd_4749106 := by exact prefixLift 4749106
  have htrace : WordTrace (prefixWord ++ tailWord_4749106) baseStart_4749106 baseEnd_4749106 := by
    simpa [prefixWord, tailWord_4749106, baseEnd_4749106] using wordTrace_append hprefix tailTrace_4749106
  have hstable : (prefixWord ++ tailWord_4749106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749106).length < 2 ^ (prefixWord ++ tailWord_4749106).sum := by decide
  have hdescent : baseEnd_4749106 < baseStart_4749106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749107 : List Nat := [1, 1, 1, 2, 7, 2, 1, 3, 1, 1, 3]
def baseStart_4749107 : Nat := 118140960795 + 4749107 * 2 ^ 59
def prefixEnd_4749107 : Nat := 4983230072969 + 3 ^ 40 * 4749107 * 2
def baseEnd_4749107 : Nat := 2438574570632055830721761

theorem tailTrace_4749107 : CollatzResearch.WordTrace tailWord_4749107 prefixEnd_4749107 2438574570632055830721761 := by
  unfold tailWord_4749107
  simp only [CollatzResearch.WordTrace]
  refine ⟨173214162405803896747101575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115476108270535931164734383 173214162405803896747101575)
  ·
    refine ⟨259821243608705845120652363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173214162405803896747101575 259821243608705845120652363)
    ·
      refine ⟨389731865413058767680978545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259821243608705845120652363 389731865413058767680978545)
      ·
        refine ⟨292298899059794075760733909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 389731865413058767680978545 292298899059794075760733909)
        ·
          refine ⟨6850755446713923650642201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 292298899059794075760733909 6850755446713923650642201)
          ·
            refine ⟨5138066585035442737981651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6850755446713923650642201 5138066585035442737981651)
            ·
              refine ⟨7707099877553164106972477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5138066585035442737981651 7707099877553164106972477)
              ·
                refine ⟨2890162454082436540114679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7707099877553164106972477 2890162454082436540114679)
                ·
                  refine ⟨4335243681123654810172019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2890162454082436540114679 4335243681123654810172019)
                  ·
                    refine ⟨6502865521685482215258029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4335243681123654810172019 6502865521685482215258029)
                    ·
                      refine ⟨2438574570632055830721761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6502865521685482215258029 2438574570632055830721761)
                      ·
                        rfl

theorem cell23_4749107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3, 1, 1, 3].length) (baseStart_4749107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749107 prefixEnd_4749107 := by exact prefixLift 4749107
  have htrace : WordTrace (prefixWord ++ tailWord_4749107) baseStart_4749107 baseEnd_4749107 := by
    simpa [prefixWord, tailWord_4749107, baseEnd_4749107] using wordTrace_append hprefix tailTrace_4749107
  have hstable : (prefixWord ++ tailWord_4749107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749107).length < 2 ^ (prefixWord ++ tailWord_4749107).sum := by decide
  have hdescent : baseEnd_4749107 < baseStart_4749107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749133 : List Nat := [1, 6, 1, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_4749133 : Nat := 118140960795 + 4749133 * 2 ^ 59
def prefixEnd_4749133 : Nat := 4983230072969 + 3 ^ 40 * 4749133 * 2
def baseEnd_4749133 : Nat := 2438587921129072728996641

theorem tailTrace_4749133 : CollatzResearch.WordTrace tailWord_4749133 prefixEnd_4749133 2438587921129072728996641 := by
  unfold tailWord_4749133
  simp only [CollatzResearch.WordTrace]
  refine ⟨173215110703709703187548053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115476740469139802125032035 173215110703709703187548053)
  ·
    refine ⟨8119458314236392336916315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 173215110703709703187548053 8119458314236392336916315)
    ·
      refine ⟨12179187471354588505374473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8119458314236392336916315 12179187471354588505374473)
      ·
        refine ⟨9134390603515941379030855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12179187471354588505374473 9134390603515941379030855)
        ·
          refine ⟨13701585905273912068546283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9134390603515941379030855 13701585905273912068546283)
          ·
            refine ⟨20552378857910868102819425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13701585905273912068546283 20552378857910868102819425)
            ·
              refine ⟨15414284143433151077114569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20552378857910868102819425 15414284143433151077114569)
              ·
                refine ⟨11560713107574863307835927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15414284143433151077114569 11560713107574863307835927)
                ·
                  refine ⟨17341069661362294961753891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11560713107574863307835927 17341069661362294961753891)
                  ·
                    refine ⟨26011604492043442442630837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17341069661362294961753891 26011604492043442442630837)
                    ·
                      refine ⟨2438587921129072728996641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26011604492043442442630837 2438587921129072728996641)
                      ·
                        rfl

theorem cell23_4749133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_4749133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749133 prefixEnd_4749133 := by exact prefixLift 4749133
  have htrace : WordTrace (prefixWord ++ tailWord_4749133) baseStart_4749133 baseEnd_4749133 := by
    simpa [prefixWord, tailWord_4749133, baseEnd_4749133] using wordTrace_append hprefix tailTrace_4749133
  have hstable : (prefixWord ++ tailWord_4749133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749133).length < 2 ^ (prefixWord ++ tailWord_4749133).sum := by decide
  have hdescent : baseEnd_4749133 < baseStart_4749133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749140 : List Nat := [2, 4, 1, 1, 3, 1, 4, 1, 2, 4]
def baseStart_4749140 : Nat := 118140960795 + 4749140 * 2 ^ 59
def prefixEnd_4749140 : Nat := 4983230072969 + 3 ^ 40 * 4749140 * 2
def baseEnd_4749140 : Nat := 812863838497884733869703

theorem tailTrace_4749140 : CollatzResearch.WordTrace tailWord_4749140 prefixEnd_4749140 812863838497884733869703 := by
  unfold tailWord_4749140
  simp only [CollatzResearch.WordTrace]
  refine ⟨86607683007342171691526437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115476910676456228922035249 86607683007342171691526437)
  ·
    refine ⟨16238940563876657192161207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86607683007342171691526437 16238940563876657192161207)
    ·
      refine ⟨24358410845814985788241811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16238940563876657192161207 24358410845814985788241811)
      ·
        refine ⟨36537616268722478682362717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24358410845814985788241811 36537616268722478682362717)
        ·
          refine ⟨13701606100770929505886019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36537616268722478682362717 13701606100770929505886019)
          ·
            refine ⟨20552409151156394258829029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13701606100770929505886019 20552409151156394258829029)
            ·
              refine ⟨3853576715841823923530443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20552409151156394258829029 3853576715841823923530443)
              ·
                refine ⟨5780365073762735885295665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3853576715841823923530443 5780365073762735885295665)
                ·
                  refine ⟨4335273805322051913971749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5780365073762735885295665 4335273805322051913971749)
                  ·
                    refine ⟨812863838497884733869703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4335273805322051913971749 812863838497884733869703)
                    ·
                      rfl

theorem cell23_4749140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_4749140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749140 prefixEnd_4749140 := by exact prefixLift 4749140
  have htrace : WordTrace (prefixWord ++ tailWord_4749140) baseStart_4749140 baseEnd_4749140 := by
    simpa [prefixWord, tailWord_4749140, baseEnd_4749140] using wordTrace_append hprefix tailTrace_4749140
  have hstable : (prefixWord ++ tailWord_4749140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749140).length < 2 ^ (prefixWord ++ tailWord_4749140).sum := by decide
  have hdescent : baseEnd_4749140 < baseStart_4749140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749146 : List Nat := [3, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3]
def baseStart_4749146 : Nat := 118140960795 + 4749146 * 2 ^ 59
def prefixEnd_4749146 : Nat := 4983230072969 + 3 ^ 40 * 4749146 * 2
def baseEnd_4749146 : Nat := 2438594596377581178134081

theorem tailTrace_4749146 : CollatzResearch.WordTrace tailWord_4749146 prefixEnd_4749146 2438594596377581178134081 := by
  unfold tailWord_4749146
  simp only [CollatzResearch.WordTrace]
  refine ⟨43303896213165651601942823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115477056568441737605180861 43303896213165651601942823)
  ·
    refine ⟨64955844319748477402914235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43303896213165651601942823 64955844319748477402914235)
    ·
      refine ⟨97433766479622716104371353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64955844319748477402914235 97433766479622716104371353)
      ·
        refine ⟨73075324859717037078278515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97433766479622716104371353 73075324859717037078278515)
        ·
          refine ⟨109612987289575555617417773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73075324859717037078278515 109612987289575555617417773)
          ·
            refine ⟨41104870233590833356531665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109612987289575555617417773 41104870233590833356531665)
            ·
              refine ⟨30828652675193125017398749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41104870233590833356531665 30828652675193125017398749)
              ·
                refine ⟨11560744753197421881524531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30828652675193125017398749 11560744753197421881524531)
                ·
                  refine ⟨17341117129796132822286797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11560744753197421881524531 17341117129796132822286797)
                  ·
                    refine ⟨6502918923673549808357549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17341117129796132822286797 6502918923673549808357549)
                    ·
                      refine ⟨2438594596377581178134081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6502918923673549808357549 2438594596377581178134081)
                      ·
                        rfl

theorem cell23_4749146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_4749146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749146 prefixEnd_4749146 := by exact prefixLift 4749146
  have htrace : WordTrace (prefixWord ++ tailWord_4749146) baseStart_4749146 baseEnd_4749146 := by
    simpa [prefixWord, tailWord_4749146, baseEnd_4749146] using wordTrace_append hprefix tailTrace_4749146
  have hstable : (prefixWord ++ tailWord_4749146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749146).length < 2 ^ (prefixWord ++ tailWord_4749146).sum := by decide
  have hdescent : baseEnd_4749146 < baseStart_4749146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749179 : List Nat := [1, 1, 1, 1, 1, 5, 1, 4, 2, 6]
def baseStart_4749179 : Nat := 118140960795 + 4749179 * 2 ^ 59
def prefixEnd_4749179 : Nat := 4983230072969 + 3 ^ 40 * 4749179 * 2
def baseEnd_4749179 : Nat := 812870513746393183007143

theorem tailTrace_4749179 : CollatzResearch.WordTrace tailWord_4749179 prefixEnd_4749179 812870513746393183007143 := by
  unfold tailWord_4749179
  simp only [CollatzResearch.WordTrace]
  refine ⟨173216788461543053043722591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115477858974362035362481727 173216788461543053043722591)
  ·
    refine ⟨259825182692314579565583887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173216788461543053043722591 259825182692314579565583887)
    ·
      refine ⟨389737774038471869348375831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259825182692314579565583887 389737774038471869348375831)
      ·
        refine ⟨584606661057707804022563747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389737774038471869348375831 584606661057707804022563747)
        ·
          refine ⟨876909991586561706033845621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 584606661057707804022563747 876909991586561706033845621)
          ·
            refine ⟨82210311711240159940673027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 876909991586561706033845621 82210311711240159940673027)
            ·
              refine ⟨123315467566860239911009541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82210311711240159940673027 123315467566860239911009541)
              ·
                refine ⟨23121650168786294983314289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123315467566860239911009541 23121650168786294983314289)
                ·
                  refine ⟨17341237626589721237485717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23121650168786294983314289 17341237626589721237485717)
                  ·
                    refine ⟨812870513746393183007143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17341237626589721237485717 812870513746393183007143)
                    ·
                      rfl

theorem cell23_4749179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 6].length) (baseStart_4749179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749179 prefixEnd_4749179 := by exact prefixLift 4749179
  have htrace : WordTrace (prefixWord ++ tailWord_4749179) baseStart_4749179 baseEnd_4749179 := by
    simpa [prefixWord, tailWord_4749179, baseEnd_4749179] using wordTrace_append hprefix tailTrace_4749179
  have hstable : (prefixWord ++ tailWord_4749179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749179).length < 2 ^ (prefixWord ++ tailWord_4749179).sum := by decide
  have hdescent : baseEnd_4749179 < baseStart_4749179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749209 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 9]
def baseStart_4749209 : Nat := 118140960795 + 4749209 * 2 ^ 59
def prefixEnd_4749209 : Nat := 4983230072969 + 3 ^ 40 * 4749209 * 2
def baseEnd_4749209 : Nat := 270958549517646047960699

theorem tailTrace_4749209 : CollatzResearch.WordTrace tailWord_4749209 prefixEnd_4749209 270958549517646047960699 := by
  unfold tailWord_4749209
  simp only [CollatzResearch.WordTrace]
  refine ⟨173217882651434368167314681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115478588434289578778209787 173217882651434368167314681)
  ·
    refine ⟨129913411988575776125486011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173217882651434368167314681 129913411988575776125486011)
    ·
      refine ⟨194870117982863664188229017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129913411988575776125486011 194870117982863664188229017)
      ·
        refine ⟨146152588487147748141171763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194870117982863664188229017 146152588487147748141171763)
        ·
          refine ⟨219228882730721622211757645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146152588487147748141171763 219228882730721622211757645)
          ·
            refine ⟨82210831024020608329409117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 219228882730721622211757645 82210831024020608329409117)
            ·
              refine ⟨30829061634007728123528419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82210831024020608329409117 30829061634007728123528419)
              ·
                refine ⟨46243592451011592185292629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30829061634007728123528419 46243592451011592185292629)
                ·
                  refine ⟨270958549517646047960699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46243592451011592185292629 270958549517646047960699)
                  ·
                    rfl

theorem cell23_4749209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 9].length) (baseStart_4749209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749209 prefixEnd_4749209 := by exact prefixLift 4749209
  have htrace : WordTrace (prefixWord ++ tailWord_4749209) baseStart_4749209 baseEnd_4749209 := by
    simpa [prefixWord, tailWord_4749209, baseEnd_4749209] using wordTrace_append hprefix tailTrace_4749209
  have hstable : (prefixWord ++ tailWord_4749209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749209).length < 2 ^ (prefixWord ++ tailWord_4749209).sum := by decide
  have hdescent : baseEnd_4749209 < baseStart_4749209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749219 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 7]
def baseStart_4749219 : Nat := 118140960795 + 4749219 * 2 ^ 59
def prefixEnd_4749219 : Nat := 4983230072969 + 3 ^ 40 * 4749219 * 2
def baseEnd_4749219 : Nat := 2438632080465359392521245

theorem tailTrace_4749219 : CollatzResearch.WordTrace tailWord_4749219 prefixEnd_4749219 2438632080465359392521245 := by
  unfold tailWord_4749219
  simp only [CollatzResearch.WordTrace]
  refine ⟨173218247381398139875178711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115478831587598759916785807 173218247381398139875178711)
  ·
    refine ⟨259827371072097209812768067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173218247381398139875178711 259827371072097209812768067)
    ·
      refine ⟨389741056608145814719152101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259827371072097209812768067 389741056608145814719152101)
      ·
        refine ⟨73076448114027340259841019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 389741056608145814719152101 73076448114027340259841019)
        ·
          refine ⟨109614672171041010389761529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73076448114027340259841019 109614672171041010389761529)
          ·
            refine ⟨82211004128280757792321147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109614672171041010389761529 82211004128280757792321147)
            ·
              refine ⟨123316506192421136688481721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82211004128280757792321147 123316506192421136688481721)
              ·
                refine ⟨92487379644315852516361291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123316506192421136688481721 92487379644315852516361291)
                ·
                  refine ⟨138731069466473778774541937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92487379644315852516361291 138731069466473778774541937)
                  ·
                    refine ⟨104048302099855334080906453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 138731069466473778774541937 104048302099855334080906453)
                    ·
                      refine ⟨2438632080465359392521245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104048302099855334080906453 2438632080465359392521245)
                      ·
                        rfl

theorem cell23_4749219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_4749219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749219 prefixEnd_4749219 := by exact prefixLift 4749219
  have htrace : WordTrace (prefixWord ++ tailWord_4749219) baseStart_4749219 baseEnd_4749219 := by
    simpa [prefixWord, tailWord_4749219, baseEnd_4749219] using wordTrace_append hprefix tailTrace_4749219
  have hstable : (prefixWord ++ tailWord_4749219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749219).length < 2 ^ (prefixWord ++ tailWord_4749219).sum := by decide
  have hdescent : baseEnd_4749219 < baseStart_4749219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749224 : List Nat := [2, 1, 6, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_4749224 : Nat := 118140960795 + 4749224 * 2 ^ 59
def prefixEnd_4749224 : Nat := 4983230072969 + 3 ^ 40 * 4749224 * 2
def baseEnd_4749224 : Nat := 2438634647868631872958723

theorem tailTrace_4749224 : CollatzResearch.WordTrace tailWord_4749224 prefixEnd_4749224 2438634647868631872958723 := by
  unfold tailWord_4749224
  simp only [CollatzResearch.WordTrace]
  refine ⟨86609214873190012864555363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115478953164253350486073817 86609214873190012864555363)
  ·
    refine ⟨129913822309785019296833045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86609214873190012864555363 129913822309785019296833045)
    ·
      refine ⟨6089710420771172779539049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 129913822309785019296833045 6089710420771172779539049)
      ·
        refine ⟨4567282815578379584654287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6089710420771172779539049 4567282815578379584654287)
        ·
          refine ⟨6850924223367569376981431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4567282815578379584654287 6850924223367569376981431)
          ·
            refine ⟨10276386335051354065472147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6850924223367569376981431 10276386335051354065472147)
            ·
              refine ⟨15414579502577031098208221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10276386335051354065472147 15414579502577031098208221)
              ·
                refine ⟨5780467313466386661828083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15414579502577031098208221 5780467313466386661828083)
                ·
                  refine ⟨8670700970199579992742125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5780467313466386661828083 8670700970199579992742125)
                  ·
                    refine ⟨3251512863824842497278297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8670700970199579992742125 3251512863824842497278297)
                    ·
                      refine ⟨2438634647868631872958723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3251512863824842497278297 2438634647868631872958723)
                      ·
                        rfl

theorem cell23_4749224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_4749224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749224 prefixEnd_4749224 := by exact prefixLift 4749224
  have htrace : WordTrace (prefixWord ++ tailWord_4749224) baseStart_4749224 baseEnd_4749224 := by
    simpa [prefixWord, tailWord_4749224, baseEnd_4749224] using wordTrace_append hprefix tailTrace_4749224
  have hstable : (prefixWord ++ tailWord_4749224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749224).length < 2 ^ (prefixWord ++ tailWord_4749224).sum := by decide
  have hdescent : baseEnd_4749224 < baseStart_4749224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749237 : List Nat := [1, 3, 3, 2, 1, 2, 3, 2, 2, 2, 2]
def baseStart_4749237 : Nat := 118140960795 + 4749237 * 2 ^ 59
def prefixEnd_4749237 : Nat := 4983230072969 + 3 ^ 40 * 4749237 * 2
def baseEnd_4749237 : Nat := 2438641323117140322096163

theorem tailTrace_4749237 : CollatzResearch.WordTrace tailWord_4749237 prefixEnd_4749237 2438641323117140322096163 := by
  unfold tailWord_4749237
  simp only [CollatzResearch.WordTrace]
  refine ⟨173218903895332928949333965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115479269263555285966222643 173218903895332928949333965)
  ·
    refine ⟨64957088960749848356000237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173218903895332928949333965 64957088960749848356000237)
    ·
      refine ⟨24358908360281193133500089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64957088960749848356000237 24358908360281193133500089)
      ·
        refine ⟨18269181270210894850125067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24358908360281193133500089 18269181270210894850125067)
        ·
          refine ⟨27403771905316342275187601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18269181270210894850125067 27403771905316342275187601)
          ·
            refine ⟨20552828928987256706390701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27403771905316342275187601 20552828928987256706390701)
            ·
              refine ⟨7707310848370221264896513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20552828928987256706390701 7707310848370221264896513)
              ·
                refine ⟨5780483136277665948672385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7707310848370221264896513 5780483136277665948672385)
                ·
                  refine ⟨4335362352208249461504289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5780483136277665948672385 4335362352208249461504289)
                  ·
                    refine ⟨3251521764156187096128217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4335362352208249461504289 3251521764156187096128217)
                    ·
                      refine ⟨2438641323117140322096163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3251521764156187096128217 2438641323117140322096163)
                      ·
                        rfl

theorem cell23_4749237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_4749237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749237 prefixEnd_4749237 := by exact prefixLift 4749237
  have htrace : WordTrace (prefixWord ++ tailWord_4749237) baseStart_4749237 baseEnd_4749237 := by
    simpa [prefixWord, tailWord_4749237, baseEnd_4749237] using wordTrace_append hprefix tailTrace_4749237
  have hstable : (prefixWord ++ tailWord_4749237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749237).length < 2 ^ (prefixWord ++ tailWord_4749237).sum := by decide
  have hdescent : baseEnd_4749237 < baseStart_4749237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749256 : List Nat := [2, 1, 3, 1, 4, 1, 1, 2, 1, 7]
def baseStart_4749256 : Nat := 118140960795 + 4749256 * 2 ^ 59
def prefixEnd_4749256 : Nat := 4983230072969 + 3 ^ 40 * 4749256 * 2
def baseEnd_4749256 : Nat := 812883693083191915919525

theorem tailTrace_4749256 : CollatzResearch.WordTrace tailWord_4749256 prefixEnd_4749256 812883693083191915919525 := by
  unfold tailWord_4749256
  simp only [CollatzResearch.WordTrace]
  refine ⟨86609798441132047597137811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115479731254842730129517081 86609798441132047597137811)
  ·
    refine ⟨129914697661698071395706717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86609798441132047597137811 129914697661698071395706717)
    ·
      refine ⟨48718011623136776773390019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129914697661698071395706717 48718011623136776773390019)
      ·
        refine ⟨73077017434705165160085029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48718011623136776773390019 73077017434705165160085029)
        ·
          refine ⟨13701940769007218467515943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73077017434705165160085029 13701940769007218467515943)
          ·
            refine ⟨20552911153510827701273915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13701940769007218467515943 20552911153510827701273915)
            ·
              refine ⟨30829366730266241551910873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20552911153510827701273915 30829366730266241551910873)
              ·
                refine ⟨23122025047699681163933155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30829366730266241551910873 23122025047699681163933155)
                ·
                  refine ⟨34683037571549521745899733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23122025047699681163933155 34683037571549521745899733)
                  ·
                    refine ⟨812883693083191915919525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34683037571549521745899733 812883693083191915919525)
                    ·
                      rfl

theorem cell23_4749256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_4749256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749256 prefixEnd_4749256 := by exact prefixLift 4749256
  have htrace : WordTrace (prefixWord ++ tailWord_4749256) baseStart_4749256 baseEnd_4749256 := by
    simpa [prefixWord, tailWord_4749256, baseEnd_4749256] using wordTrace_append hprefix tailTrace_4749256
  have hstable : (prefixWord ++ tailWord_4749256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749256).length < 2 ^ (prefixWord ++ tailWord_4749256).sum := by decide
  have hdescent : baseEnd_4749256 < baseStart_4749256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749277 : List Nat := [1, 4, 3, 1, 3, 2, 1, 3, 5]
def baseStart_4749277 : Nat := 118140960795 + 4749277 * 2 ^ 59
def prefixEnd_4749277 : Nat := 4983230072969 + 3 ^ 40 * 4749277 * 2
def baseEnd_4749277 : Nat := 270962429149257796177331

theorem tailTrace_4749277 : CollatzResearch.WordTrace tailWord_4749277 prefixEnd_4749277 270962429149257796177331 := by
  unfold tailWord_4749277
  simp only [CollatzResearch.WordTrace]
  refine ⟨173220362815188015780790085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115480241876792010520526723 173220362815188015780790085)
  ·
    refine ⟨32478818027847752958898141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173220362815188015780790085 32478818027847752958898141)
    ·
      refine ⟨12179556760442907359586803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32478818027847752958898141 12179556760442907359586803)
      ·
        refine ⟨18269335140664361039380205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12179556760442907359586803 18269335140664361039380205)
        ·
          refine ⟨6851000677749135389767577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18269335140664361039380205 6851000677749135389767577)
          ·
            refine ⟨5138250508311851542325683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6851000677749135389767577 5138250508311851542325683)
            ·
              refine ⟨7707375762467777313488525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5138250508311851542325683 7707375762467777313488525)
              ·
                refine ⟨2890265910925416492558197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7707375762467777313488525 2890265910925416492558197)
                ·
                  refine ⟨270962429149257796177331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2890265910925416492558197 270962429149257796177331)
                  ·
                    rfl

theorem cell23_4749277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3, 5].length) (baseStart_4749277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749277 prefixEnd_4749277 := by exact prefixLift 4749277
  have htrace : WordTrace (prefixWord ++ tailWord_4749277) baseStart_4749277 baseEnd_4749277 := by
    simpa [prefixWord, tailWord_4749277, baseEnd_4749277] using wordTrace_append hprefix tailTrace_4749277
  have hstable : (prefixWord ++ tailWord_4749277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749277).length < 2 ^ (prefixWord ++ tailWord_4749277).sum := by decide
  have hdescent : baseEnd_4749277 < baseStart_4749277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749313 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 4, 2, 3]
def baseStart_4749313 : Nat := 118140960795 + 4749313 * 2 ^ 59
def prefixEnd_4749313 : Nat := 4983230072969 + 3 ^ 40 * 4749313 * 2
def baseEnd_4749313 : Nat := 2438680347646882024745813

theorem tailTrace_4749313 : CollatzResearch.WordTrace tailWord_4749313 prefixEnd_4749313 2438680347646882024745813 := by
  unfold tailWord_4749313
  simp only [CollatzResearch.WordTrace]
  refine ⟨173221675843057593929100593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115481117228705062619400395 173221675843057593929100593)
  ·
    refine ⟨129916256882293195446825445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173221675843057593929100593 129916256882293195446825445)
    ·
      refine ⟨24359298165429974146279771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129916256882293195446825445 24359298165429974146279771)
      ·
        refine ⟨36538947248144961219419657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24359298165429974146279771 36538947248144961219419657)
        ·
          refine ⟨27404210436108720914564743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36538947248144961219419657 27404210436108720914564743)
          ·
            refine ⟨41106315654163081371847115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27404210436108720914564743 41106315654163081371847115)
            ·
              refine ⟨61659473481244622057770673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41106315654163081371847115 61659473481244622057770673)
              ·
                refine ⟨46244605110933466543328005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61659473481244622057770673 46244605110933466543328005)
                ·
                  refine ⟨8670863458300024976874001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46244605110933466543328005 8670863458300024976874001)
                  ·
                    refine ⟨6503147593725018732655501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8670863458300024976874001 6503147593725018732655501)
                    ·
                      refine ⟨2438680347646882024745813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6503147593725018732655501 2438680347646882024745813)
                      ·
                        rfl

theorem cell23_4749313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_4749313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749313 prefixEnd_4749313 := by exact prefixLift 4749313
  have htrace : WordTrace (prefixWord ++ tailWord_4749313) baseStart_4749313 baseEnd_4749313 := by
    simpa [prefixWord, tailWord_4749313, baseEnd_4749313] using wordTrace_append hprefix tailTrace_4749313
  have hstable : (prefixWord ++ tailWord_4749313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749313).length < 2 ^ (prefixWord ++ tailWord_4749313).sum := by decide
  have hdescent : baseEnd_4749313 < baseStart_4749313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749354 : List Nat := [3, 1, 4, 1, 2, 1, 4, 2, 1, 4]
def baseStart_4749354 : Nat := 118140960795 + 4749354 * 2 ^ 59
def prefixEnd_4749354 : Nat := 4983230072969 + 3 ^ 40 * 4749354 * 2
def baseEnd_4749354 : Nat := 812900466784572121444375

theorem tailTrace_4749354 : CollatzResearch.WordTrace tailWord_4749354 prefixEnd_4749354 812900466784572121444375 := by
  unfold tailWord_4749354
  simp only [CollatzResearch.WordTrace]
  refine ⟨43305792808977264482835779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115482114157272705287562077 43305792808977264482835779)
  ·
    refine ⟨64958689213465896724253669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43305792808977264482835779 64958689213465896724253669)
    ·
      refine ⟨12179754227524855635797563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64958689213465896724253669 12179754227524855635797563)
      ·
        refine ⟨18269631341287283453696345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12179754227524855635797563 18269631341287283453696345)
        ·
          refine ⟨13702223505965462590272259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18269631341287283453696345 13702223505965462590272259)
          ·
            refine ⟨20553335258948193885408389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13702223505965462590272259 20553335258948193885408389)
            ·
              refine ⟨3853750361052786353514073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20553335258948193885408389 3853750361052786353514073)
              ·
                refine ⟨2890312770789589765135555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3853750361052786353514073 2890312770789589765135555)
                ·
                  refine ⟨4335469156184384647703333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2890312770789589765135555 4335469156184384647703333)
                  ·
                    refine ⟨812900466784572121444375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4335469156184384647703333 812900466784572121444375)
                    ·
                      rfl

theorem cell23_4749354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_4749354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749354 prefixEnd_4749354 := by exact prefixLift 4749354
  have htrace : WordTrace (prefixWord ++ tailWord_4749354) baseStart_4749354 baseEnd_4749354 := by
    simpa [prefixWord, tailWord_4749354, baseEnd_4749354] using wordTrace_append hprefix tailTrace_4749354
  have hstable : (prefixWord ++ tailWord_4749354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749354).length < 2 ^ (prefixWord ++ tailWord_4749354).sum := by decide
  have hdescent : baseEnd_4749354 < baseStart_4749354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749377 : List Nat := [1, 2, 5, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_4749377 : Nat := 118140960795 + 4749377 * 2 ^ 59
def prefixEnd_4749377 : Nat := 4983230072969 + 3 ^ 40 * 4749377 * 2
def baseEnd_4749377 : Nat := 2438713210408769774345519

theorem tailTrace_4749377 : CollatzResearch.WordTrace tailWord_4749377 prefixEnd_4749377 2438713210408769774345519 := by
  unfold tailWord_4749377
  simp only [CollatzResearch.WordTrace]
  refine ⟨173224010114825732859430385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115482673409883821906286923 173224010114825732859430385)
  ·
    refine ⟨129918007586119299644572789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173224010114825732859430385 129918007586119299644572789)
    ·
      refine ⟨12179813211198684341678699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 129918007586119299644572789 12179813211198684341678699)
      ·
        refine ⟨18269719816798026512518049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12179813211198684341678699 18269719816798026512518049)
        ·
          refine ⟨13702289862598519884388537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18269719816798026512518049 13702289862598519884388537)
          ·
            refine ⟨10276717396948889913291403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13702289862598519884388537 10276717396948889913291403)
            ·
              refine ⟨15415076095423334869937105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10276717396948889913291403 15415076095423334869937105)
              ·
                refine ⟨11561307071567501152452829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15415076095423334869937105 11561307071567501152452829)
                ·
                  refine ⟨4335490151837812932169811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11561307071567501152452829 4335490151837812932169811)
                  ·
                    refine ⟨6503235227756719398254717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4335490151837812932169811 6503235227756719398254717)
                    ·
                      refine ⟨2438713210408769774345519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6503235227756719398254717 2438713210408769774345519)
                      ·
                        rfl

theorem cell23_4749377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_4749377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749377 prefixEnd_4749377 := by exact prefixLift 4749377
  have htrace : WordTrace (prefixWord ++ tailWord_4749377) baseStart_4749377 baseEnd_4749377 := by
    simpa [prefixWord, tailWord_4749377, baseEnd_4749377] using wordTrace_append hprefix tailTrace_4749377
  have hstable : (prefixWord ++ tailWord_4749377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749377).length < 2 ^ (prefixWord ++ tailWord_4749377).sum := by decide
  have hdescent : baseEnd_4749377 < baseStart_4749377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749383 : List Nat := [1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 4]
def baseStart_4749383 : Nat := 118140960795 + 4749383 * 2 ^ 59
def prefixEnd_4749383 : Nat := 4983230072969 + 3 ^ 40 * 4749383 * 2
def baseEnd_4749383 : Nat := 2438716291292696750870491

theorem tailTrace_4749383 : CollatzResearch.WordTrace tailWord_4749383 prefixEnd_4749383 2438716291292696750870491 := by
  unfold tailWord_4749383
  simp only [CollatzResearch.WordTrace]
  refine ⟨173224228952803995884148803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115482819301869330589432535 173224228952803995884148803)
  ·
    refine ⟨259836343429205993826223205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173224228952803995884148803 259836343429205993826223205)
    ·
      refine ⟨48719314392976123842416851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 259836343429205993826223205 48719314392976123842416851)
      ·
        refine ⟨73078971589464185763625277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48719314392976123842416851 73078971589464185763625277)
        ·
          refine ⟨27404614346049069661359479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73078971589464185763625277 27404614346049069661359479)
          ·
            refine ⟨41106921519073604492039219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27404614346049069661359479 41106921519073604492039219)
            ·
              refine ⟨61660382278610406738058829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41106921519073604492039219 61660382278610406738058829)
              ·
                refine ⟨23122643354478902526772061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61660382278610406738058829 23122643354478902526772061)
                ·
                  refine ⟨8670991257929588447539523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23122643354478902526772061 8670991257929588447539523)
                  ·
                    refine ⟨13006486886894382671309285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8670991257929588447539523 13006486886894382671309285)
                    ·
                      refine ⟨2438716291292696750870491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13006486886894382671309285 2438716291292696750870491)
                      ·
                        rfl

theorem cell23_4749383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_4749383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749383 prefixEnd_4749383 := by exact prefixLift 4749383
  have htrace : WordTrace (prefixWord ++ tailWord_4749383) baseStart_4749383 baseEnd_4749383 := by
    simpa [prefixWord, tailWord_4749383, baseEnd_4749383] using wordTrace_append hprefix tailTrace_4749383
  have hstable : (prefixWord ++ tailWord_4749383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749383).length < 2 ^ (prefixWord ++ tailWord_4749383).sum := by decide
  have hdescent : baseEnd_4749383 < baseStart_4749383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749393 : List Nat := [1, 2, 2, 1, 3, 1, 1, 4, 4, 4]
def baseStart_4749393 : Nat := 118140960795 + 4749393 * 2 ^ 59
def prefixEnd_4749393 : Nat := 4983230072969 + 3 ^ 40 * 4749393 * 2
def baseEnd_4749393 : Nat := 812907142033080570581815

theorem tailTrace_4749393 : CollatzResearch.WordTrace tailWord_4749393 prefixEnd_4749393 812907142033080570581815 := by
  unfold tailWord_4749393
  simp only [CollatzResearch.WordTrace]
  refine ⟨173224593682767767592012833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115483062455178511728008555 173224593682767767592012833)
  ·
    refine ⟨129918445262075825694009625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173224593682767767592012833 129918445262075825694009625)
    ·
      refine ⟨97438833946556869270507219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129918445262075825694009625 97438833946556869270507219)
      ·
        refine ⟨146158250919835303905760829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97438833946556869270507219 146158250919835303905760829)
        ·
          refine ⟨54809344094938238964660311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146158250919835303905760829 54809344094938238964660311)
          ·
            refine ⟨82214016142407358446990467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54809344094938238964660311 82214016142407358446990467)
            ·
              refine ⟨123321024213611037670485701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82214016142407358446990467 123321024213611037670485701)
              ·
                refine ⟨23122692040052069563216069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123321024213611037670485701 23122692040052069563216069)
                ·
                  refine ⟨4335504757509763043103013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23122692040052069563216069 4335504757509763043103013)
                  ·
                    refine ⟨812907142033080570581815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4335504757509763043103013 812907142033080570581815)
                    ·
                      rfl

theorem cell23_4749393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4, 4].length) (baseStart_4749393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749393 prefixEnd_4749393 := by exact prefixLift 4749393
  have htrace : WordTrace (prefixWord ++ tailWord_4749393) baseStart_4749393 baseEnd_4749393 := by
    simpa [prefixWord, tailWord_4749393, baseEnd_4749393] using wordTrace_append hprefix tailTrace_4749393
  have hstable : (prefixWord ++ tailWord_4749393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749393).length < 2 ^ (prefixWord ++ tailWord_4749393).sum := by decide
  have hdescent : baseEnd_4749393 < baseStart_4749393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749397 : List Nat := [1, 3, 2, 2, 1, 5, 2, 1, 1, 5]
def baseStart_4749397 : Nat := 118140960795 + 4749397 * 2 ^ 59
def prefixEnd_4749397 : Nat := 4983230072969 + 3 ^ 40 * 4749397 * 2
def baseEnd_4749397 : Nat := 812907826673953232031809

theorem tailTrace_4749397 : CollatzResearch.WordTrace tailWord_4749397 prefixEnd_4749397 812907826673953232031809 := by
  unfold tailWord_4749397
  simp only [CollatzResearch.WordTrace]
  refine ⟨173224739574753276275158445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115483159716502184183438963 173224739574753276275158445)
  ·
    refine ⟨64959277340532478603184417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173224739574753276275158445 64959277340532478603184417)
    ·
      refine ⟨48719458005399358952388313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64959277340532478603184417 48719458005399358952388313)
      ·
        refine ⟨36539593504049519214291235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48719458005399358952388313 36539593504049519214291235)
        ·
          refine ⟨54809390256074278821436853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36539593504049519214291235 54809390256074278821436853)
          ·
            refine ⟨5138380336506963639509705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54809390256074278821436853 5138380336506963639509705)
            ·
              refine ⟨3853785252380222729632279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5138380336506963639509705 3853785252380222729632279)
              ·
                refine ⟨5780677878570334094448419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3853785252380222729632279 5780677878570334094448419)
                ·
                  refine ⟨8671016817855501141672629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5780677878570334094448419 8671016817855501141672629)
                  ·
                    refine ⟨812907826673953232031809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8671016817855501141672629 812907826673953232031809)
                    ·
                      rfl

theorem cell23_4749397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_4749397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749397 prefixEnd_4749397 := by exact prefixLift 4749397
  have htrace : WordTrace (prefixWord ++ tailWord_4749397) baseStart_4749397 baseEnd_4749397 := by
    simpa [prefixWord, tailWord_4749397, baseEnd_4749397] using wordTrace_append hprefix tailTrace_4749397
  have hstable : (prefixWord ++ tailWord_4749397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749397).length < 2 ^ (prefixWord ++ tailWord_4749397).sum := by decide
  have hdescent : baseEnd_4749397 < baseStart_4749397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749400 : List Nat := [2, 1, 2, 2, 1, 5, 1, 3, 1, 1, 4]
def baseStart_4749400 : Nat := 118140960795 + 4749400 * 2 ^ 59
def prefixEnd_4749400 : Nat := 4983230072969 + 3 ^ 40 * 4749400 * 2
def baseEnd_4749400 : Nat := 2438725020463823184357913

theorem tailTrace_4749400 : CollatzResearch.WordTrace tailWord_4749400 prefixEnd_4749400 2438725020463823184357913 := by
  unfold tailWord_4749400
  simp only [CollatzResearch.WordTrace]
  refine ⟨86612424496871203893758827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115483232662494938525011769 86612424496871203893758827)
  ·
    refine ⟨129918636745306805840638241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86612424496871203893758827 129918636745306805840638241)
    ·
      refine ⟨97438977558980104380478681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129918636745306805840638241 97438977558980104380478681)
      ·
        refine ⟨73079233169235078285359011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97438977558980104380478681 73079233169235078285359011)
        ·
          refine ⟨109618849753852617428038517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73079233169235078285359011 109618849753852617428038517)
          ·
            refine ⟨10276767164423682883878611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 109618849753852617428038517 10276767164423682883878611)
            ·
              refine ⟨15415150746635524325817917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10276767164423682883878611 15415150746635524325817917)
              ·
                refine ⟨5780681529988321622181719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15415150746635524325817917 5780681529988321622181719)
                ·
                  refine ⟨8671022294982482433272579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5780681529988321622181719 8671022294982482433272579)
                  ·
                    refine ⟨13006533442473723649908869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8671022294982482433272579 13006533442473723649908869)
                    ·
                      refine ⟨2438725020463823184357913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13006533442473723649908869 2438725020463823184357913)
                      ·
                        rfl

theorem cell23_4749400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_4749400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749400 prefixEnd_4749400 := by exact prefixLift 4749400
  have htrace : WordTrace (prefixWord ++ tailWord_4749400) baseStart_4749400 baseEnd_4749400 := by
    simpa [prefixWord, tailWord_4749400, baseEnd_4749400] using wordTrace_append hprefix tailTrace_4749400
  have hstable : (prefixWord ++ tailWord_4749400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749400).length < 2 ^ (prefixWord ++ tailWord_4749400).sum := by decide
  have hdescent : baseEnd_4749400 < baseStart_4749400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749417 : List Nat := [1, 2, 1, 1, 1, 5, 4, 1, 3, 2, 2]
def baseStart_4749417 : Nat := 118140960795 + 4749417 * 2 ^ 59
def prefixEnd_4749417 : Nat := 4983230072969 + 3 ^ 40 * 4749417 * 2
def baseEnd_4749417 : Nat := 2438733749634949617845335

theorem tailTrace_4749417 : CollatzResearch.WordTrace tailWord_4749417 prefixEnd_4749417 2438733749634949617845335 := by
  unfold tailWord_4749417
  simp only [CollatzResearch.WordTrace]
  refine ⟨173225469034680819690886505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115483646023120546460591003 173225469034680819690886505)
  ·
    refine ⟨129919101776010614768164879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173225469034680819690886505 129919101776010614768164879)
    ·
      refine ⟨194878652664015922152247319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129919101776010614768164879 194878652664015922152247319)
      ·
        refine ⟨292317978996023883228370979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194878652664015922152247319 292317978996023883228370979)
        ·
          refine ⟨438476968494035824842556469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292317978996023883228370979 438476968494035824842556469)
          ·
            refine ⟨41107215796315858578989669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 438476968494035824842556469 41107215796315858578989669)
            ·
              refine ⟨7707602961809223483560563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41107215796315858578989669 7707602961809223483560563)
              ·
                refine ⟨11561404442713835225340845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7707602961809223483560563 11561404442713835225340845)
                ·
                  refine ⟨4335526666017688209502817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11561404442713835225340845 4335526666017688209502817)
                  ·
                    refine ⟨3251644999513266157127113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4335526666017688209502817 3251644999513266157127113)
                    ·
                      refine ⟨2438733749634949617845335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3251644999513266157127113 2438733749634949617845335)
                      ·
                        rfl

theorem cell23_4749417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3, 2, 2].length) (baseStart_4749417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749417 prefixEnd_4749417 := by exact prefixLift 4749417
  have htrace : WordTrace (prefixWord ++ tailWord_4749417) baseStart_4749417 baseEnd_4749417 := by
    simpa [prefixWord, tailWord_4749417, baseEnd_4749417] using wordTrace_append hprefix tailTrace_4749417
  have hstable : (prefixWord ++ tailWord_4749417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749417).length < 2 ^ (prefixWord ++ tailWord_4749417).sum := by decide
  have hdescent : baseEnd_4749417 < baseStart_4749417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749430 : List Nat := [5, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_4749430 : Nat := 118140960795 + 4749430 * 2 ^ 59
def prefixEnd_4749430 : Nat := 4983230072969 + 3 ^ 40 * 4749430 * 2
def baseEnd_4749430 : Nat := 2438740424883458066982775

theorem tailTrace_4749430 : CollatzResearch.WordTrace tailWord_4749430 prefixEnd_4749430 2438740424883458066982775 := by
  unfold tailWord_4749430
  simp only [CollatzResearch.WordTrace]
  refine ⟨10826621448977107681944359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115483962122422481940739829 10826621448977107681944359)
  ·
    refine ⟨16239932173465661522916539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10826621448977107681944359 16239932173465661522916539)
    ·
      refine ⟨24359898260198492284374809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16239932173465661522916539 24359898260198492284374809)
      ·
        refine ⟨18269923695148869213281107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24359898260198492284374809 18269923695148869213281107)
        ·
          refine ⟨27404885542723303819921661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18269923695148869213281107 27404885542723303819921661)
          ·
            refine ⟨10276832078521238932470623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27404885542723303819921661 10276832078521238932470623)
            ·
              refine ⟨15415248117781858398705935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10276832078521238932470623 15415248117781858398705935)
              ·
                refine ⟨23122872176672787598058903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15415248117781858398705935 23122872176672787598058903)
                ·
                  refine ⟨34684308265009181397088355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23122872176672787598058903 34684308265009181397088355)
                  ·
                    refine ⟨52026462397513772095632533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34684308265009181397088355 52026462397513772095632533)
                    ·
                      refine ⟨2438740424883458066982775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52026462397513772095632533 2438740424883458066982775)
                      ·
                        rfl

theorem cell23_4749430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_4749430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749430 prefixEnd_4749430 := by exact prefixLift 4749430
  have htrace : WordTrace (prefixWord ++ tailWord_4749430) baseStart_4749430 baseEnd_4749430 := by
    simpa [prefixWord, tailWord_4749430, baseEnd_4749430] using wordTrace_append hprefix tailTrace_4749430
  have hstable : (prefixWord ++ tailWord_4749430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749430).length < 2 ^ (prefixWord ++ tailWord_4749430).sum := by decide
  have hdescent : baseEnd_4749430 < baseStart_4749430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749437 : List Nat := [1, 4, 1, 1, 3, 3, 2, 2, 1, 2, 3]
def baseStart_4749437 : Nat := 118140960795 + 4749437 * 2 ^ 59
def prefixEnd_4749437 : Nat := 4983230072969 + 3 ^ 40 * 4749437 * 2
def baseEnd_4749437 : Nat := 2438744019248039539595243

theorem tailTrace_4749437 : CollatzResearch.WordTrace tailWord_4749437 prefixEnd_4749437 2438744019248039539595243 := by
  unfold tailWord_4749437
  simp only [CollatzResearch.WordTrace]
  refine ⟨173226198494608363106614565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115484132329738908737743043 173226198494608363106614565)
  ·
    refine ⟨32479912217739068082490231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173226198494608363106614565 32479912217739068082490231)
    ·
      refine ⟨48719868326608602123735347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32479912217739068082490231 48719868326608602123735347)
      ·
        refine ⟨73079802489912903185603021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48719868326608602123735347 73079802489912903185603021)
        ·
          refine ⟨27404925933717338694601133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73079802489912903185603021 27404925933717338694601133)
          ·
            refine ⟨10276847225144002010475425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27404925933717338694601133 10276847225144002010475425)
            ·
              refine ⟨7707635418858001507856569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10276847225144002010475425 7707635418858001507856569)
              ·
                refine ⟨5780726564143501130892427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7707635418858001507856569 5780726564143501130892427)
                ·
                  refine ⟨8671089846215251696338641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5780726564143501130892427 8671089846215251696338641)
                  ·
                    refine ⟨6503317384661438772253981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8671089846215251696338641 6503317384661438772253981)
                    ·
                      refine ⟨2438744019248039539595243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6503317384661438772253981 2438744019248039539595243)
                      ·
                        rfl

theorem cell23_4749437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_4749437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749437 prefixEnd_4749437 := by exact prefixLift 4749437
  have htrace : WordTrace (prefixWord ++ tailWord_4749437) baseStart_4749437 baseEnd_4749437 := by
    simpa [prefixWord, tailWord_4749437, baseEnd_4749437] using wordTrace_append hprefix tailTrace_4749437
  have hstable : (prefixWord ++ tailWord_4749437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749437).length < 2 ^ (prefixWord ++ tailWord_4749437).sum := by decide
  have hdescent : baseEnd_4749437 < baseStart_4749437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749462 : List Nat := [5, 3, 2, 1, 2, 1, 1, 1, 3, 1, 3]
def baseStart_4749462 : Nat := 118140960795 + 4749462 * 2 ^ 59
def prefixEnd_4749462 : Nat := 4983230072969 + 3 ^ 40 * 4749462 * 2
def baseEnd_4749462 : Nat := 2438756856264401941782629

theorem tailTrace_4749462 : CollatzResearch.WordTrace tailWord_4749462 prefixEnd_4749462 2438756856264401941782629 := by
  unfold tailWord_4749462
  simp only [CollatzResearch.WordTrace]
  refine ⟨10826694394969862023517165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115484740213011861584183093 10826694394969862023517165)
  ·
    refine ⟨4060010398113698258818937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10826694394969862023517165 4060010398113698258818937)
    ·
      refine ⟨3045007798585273694114203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4060010398113698258818937 3045007798585273694114203)
      ·
        refine ⟨4567511697877910541171305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3045007798585273694114203 4567511697877910541171305)
        ·
          refine ⟨3425633773408432905878479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4567511697877910541171305 3425633773408432905878479)
          ·
            refine ⟨5138450660112649358817719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3425633773408432905878479 5138450660112649358817719)
            ·
              refine ⟨7707675990168974038226579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5138450660112649358817719 7707675990168974038226579)
              ·
                refine ⟨11561513985253461057339869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7707675990168974038226579 11561513985253461057339869)
                ·
                  refine ⟨4335567744470047896502451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11561513985253461057339869 4335567744470047896502451)
                  ·
                    refine ⟨6503351616705071844753677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4335567744470047896502451 6503351616705071844753677)
                    ·
                      refine ⟨2438756856264401941782629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6503351616705071844753677 2438756856264401941782629)
                      ·
                        rfl

theorem cell23_4749462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_4749462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749462 prefixEnd_4749462 := by exact prefixLift 4749462
  have htrace : WordTrace (prefixWord ++ tailWord_4749462) baseStart_4749462 baseEnd_4749462 := by
    simpa [prefixWord, tailWord_4749462, baseEnd_4749462] using wordTrace_append hprefix tailTrace_4749462
  have hstable : (prefixWord ++ tailWord_4749462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749462).length < 2 ^ (prefixWord ++ tailWord_4749462).sum := by decide
  have hdescent : baseEnd_4749462 < baseStart_4749462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749503 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 4]
def baseStart_4749503 : Nat := 118140960795 + 4749503 * 2 ^ 59
def prefixEnd_4749503 : Nat := 4983230072969 + 3 ^ 40 * 4749503 * 2
def baseEnd_4749503 : Nat := 2438777908971236281369939

theorem tailTrace_4749503 : CollatzResearch.WordTrace tailWord_4749503 prefixEnd_4749503 2438777908971236281369939 := by
  unfold tailWord_4749503
  simp only [CollatzResearch.WordTrace]
  refine ⟨173228605712369256378517163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115485737141579504252344775 173228605712369256378517163)
  ·
    refine ⟨259842908568553884567775745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173228605712369256378517163 259842908568553884567775745)
    ·
      refine ⟨194882181426415413425831809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259842908568553884567775745 194882181426415413425831809)
      ·
        refine ⟨146161636069811560069373857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194882181426415413425831809 146161636069811560069373857)
        ·
          refine ⟨109621227052358670052030393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146161636069811560069373857 109621227052358670052030393)
          ·
            refine ⟨82215920289269002539022795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109621227052358670052030393 82215920289269002539022795)
            ·
              refine ⟨123323880433903503808534193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82215920289269002539022795 123323880433903503808534193)
              ·
                refine ⟨92492910325427627856400645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123323880433903503808534193 92492910325427627856400645)
                ·
                  refine ⟨17342420686017680223075121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92492910325427627856400645 17342420686017680223075121)
                  ·
                    refine ⟨13006815514513260167306341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17342420686017680223075121 13006815514513260167306341)
                    ·
                      refine ⟨2438777908971236281369939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13006815514513260167306341 2438777908971236281369939)
                      ·
                        rfl

theorem cell23_4749503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_4749503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749503 prefixEnd_4749503 := by exact prefixLift 4749503
  have htrace : WordTrace (prefixWord ++ tailWord_4749503) baseStart_4749503 baseEnd_4749503 := by
    simpa [prefixWord, tailWord_4749503, baseEnd_4749503] using wordTrace_append hprefix tailTrace_4749503
  have hstable : (prefixWord ++ tailWord_4749503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749503).length < 2 ^ (prefixWord ++ tailWord_4749503).sum := by decide
  have hdescent : baseEnd_4749503 < baseStart_4749503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749553 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 1, 1, 7]
def baseStart_4749553 : Nat := 118140960795 + 4749553 * 2 ^ 59
def prefixEnd_4749553 : Nat := 4983230072969 + 3 ^ 40 * 4749553 * 2
def baseEnd_4749553 : Nat := 2438803583003961085744709

theorem tailTrace_4749553 : CollatzResearch.WordTrace tailWord_4749553 prefixEnd_4749553 2438803583003961085744709 := by
  unfold tailWord_4749553
  simp only [CollatzResearch.WordTrace]
  refine ⟨173230429362188114917837313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115486952908125409945224875 173230429362188114917837313)
  ·
    refine ⟨129922822021641086188377985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173230429362188114917837313 129922822021641086188377985)
    ·
      refine ⟨97442116516230814641283489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129922822021641086188377985 97442116516230814641283489)
      ·
        refine ⟨73081587387173110980962617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97442116516230814641283489 73081587387173110980962617)
        ·
          refine ⟨54811190540379833235721963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73081587387173110980962617 54811190540379833235721963)
          ·
            refine ⟨82216785810569749853582945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54811190540379833235721963 82216785810569749853582945)
            ·
              refine ⟨61662589357927312390187209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82216785810569749853582945 61662589357927312390187209)
              ·
                refine ⟨46246942018445484292640407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61662589357927312390187209 46246942018445484292640407)
                ·
                  refine ⟨69370413027668226438960611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46246942018445484292640407 69370413027668226438960611)
                  ·
                    refine ⟨104055619541502339658440917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69370413027668226438960611 104055619541502339658440917)
                    ·
                      refine ⟨2438803583003961085744709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104055619541502339658440917 2438803583003961085744709)
                      ·
                        rfl

theorem cell23_4749553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_4749553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749553 prefixEnd_4749553 := by exact prefixLift 4749553
  have htrace : WordTrace (prefixWord ++ tailWord_4749553) baseStart_4749553 baseEnd_4749553 := by
    simpa [prefixWord, tailWord_4749553, baseEnd_4749553] using wordTrace_append hprefix tailTrace_4749553
  have hstable : (prefixWord ++ tailWord_4749553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749553).length < 2 ^ (prefixWord ++ tailWord_4749553).sum := by decide
  have hdescent : baseEnd_4749553 < baseStart_4749553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4749575 : List Nat := [1, 1, 4, 5, 2, 1, 1, 2, 2, 2, 2]
def baseStart_4749575 : Nat := 118140960795 + 4749575 * 2 ^ 59
def prefixEnd_4749575 : Nat := 4983230072969 + 3 ^ 40 * 4749575 * 2
def baseEnd_4749575 : Nat := 2438814879578359999669609

theorem tailTrace_4749575 : CollatzResearch.WordTrace tailWord_4749575 prefixEnd_4749575 2438814879578359999669609 := by
  unfold tailWord_4749575
  simp only [CollatzResearch.WordTrace]
  refine ⟨173231231768108412675138179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115487487845405608450092119 173231231768108412675138179)
  ·
    refine ⟨259846847652162619012707269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173231231768108412675138179 259846847652162619012707269)
    ·
      refine ⟨48721283934780491064882613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 259846847652162619012707269 48721283934780491064882613)
      ·
        refine ⟨4567620368885671037332745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48721283934780491064882613 4567620368885671037332745)
        ·
          refine ⟨3425715276664253277999559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4567620368885671037332745 3425715276664253277999559)
          ·
            refine ⟨5138572914996379916999339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3425715276664253277999559 5138572914996379916999339)
            ·
              refine ⟨7707859372494569875499009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5138572914996379916999339 7707859372494569875499009)
              ·
                refine ⟨5780894529370927406624257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7707859372494569875499009 5780894529370927406624257)
                ·
                  refine ⟨4335670897028195554968193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5780894529370927406624257 4335670897028195554968193)
                  ·
                    refine ⟨3251753172771146666226145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4335670897028195554968193 3251753172771146666226145)
                    ·
                      refine ⟨2438814879578359999669609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3251753172771146666226145 2438814879578359999669609)
                      ·
                        rfl

theorem cell23_4749575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_4749575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4749575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4749575 prefixEnd_4749575 := by exact prefixLift 4749575
  have htrace : WordTrace (prefixWord ++ tailWord_4749575) baseStart_4749575 baseEnd_4749575 := by
    simpa [prefixWord, tailWord_4749575, baseEnd_4749575] using wordTrace_append hprefix tailTrace_4749575
  have hstable : (prefixWord ++ tailWord_4749575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4749575).length < 2 ^ (prefixWord ++ tailWord_4749575).sum := by decide
  have hdescent : baseEnd_4749575 < baseStart_4749575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4749575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
