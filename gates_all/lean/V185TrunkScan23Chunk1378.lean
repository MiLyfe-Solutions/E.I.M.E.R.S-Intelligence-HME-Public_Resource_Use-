import V185TrunkScan23Chunk1377

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8162217 : List Nat := [1, 2, 1, 1, 1, 1, 5, 5, 6]
def baseStart_8162217 : Nat := 118140960795 + 8162217 * 2 ^ 59
def prefixEnd_8162217 : Nat := 4983230072969 + 3 ^ 40 * 8162217 * 2
def baseEnd_8162217 : Nat := 465682280811021891350017

theorem tailTrace_8162217 : CollatzResearch.WordTrace tailWord_8162217 prefixEnd_8162217 465682280811021891350017 := by
  unfold tailWord_8162217
  simp only [CollatzResearch.WordTrace]
  refine ⟨297700511070689279527044905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198467007380459519684696603 297700511070689279527044905)
  ·
    refine ⟨223275383303016959645283679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297700511070689279527044905 223275383303016959645283679)
    ·
      refine ⟨334913074954525439467925519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223275383303016959645283679 334913074954525439467925519)
      ·
        refine ⟨502369612431788159201888279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334913074954525439467925519 502369612431788159201888279)
        ·
          refine ⟨753554418647682238802832419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502369612431788159201888279 753554418647682238802832419)
          ·
            refine ⟨1130331627971523358204248629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753554418647682238802832419 1130331627971523358204248629)
            ·
              refine ⟨105968590122330314831648309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1130331627971523358204248629 105968590122330314831648309)
              ·
                refine ⟨9934555323968467015467029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105968590122330314831648309 9934555323968467015467029)
                ·
                  refine ⟨465682280811021891350017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9934555323968467015467029 465682280811021891350017)
                  ·
                    rfl

theorem cell23_8162217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 6].length) (baseStart_8162217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162217 prefixEnd_8162217 := by exact prefixLift 8162217
  have htrace : WordTrace (prefixWord ++ tailWord_8162217) baseStart_8162217 baseEnd_8162217 := by
    simpa [prefixWord, tailWord_8162217, baseEnd_8162217] using wordTrace_append hprefix tailTrace_8162217
  have hstable : (prefixWord ++ tailWord_8162217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162217).length < 2 ^ (prefixWord ++ tailWord_8162217).sum := by decide
  have hdescent : baseEnd_8162217 < baseStart_8162217 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162227 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 1, 7, 3]
def baseStart_8162227 : Nat := 118140960795 + 8162227 * 2 ^ 59
def prefixEnd_8162227 : Nat := 4983230072969 + 3 ^ 40 * 8162227 * 2
def baseEnd_8162227 : Nat := 4191145662105741983025107

theorem tailTrace_8162227 : CollatzResearch.WordTrace tailWord_8162227 prefixEnd_8162227 4191145662105741983025107 := by
  unfold tailWord_8162227
  simp only [CollatzResearch.WordTrace]
  refine ⟨297700875800653051234908935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198467250533768700823272623 297700875800653051234908935)
  ·
    refine ⟨446551313700979576852363403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297700875800653051234908935 446551313700979576852363403)
    ·
      refine ⟨669826970551469365278545105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446551313700979576852363403 669826970551469365278545105)
      ·
        refine ⟨502370227913602023958908829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 669826970551469365278545105 502370227913602023958908829)
        ·
          refine ⟨188388835467600758984590811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 502370227913602023958908829 188388835467600758984590811)
          ·
            refine ⟨282583253201401138476886217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188388835467600758984590811 282583253201401138476886217)
            ·
              refine ⟨211937439901050853857664663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282583253201401138476886217 211937439901050853857664663)
              ·
                refine ⟨317906159851576280786496995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211937439901050853857664663 317906159851576280786496995)
                ·
                  refine ⟨476859239777364421179745493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317906159851576280786496995 476859239777364421179745493)
                  ·
                    refine ⟨11176388432281978621400285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 476859239777364421179745493 11176388432281978621400285)
                    ·
                      refine ⟨4191145662105741983025107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11176388432281978621400285 4191145662105741983025107)
                      ·
                        rfl

theorem cell23_8162227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7, 3].length) (baseStart_8162227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162227 prefixEnd_8162227 := by exact prefixLift 8162227
  have htrace : WordTrace (prefixWord ++ tailWord_8162227) baseStart_8162227 baseEnd_8162227 := by
    simpa [prefixWord, tailWord_8162227, baseEnd_8162227] using wordTrace_append hprefix tailTrace_8162227
  have hstable : (prefixWord ++ tailWord_8162227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162227).length < 2 ^ (prefixWord ++ tailWord_8162227).sum := by decide
  have hdescent : baseEnd_8162227 < baseStart_8162227 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162228 : List Nat := [2, 5, 2, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_8162228 : Nat := 118140960795 + 8162228 * 2 ^ 59
def prefixEnd_8162228 : Nat := 4983230072969 + 3 ^ 40 * 8162228 * 2
def baseEnd_8162228 : Nat := 4191146175586396479112603

theorem tailTrace_8162228 : CollatzResearch.WordTrace tailWord_8162228 prefixEnd_8162228 4191146175586396479112603 := by
  unfold tailWord_8162228
  simp only [CollatzResearch.WordTrace]
  refine ⟨148850456136824714202847669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198467274849099618937130225 148850456136824714202847669)
  ·
    refine ⟨13954730262827316956516969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148850456136824714202847669 13954730262827316956516969)
    ·
      refine ⟨10466047697120487717387727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13954730262827316956516969 10466047697120487717387727)
      ·
        refine ⟨15699071545680731576081591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10466047697120487717387727 15699071545680731576081591)
        ·
          refine ⟨23548607318521097364122387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15699071545680731576081591 23548607318521097364122387)
          ·
            refine ⟨35322910977781646046183581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23548607318521097364122387 35322910977781646046183581)
            ·
              refine ⟨13246091616668117267318843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35322910977781646046183581 13246091616668117267318843)
              ·
                refine ⟨19869137425002175900978265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13246091616668117267318843 19869137425002175900978265)
                ·
                  refine ⟨14901853068751631925733699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19869137425002175900978265 14901853068751631925733699)
                  ·
                    refine ⟨22352779603127447888600549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14901853068751631925733699 22352779603127447888600549)
                    ·
                      refine ⟨4191146175586396479112603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22352779603127447888600549 4191146175586396479112603)
                      ·
                        rfl

theorem cell23_8162228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_8162228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162228 prefixEnd_8162228 := by exact prefixLift 8162228
  have htrace : WordTrace (prefixWord ++ tailWord_8162228) baseStart_8162228 baseEnd_8162228 := by
    simpa [prefixWord, tailWord_8162228, baseEnd_8162228] using wordTrace_append hprefix tailTrace_8162228
  have hstable : (prefixWord ++ tailWord_8162228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162228).length < 2 ^ (prefixWord ++ tailWord_8162228).sum := by decide
  have hdescent : baseEnd_8162228 < baseStart_8162228 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162238 : List Nat := [4, 2, 1, 1, 1, 2, 4, 3, 1, 4]
def baseStart_8162238 : Nat := 118140960795 + 8162238 * 2 ^ 59
def prefixEnd_8162238 : Nat := 4983230072969 + 3 ^ 40 * 8162238 * 2
def baseEnd_8162238 : Nat := 1397050436797647146662519

theorem tailTrace_8162238 : CollatzResearch.WordTrace tailWord_8162238 prefixEnd_8162238 1397050436797647146662519 := by
  unfold tailWord_8162238
  simp only [CollatzResearch.WordTrace]
  refine ⟨37212659625451650014194921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198467518002408800075706245 37212659625451650014194921)
  ·
    refine ⟨27909494719088737510646191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37212659625451650014194921 27909494719088737510646191)
    ·
      refine ⟨41864242078633106265969287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27909494719088737510646191 41864242078633106265969287)
      ·
        refine ⟨62796363117949659398953931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41864242078633106265969287 62796363117949659398953931)
        ·
          refine ⟨94194544676924489098430897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62796363117949659398953931 94194544676924489098430897)
          ·
            refine ⟨70645908507693366823823173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94194544676924489098430897 70645908507693366823823173)
            ·
              refine ⟨13246107845192506279466845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70645908507693366823823173 13246107845192506279466845)
              ·
                refine ⟨4967290441947189854800067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13246107845192506279466845 4967290441947189854800067)
                ·
                  refine ⟨7450935662920784782200101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4967290441947189854800067 7450935662920784782200101)
                  ·
                    refine ⟨1397050436797647146662519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7450935662920784782200101 1397050436797647146662519)
                    ·
                      rfl

theorem cell23_8162238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_8162238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162238 prefixEnd_8162238 := by exact prefixLift 8162238
  have htrace : WordTrace (prefixWord ++ tailWord_8162238) baseStart_8162238 baseEnd_8162238 := by
    simpa [prefixWord, tailWord_8162238, baseEnd_8162238] using wordTrace_append hprefix tailTrace_8162238
  have hstable : (prefixWord ++ tailWord_8162238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162238).length < 2 ^ (prefixWord ++ tailWord_8162238).sum := by decide
  have hdescent : baseEnd_8162238 < baseStart_8162238 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162311 : List Nat := [1, 1, 4, 3, 1, 1, 2, 4, 2, 4]
def baseStart_8162311 : Nat := 118140960795 + 8162311 * 2 ^ 59
def prefixEnd_8162311 : Nat := 4983230072969 + 3 ^ 40 * 8162311 * 2
def baseEnd_8162311 : Nat := 1397062931493573218124907

theorem tailTrace_8162311 : CollatzResearch.WordTrace tailWord_8162311 prefixEnd_8162311 1397062931493573218124907 := by
  unfold tailWord_8162311
  simp only [CollatzResearch.WordTrace]
  refine ⟨297703939532348733580966787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198469293021565822387311191 297703939532348733580966787)
  ·
    refine ⟨446555909298523100371450181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297703939532348733580966787 446555909298523100371450181)
    ·
      refine ⟨83729232993473081319646909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 446555909298523100371450181 83729232993473081319646909)
      ·
        refine ⟨31398462372552405494867591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83729232993473081319646909 31398462372552405494867591)
        ·
          refine ⟨47097693558828608242301387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31398462372552405494867591 47097693558828608242301387)
          ·
            refine ⟨70646540338242912363452081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47097693558828608242301387 70646540338242912363452081)
            ·
              refine ⟨52984905253682184272589061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70646540338242912363452081 52984905253682184272589061)
              ·
                refine ⟨9934669735065409551110449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52984905253682184272589061 9934669735065409551110449)
                ·
                  refine ⟨7451002301299057163332837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9934669735065409551110449 7451002301299057163332837)
                  ·
                    refine ⟨1397062931493573218124907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7451002301299057163332837 1397062931493573218124907)
                    ·
                      rfl

theorem cell23_8162311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_8162311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162311 prefixEnd_8162311 := by exact prefixLift 8162311
  have htrace : WordTrace (prefixWord ++ tailWord_8162311) baseStart_8162311 baseEnd_8162311 := by
    simpa [prefixWord, tailWord_8162311, baseEnd_8162311] using wordTrace_append hprefix tailTrace_8162311
  have hstable : (prefixWord ++ tailWord_8162311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162311).length < 2 ^ (prefixWord ++ tailWord_8162311).sum := by decide
  have hdescent : baseEnd_8162311 < baseStart_8162311 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162314 : List Nat := [3, 1, 2, 2, 3, 1, 1, 2, 1, 1, 6]
def baseStart_8162314 : Nat := 118140960795 + 8162314 * 2 ^ 59
def prefixEnd_8162314 : Nat := 4983230072969 + 3 ^ 40 * 8162314 * 2
def baseEnd_8162314 : Nat := 4191190334922683142637207

theorem tailTrace_8162314 : CollatzResearch.WordTrace tailWord_8162314 prefixEnd_8162314 4191190334922683142637207 := by
  unfold tailWord_8162314
  simp only [CollatzResearch.WordTrace]
  refine ⟨74426012237834466273331499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198469365967558576728883997 74426012237834466273331499)
  ·
    refine ⟨111639018356751699409997249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74426012237834466273331499 111639018356751699409997249)
    ·
      refine ⟨83729263767563774557497937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111639018356751699409997249 83729263767563774557497937)
      ·
        refine ⟨62796947825672830918123453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83729263767563774557497937 62796947825672830918123453)
        ·
          refine ⟨23548855434627311594296295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62796947825672830918123453 23548855434627311594296295)
          ·
            refine ⟨35323283151940967391444443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23548855434627311594296295 35323283151940967391444443)
            ·
              refine ⟨52984924727911451087166665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35323283151940967391444443 52984924727911451087166665)
              ·
                refine ⟨39738693545933588315374999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52984924727911451087166665 39738693545933588315374999)
                ·
                  refine ⟨59608040318900382473062499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39738693545933588315374999 59608040318900382473062499)
                  ·
                    refine ⟨89412060478350573709593749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59608040318900382473062499 89412060478350573709593749)
                    ·
                      refine ⟨4191190334922683142637207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89412060478350573709593749 4191190334922683142637207)
                      ·
                        rfl

theorem cell23_8162314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_8162314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162314 prefixEnd_8162314 := by exact prefixLift 8162314
  have htrace : WordTrace (prefixWord ++ tailWord_8162314) baseStart_8162314 baseEnd_8162314 := by
    simpa [prefixWord, tailWord_8162314, baseEnd_8162314] using wordTrace_append hprefix tailTrace_8162314
  have hstable : (prefixWord ++ tailWord_8162314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162314).length < 2 ^ (prefixWord ++ tailWord_8162314).sum := by decide
  have hdescent : baseEnd_8162314 < baseStart_8162314 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162328 : List Nat := [2, 1, 2, 3, 2, 2, 4, 1, 2, 4]
def baseStart_8162328 : Nat := 118140960795 + 8162328 * 2 ^ 59
def prefixEnd_8162328 : Nat := 4983230072969 + 3 ^ 40 * 8162328 * 2
def baseEnd_8162328 : Nat := 1397065841217282029287381

theorem tailTrace_8162328 : CollatzResearch.WordTrace tailWord_8162328 prefixEnd_8162328 1397065841217282029287381 := by
  unfold tailWord_8162328
  simp only [CollatzResearch.WordTrace]
  refine ⟨148852279786643572742167819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198469706382191430322890425 148852279786643572742167819)
  ·
    refine ⟨223278419679965359113251729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148852279786643572742167819 223278419679965359113251729)
    ·
      refine ⟨167458814759974019334938797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223278419679965359113251729 167458814759974019334938797)
      ·
        refine ⟨62797055534990257250602049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167458814759974019334938797 62797055534990257250602049)
        ·
          refine ⟨47097791651242692937951537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62797055534990257250602049 47097791651242692937951537)
          ·
            refine ⟨35323343738432019703463653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47097791651242692937951537 35323343738432019703463653)
            ·
              refine ⟨6623126950956003694399435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35323343738432019703463653 6623126950956003694399435)
              ·
                refine ⟨9934690426434005541599153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6623126950956003694399435 9934690426434005541599153)
                ·
                  refine ⟨7451017819825504156199365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9934690426434005541599153 7451017819825504156199365)
                  ·
                    refine ⟨1397065841217282029287381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7451017819825504156199365 1397065841217282029287381)
                    ·
                      rfl

theorem cell23_8162328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 2, 4].length) (baseStart_8162328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162328 prefixEnd_8162328 := by exact prefixLift 8162328
  have htrace : WordTrace (prefixWord ++ tailWord_8162328) baseStart_8162328 baseEnd_8162328 := by
    simpa [prefixWord, tailWord_8162328, baseEnd_8162328] using wordTrace_append hprefix tailTrace_8162328
  have hstable : (prefixWord ++ tailWord_8162328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162328).length < 2 ^ (prefixWord ++ tailWord_8162328).sum := by decide
  have hdescent : baseEnd_8162328 < baseStart_8162328 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162338 : List Nat := [3, 3, 1, 1, 1, 3, 3, 2, 1, 2, 3]
def baseStart_8162338 : Nat := 118140960795 + 8162338 * 2 ^ 59
def prefixEnd_8162338 : Nat := 4983230072969 + 3 ^ 40 * 8162338 * 2
def baseEnd_8162338 : Nat := 4191202658458391048737097

theorem tailTrace_8162338 : CollatzResearch.WordTrace tailWord_8162338 prefixEnd_8162338 4191202658458391048737097 := by
  unfold tailWord_8162338
  simp only [CollatzResearch.WordTrace]
  refine ⟨74426231075812729298049917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198469949535500611461466445 74426231075812729298049917)
  ·
    refine ⟨27909836653429773486768719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74426231075812729298049917 27909836653429773486768719)
    ·
      refine ⟨41864754980144660230153079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27909836653429773486768719 41864754980144660230153079)
      ·
        refine ⟨62797132470216990345229619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41864754980144660230153079 62797132470216990345229619)
        ·
          refine ⟨94195698705325485517844429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62797132470216990345229619 94195698705325485517844429)
          ·
            refine ⟨35323387014497057069191661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94195698705325485517844429 35323387014497057069191661)
            ·
              refine ⟨13246270130436396400946873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35323387014497057069191661 13246270130436396400946873)
              ·
                refine ⟨9934702597827297300710155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13246270130436396400946873 9934702597827297300710155)
                ·
                  refine ⟨14902053896740945951065233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9934702597827297300710155 14902053896740945951065233)
                  ·
                    refine ⟨11176540422555709463298925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14902053896740945951065233 11176540422555709463298925)
                    ·
                      refine ⟨4191202658458391048737097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11176540422555709463298925 4191202658458391048737097)
                      ·
                        rfl

theorem cell23_8162338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_8162338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162338 prefixEnd_8162338 := by exact prefixLift 8162338
  have htrace : WordTrace (prefixWord ++ tailWord_8162338) baseStart_8162338 baseEnd_8162338 := by
    simpa [prefixWord, tailWord_8162338, baseEnd_8162338] using wordTrace_append hprefix tailTrace_8162338
  have hstable : (prefixWord ++ tailWord_8162338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162338).length < 2 ^ (prefixWord ++ tailWord_8162338).sum := by decide
  have hdescent : baseEnd_8162338 < baseStart_8162338 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162368 : List Nat := [2, 1, 1, 2, 2, 3, 4, 2, 2, 1, 3]
def baseStart_8162368 : Nat := 118140960795 + 8162368 * 2 ^ 59
def prefixEnd_8162368 : Nat := 4983230072969 + 3 ^ 40 * 8162368 * 2
def baseEnd_8162368 : Nat := 4191218062878025931361959

theorem tailTrace_8162368 : CollatzResearch.WordTrace tailWord_8162368 prefixEnd_8162368 4191218062878025931361959 := by
  unfold tailWord_8162368
  simp only [CollatzResearch.WordTrace]
  refine ⟨148853009246571116157895879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198470678995428154877194505 148853009246571116157895879)
  ·
    refine ⟨223279513869856674236843819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148853009246571116157895879 223279513869856674236843819)
    ·
      refine ⟨334919270804785011355265729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223279513869856674236843819 334919270804785011355265729)
      ·
        refine ⟨251189453103588758516449297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334919270804785011355265729 251189453103588758516449297)
        ·
          refine ⟨188392089827691568887336973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251189453103588758516449297 188392089827691568887336973)
          ·
            refine ⟨70647033685384338332751365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188392089827691568887336973 70647033685384338332751365)
            ·
              refine ⟨13246318816009563437390881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70647033685384338332751365 13246318816009563437390881)
              ·
                refine ⟨9934739112007172578043161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13246318816009563437390881 9934739112007172578043161)
                ·
                  refine ⟨7451054334005379433532371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9934739112007172578043161 7451054334005379433532371)
                  ·
                    refine ⟨11176581501008069150298557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7451054334005379433532371 11176581501008069150298557)
                    ·
                      refine ⟨4191218062878025931361959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11176581501008069150298557 4191218062878025931361959)
                      ·
                        rfl

theorem cell23_8162368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 2, 1, 3].length) (baseStart_8162368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162368 prefixEnd_8162368 := by exact prefixLift 8162368
  have htrace : WordTrace (prefixWord ++ tailWord_8162368) baseStart_8162368 baseEnd_8162368 := by
    simpa [prefixWord, tailWord_8162368, baseEnd_8162368] using wordTrace_append hprefix tailTrace_8162368
  have hstable : (prefixWord ++ tailWord_8162368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162368).length < 2 ^ (prefixWord ++ tailWord_8162368).sum := by decide
  have hdescent : baseEnd_8162368 < baseStart_8162368 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162394 : List Nat := [3, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5]
def baseStart_8162394 : Nat := 118140960795 + 8162394 * 2 ^ 59
def prefixEnd_8162394 : Nat := 4983230072969 + 3 ^ 40 * 8162394 * 2
def baseEnd_8162394 : Nat := 4191231413375042829636839

theorem tailTrace_8162394 : CollatzResearch.WordTrace tailWord_8162394 prefixEnd_8162394 4191231413375042829636839 := by
  unfold tailWord_8162394
  simp only [CollatzResearch.WordTrace]
  refine ⟨74426741697762009689059559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198471311194032025837492157 74426741697762009689059559)
  ·
    refine ⟨111640112546643014533589339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74426741697762009689059559 111640112546643014533589339)
    ·
      refine ⟨167460168819964521800384009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111640112546643014533589339 167460168819964521800384009)
      ·
        refine ⟨125595126614973391350288007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167460168819964521800384009 125595126614973391350288007)
        ·
          refine ⟨188392689922460087025432011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125595126614973391350288007 188392689922460087025432011)
          ·
            refine ⟨282589034883690130538148017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188392689922460087025432011 282589034883690130538148017)
            ·
              refine ⟨211941776162767597903611013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282589034883690130538148017 211941776162767597903611013)
              ·
                refine ⟨39739083030518924606927065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211941776162767597903611013 39739083030518924606927065)
                ·
                  refine ⟨29804312272889193455195299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39739083030518924606927065 29804312272889193455195299)
                  ·
                    refine ⟨44706468409333790182792949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29804312272889193455195299 44706468409333790182792949)
                    ·
                      refine ⟨4191231413375042829636839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44706468409333790182792949 4191231413375042829636839)
                      ·
                        rfl

theorem cell23_8162394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_8162394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162394 prefixEnd_8162394 := by exact prefixLift 8162394
  have htrace : WordTrace (prefixWord ++ tailWord_8162394) baseStart_8162394 baseEnd_8162394 := by
    simpa [prefixWord, tailWord_8162394, baseEnd_8162394] using wordTrace_append hprefix tailTrace_8162394
  have hstable : (prefixWord ++ tailWord_8162394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162394).length < 2 ^ (prefixWord ++ tailWord_8162394).sum := by decide
  have hdescent : baseEnd_8162394 < baseStart_8162394 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162404 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 3, 4, 4]
def baseStart_8162404 : Nat := 118140960795 + 8162404 * 2 ^ 59
def prefixEnd_8162404 : Nat := 4983230072969 + 3 ^ 40 * 8162404 * 2
def baseEnd_8162404 : Nat := 4191236548181587790511793

theorem tailTrace_8162404 : CollatzResearch.WordTrace tailWord_8162404 prefixEnd_8162404 4191236548181587790511793 := by
  unfold tailWord_8162404
  simp only [CollatzResearch.WordTrace]
  refine ⟨148853665760505905232051133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198471554347341206976068177 148853665760505905232051133)
  ·
    refine ⟨55820124660189714462019175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148853665760505905232051133 55820124660189714462019175)
    ·
      refine ⟨83730186990284571693028763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55820124660189714462019175 83730186990284571693028763)
      ·
        refine ⟨125595280485426857539543145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83730186990284571693028763 125595280485426857539543145)
        ·
          refine ⟨94196460364070143154657359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125595280485426857539543145 94196460364070143154657359)
          ·
            refine ⟨141294690546105214731986039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94196460364070143154657359 141294690546105214731986039)
            ·
              refine ⟨211942035819157822097979059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141294690546105214731986039 211942035819157822097979059)
              ·
                refine ⟨317913053728736733146968589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211942035819157822097979059 317913053728736733146968589)
                ·
                  refine ⟨119217395148276274930113221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 317913053728736733146968589 119217395148276274930113221)
                  ·
                    refine ⟨22353261590301801549396229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119217395148276274930113221 22353261590301801549396229)
                    ·
                      refine ⟨4191236548181587790511793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22353261590301801549396229 4191236548181587790511793)
                      ·
                        rfl

theorem cell23_8162404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_8162404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162404 prefixEnd_8162404 := by exact prefixLift 8162404
  have htrace : WordTrace (prefixWord ++ tailWord_8162404) baseStart_8162404 baseEnd_8162404 := by
    simpa [prefixWord, tailWord_8162404, baseEnd_8162404] using wordTrace_append hprefix tailTrace_8162404
  have hstable : (prefixWord ++ tailWord_8162404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162404).length < 2 ^ (prefixWord ++ tailWord_8162404).sum := by decide
  have hdescent : baseEnd_8162404 < baseStart_8162404 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162425 : List Nat := [1, 2, 1, 3, 5, 1, 1, 1, 4, 2, 2]
def baseStart_8162425 : Nat := 118140960795 + 8162425 * 2 ^ 59
def prefixEnd_8162425 : Nat := 4983230072969 + 3 ^ 40 * 8162425 * 2
def baseEnd_8162425 : Nat := 4191247331275332208349197

theorem tailTrace_8162425 : CollatzResearch.WordTrace tailWord_8162425 prefixEnd_8162425 4191247331275332208349197 := by
  unfold tailWord_8162425
  simp only [CollatzResearch.WordTrace]
  refine ⟨297708097453935731050616729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198472064969290487367077819 297708097453935731050616729)
  ·
    refine ⟨223281073090451798287962547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297708097453935731050616729 223281073090451798287962547)
    ·
      refine ⟨334921609635677697431943821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223281073090451798287962547 334921609635677697431943821)
      ·
        refine ⟨125595603613379136536978933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334921609635677697431943821 125595603613379136536978933)
        ·
          refine ⟨11774587838754294050341775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125595603613379136536978933 11774587838754294050341775)
          ·
            refine ⟨17661881758131441075512663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11774587838754294050341775 17661881758131441075512663)
            ·
              refine ⟨26492822637197161613268995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17661881758131441075512663 26492822637197161613268995)
              ·
                refine ⟨39739233955795742419903493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26492822637197161613268995 39739233955795742419903493)
                ·
                  refine ⟨7451106366711701703731905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39739233955795742419903493 7451106366711701703731905)
                  ·
                    refine ⟨5588329775033776277798929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7451106366711701703731905 5588329775033776277798929)
                    ·
                      refine ⟨4191247331275332208349197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5588329775033776277798929 4191247331275332208349197)
                      ·
                        rfl

theorem cell23_8162425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4, 2, 2].length) (baseStart_8162425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162425 prefixEnd_8162425 := by exact prefixLift 8162425
  have htrace : WordTrace (prefixWord ++ tailWord_8162425) baseStart_8162425 baseEnd_8162425 := by
    simpa [prefixWord, tailWord_8162425, baseEnd_8162425] using wordTrace_append hprefix tailTrace_8162425
  have hstable : (prefixWord ++ tailWord_8162425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162425).length < 2 ^ (prefixWord ++ tailWord_8162425).sum := by decide
  have hdescent : baseEnd_8162425 < baseStart_8162425 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162441 : List Nat := [1, 2, 1, 1, 4, 3, 2, 1, 2, 3, 3]
def baseStart_8162441 : Nat := 118140960795 + 8162441 * 2 ^ 59
def prefixEnd_8162441 : Nat := 4983230072969 + 3 ^ 40 * 8162441 * 2
def baseEnd_8162441 : Nat := 4191255546965804145749123

theorem tailTrace_8162441 : CollatzResearch.WordTrace tailWord_8162441 prefixEnd_8162441 4191255546965804145749123 := by
  unfold tailWord_8162441
  simp only [CollatzResearch.WordTrace]
  refine ⟨297708681021877765783199177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198472454014585177188799451 297708681021877765783199177)
  ·
    refine ⟨223281510766408324337399383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297708681021877765783199177 223281510766408324337399383)
    ·
      refine ⟨334922266149612486506099075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223281510766408324337399383 334922266149612486506099075)
      ·
        refine ⟨502383399224418729759148613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334922266149612486506099075 502383399224418729759148613)
        ·
          refine ⟨94196887354578511829840365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 502383399224418729759148613 94196887354578511829840365)
          ·
            refine ⟨35323832757966941936190137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94196887354578511829840365 35323832757966941936190137)
            ·
              refine ⟨26492874568475206452142603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35323832757966941936190137 26492874568475206452142603)
              ·
                refine ⟨39739311852712809678213905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26492874568475206452142603 39739311852712809678213905)
                ·
                  refine ⟨29804483889534607258660429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39739311852712809678213905 29804483889534607258660429)
                  ·
                    refine ⟨11176681458575477721997661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29804483889534607258660429 11176681458575477721997661)
                    ·
                      refine ⟨4191255546965804145749123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11176681458575477721997661 4191255546965804145749123)
                      ·
                        rfl

theorem cell23_8162441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 3, 3].length) (baseStart_8162441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162441 prefixEnd_8162441 := by exact prefixLift 8162441
  have htrace : WordTrace (prefixWord ++ tailWord_8162441) baseStart_8162441 baseEnd_8162441 := by
    simpa [prefixWord, tailWord_8162441, baseEnd_8162441] using wordTrace_append hprefix tailTrace_8162441
  have hstable : (prefixWord ++ tailWord_8162441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162441).length < 2 ^ (prefixWord ++ tailWord_8162441).sum := by decide
  have hdescent : baseEnd_8162441 < baseStart_8162441 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162442 : List Nat := [3, 1, 2, 3, 1, 1, 5, 1, 2, 2, 2]
def baseStart_8162442 : Nat := 118140960795 + 8162442 * 2 ^ 59
def prefixEnd_8162442 : Nat := 4983230072969 + 3 ^ 40 * 8162442 * 2
def baseEnd_8162442 : Nat := 4191256060446458641836619

theorem tailTrace_8162442 : CollatzResearch.WordTrace tailWord_8162442 prefixEnd_8162442 4191256060446458641836619 := by
  unfold tailWord_8162442
  simp only [CollatzResearch.WordTrace]
  refine ⟨74427179373718535738496395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198472478329916095302657053 74427179373718535738496395)
  ·
    refine ⟨111640769060577803607744593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74427179373718535738496395 111640769060577803607744593)
    ·
      refine ⟨83730576795433352705808445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111640769060577803607744593 83730576795433352705808445)
      ·
        refine ⟨31398966298287507264678167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83730576795433352705808445 31398966298287507264678167)
        ·
          refine ⟨47098449447431260897017251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31398966298287507264678167 47098449447431260897017251)
          ·
            refine ⟨70647674171146891345525877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47098449447431260897017251 70647674171146891345525877)
            ·
              refine ⟨6623219453545021063643051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70647674171146891345525877 6623219453545021063643051)
              ·
                refine ⟨9934829180317531595464577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6623219453545021063643051 9934829180317531595464577)
                ·
                  refine ⟨7451121885238148696598433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9934829180317531595464577 7451121885238148696598433)
                  ·
                    refine ⟨5588341413928611522448825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7451121885238148696598433 5588341413928611522448825)
                    ·
                      refine ⟨4191256060446458641836619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5588341413928611522448825 4191256060446458641836619)
                      ·
                        rfl

theorem cell23_8162442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_8162442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162442 prefixEnd_8162442 := by exact prefixLift 8162442
  have htrace : WordTrace (prefixWord ++ tailWord_8162442) baseStart_8162442 baseEnd_8162442 := by
    simpa [prefixWord, tailWord_8162442, baseEnd_8162442] using wordTrace_append hprefix tailTrace_8162442
  have hstable : (prefixWord ++ tailWord_8162442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162442).length < 2 ^ (prefixWord ++ tailWord_8162442).sum := by decide
  have hdescent : baseEnd_8162442 < baseStart_8162442 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162451 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 2, 5, 2]
def baseStart_8162451 : Nat := 118140960795 + 8162451 * 2 ^ 59
def prefixEnd_8162451 : Nat := 4983230072969 + 3 ^ 40 * 8162451 * 2
def baseEnd_8162451 : Nat := 4191260681772349106624077

theorem tailTrace_8162451 : CollatzResearch.WordTrace tailWord_8162451 prefixEnd_8162451 4191260681772349106624077 := by
  unfold tailWord_8162451
  simp only [CollatzResearch.WordTrace]
  refine ⟨297709045751841537491063207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198472697167894358327375471 297709045751841537491063207)
  ·
    refine ⟨446563568627762306236594811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297709045751841537491063207 446563568627762306236594811)
    ·
      refine ⟨669845352941643459354892217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446563568627762306236594811 669845352941643459354892217)
      ·
        refine ⟨502384014706232594516169163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 669845352941643459354892217 502384014706232594516169163)
        ·
          refine ⟨753576022059348891774253745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502384014706232594516169163 753576022059348891774253745)
          ·
            refine ⟨565182016544511668830690309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 753576022059348891774253745 565182016544511668830690309)
            ·
              refine ⟨105971628102095937905754433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 565182016544511668830690309 105971628102095937905754433)
              ·
                refine ⟨79478721076571953429315825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105971628102095937905754433 79478721076571953429315825)
                ·
                  refine ⟨59609040807428965071986869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79478721076571953429315825 59609040807428965071986869)
                  ·
                    refine ⟨5588347575696465475498769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59609040807428965071986869 5588347575696465475498769)
                    ·
                      refine ⟨4191260681772349106624077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5588347575696465475498769 4191260681772349106624077)
                      ·
                        rfl

theorem cell23_8162451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 5, 2].length) (baseStart_8162451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162451 prefixEnd_8162451 := by exact prefixLift 8162451
  have htrace : WordTrace (prefixWord ++ tailWord_8162451) baseStart_8162451 baseEnd_8162451 := by
    simpa [prefixWord, tailWord_8162451, baseEnd_8162451] using wordTrace_append hprefix tailTrace_8162451
  have hstable : (prefixWord ++ tailWord_8162451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162451).length < 2 ^ (prefixWord ++ tailWord_8162451).sum := by decide
  have hdescent : baseEnd_8162451 < baseStart_8162451 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162461 : List Nat := [1, 4, 2, 1, 1, 2, 2, 3, 2, 5]
def baseStart_8162461 : Nat := 118140960795 + 8162461 * 2 ^ 59
def prefixEnd_8162461 : Nat := 4983230072969 + 3 ^ 40 * 8162461 * 2
def baseEnd_8162461 : Nat := 1397088605526298022499677

theorem tailTrace_8162461 : CollatzResearch.WordTrace tailWord_8162461 prefixEnd_8162461 1397088605526298022499677 := by
  unfold tailWord_8162461
  simp only [CollatzResearch.WordTrace]
  refine ⟨297709410481805309198927237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198472940321203539465951491 297709410481805309198927237)
  ·
    refine ⟨55820514465338495474798857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297709410481805309198927237 55820514465338495474798857)
    ·
      refine ⟨41865385849003871606099143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55820514465338495474798857 41865385849003871606099143)
      ·
        refine ⟨62798078773505807409148715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41865385849003871606099143 62798078773505807409148715)
        ·
          refine ⟨94197118160258711113723073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62798078773505807409148715 94197118160258711113723073)
          ·
            refine ⟨70647838620194033335292305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94197118160258711113723073 70647838620194033335292305)
            ·
              refine ⟨52985878965145525001469229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70647838620194033335292305 52985878965145525001469229)
              ·
                refine ⟨19869704611929571875550961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52985878965145525001469229 19869704611929571875550961)
                ·
                  refine ⟨14902278458947178906663221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19869704611929571875550961 14902278458947178906663221)
                  ·
                    refine ⟨1397088605526298022499677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14902278458947178906663221 1397088605526298022499677)
                    ·
                      rfl

theorem cell23_8162461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_8162461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162461 prefixEnd_8162461 := by exact prefixLift 8162461
  have htrace : WordTrace (prefixWord ++ tailWord_8162461) baseStart_8162461 baseEnd_8162461 := by
    simpa [prefixWord, tailWord_8162461, baseEnd_8162461] using wordTrace_append hprefix tailTrace_8162461
  have hstable : (prefixWord ++ tailWord_8162461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162461).length < 2 ^ (prefixWord ++ tailWord_8162461).sum := by decide
  have hdescent : baseEnd_8162461 < baseStart_8162461 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162491 : List Nat := [1, 1, 1, 1, 1, 2, 4, 5, 3, 4]
def baseStart_8162491 : Nat := 118140960795 + 8162491 * 2 ^ 59
def prefixEnd_8162491 : Nat := 4983230072969 + 3 ^ 40 * 8162491 * 2
def baseEnd_8162491 : Nat := 1397093740332842983374631

theorem tailTrace_8162491 : CollatzResearch.WordTrace tailWord_8162491 prefixEnd_8162491 1397093740332842983374631 := by
  unfold tailWord_8162491
  simp only [CollatzResearch.WordTrace]
  refine ⟨297710504671696624322519327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198473669781131082881679551 297710504671696624322519327)
  ·
    refine ⟨446565757007544936483778991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297710504671696624322519327 446565757007544936483778991)
    ·
      refine ⟨669848635511317404725668487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446565757007544936483778991 669848635511317404725668487)
      ·
        refine ⟨1004772953266976107088502731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669848635511317404725668487 1004772953266976107088502731)
        ·
          refine ⟨1507159429900464160632754097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1004772953266976107088502731 1507159429900464160632754097)
          ·
            refine ⟨1130369572425348120474565573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1507159429900464160632754097 1130369572425348120474565573)
            ·
              refine ⟨211944294829752772588981045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1130369572425348120474565573 211944294829752772588981045)
              ·
                refine ⟨19869777640289322430216973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 211944294829752772588981045 19869777640289322430216973)
                ·
                  refine ⟨7451166615108495911331365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19869777640289322430216973 7451166615108495911331365)
                  ·
                    refine ⟨1397093740332842983374631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7451166615108495911331365 1397093740332842983374631)
                    ·
                      rfl

theorem cell23_8162491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3, 4].length) (baseStart_8162491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162491 prefixEnd_8162491 := by exact prefixLift 8162491
  have htrace : WordTrace (prefixWord ++ tailWord_8162491) baseStart_8162491 baseEnd_8162491 := by
    simpa [prefixWord, tailWord_8162491, baseEnd_8162491] using wordTrace_append hprefix tailTrace_8162491
  have hstable : (prefixWord ++ tailWord_8162491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162491).length < 2 ^ (prefixWord ++ tailWord_8162491).sum := by decide
  have hdescent : baseEnd_8162491 < baseStart_8162491 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162501 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 6, 2, 3]
def baseStart_8162501 : Nat := 118140960795 + 8162501 * 2 ^ 59
def prefixEnd_8162501 : Nat := 4983230072969 + 3 ^ 40 * 8162501 * 2
def baseEnd_8162501 : Nat := 4191286355805073910998847

theorem tailTrace_8162501 : CollatzResearch.WordTrace tailWord_8162501 prefixEnd_8162501 4191286355805073910998847 := by
  unfold tailWord_8162501
  simp only [CollatzResearch.WordTrace]
  refine ⟨297710869401660396030383357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198473912934440264020255571 297710869401660396030383357)
  ·
    refine ⟨111641576025622648511393759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297710869401660396030383357 111641576025622648511393759)
    ·
      refine ⟨167462364038433972767090639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111641576025622648511393759 167462364038433972767090639)
      ·
        refine ⟨251193546057650959150635959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167462364038433972767090639 251193546057650959150635959)
        ·
          refine ⟨376790319086476438725953939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251193546057650959150635959 376790319086476438725953939)
          ·
            refine ⟨565185478629714658088930909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376790319086476438725953939 565185478629714658088930909)
            ·
              refine ⟨211944554486142996783349091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 565185478629714658088930909 211944554486142996783349091)
              ·
                refine ⟨317916831729214495175023637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211944554486142996783349091 317916831729214495175023637)
                ·
                  refine ⟨14902351487306929461329233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 317916831729214495175023637 14902351487306929461329233)
                  ·
                    refine ⟨11176763615480197095996925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14902351487306929461329233 11176763615480197095996925)
                    ·
                      refine ⟨4191286355805073910998847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11176763615480197095996925 4191286355805073910998847)
                      ·
                        rfl

theorem cell23_8162501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 2, 3].length) (baseStart_8162501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162501 prefixEnd_8162501 := by exact prefixLift 8162501
  have htrace : WordTrace (prefixWord ++ tailWord_8162501) baseStart_8162501 baseEnd_8162501 := by
    simpa [prefixWord, tailWord_8162501, baseEnd_8162501] using wordTrace_append hprefix tailTrace_8162501
  have hstable : (prefixWord ++ tailWord_8162501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162501).length < 2 ^ (prefixWord ++ tailWord_8162501).sum := by decide
  have hdescent : baseEnd_8162501 < baseStart_8162501 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162538 : List Nat := [3, 1, 3, 1, 1, 4, 2, 2, 6]
def baseStart_8162538 : Nat := 118140960795 + 8162538 * 2 ^ 59
def prefixEnd_8162538 : Nat := 4983230072969 + 3 ^ 40 * 8162538 * 2
def baseEnd_8162538 : Nat := 465700594954365585137353

theorem tailTrace_8162538 : CollatzResearch.WordTrace tailWord_8162538 prefixEnd_8162538 465700594954365585137353 := by
  unfold tailWord_8162538
  simp only [CollatzResearch.WordTrace]
  refine ⟨74428054725631587837370067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198474812601684234232986845 74428054725631587837370067)
  ·
    refine ⟨111642082088447381756055101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74428054725631587837370067 111642082088447381756055101)
    ·
      refine ⟨41865780783167768158520663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111642082088447381756055101 41865780783167768158520663)
      ·
        refine ⟨62798671174751652237780995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41865780783167768158520663 62798671174751652237780995)
        ·
          refine ⟨94198006762127478356671493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62798671174751652237780995 94198006762127478356671493)
          ·
            refine ⟨17662126267898902191875905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94198006762127478356671493 17662126267898902191875905)
            ·
              refine ⟨13246594700924176643906929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17662126267898902191875905 13246594700924176643906929)
              ·
                refine ⟨9934946025693132482930197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13246594700924176643906929 9934946025693132482930197)
                ·
                  refine ⟨465700594954365585137353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9934946025693132482930197 465700594954365585137353)
                  ·
                    rfl

theorem cell23_8162538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 6].length) (baseStart_8162538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162538 prefixEnd_8162538 := by exact prefixLift 8162538
  have htrace : WordTrace (prefixWord ++ tailWord_8162538) baseStart_8162538 baseEnd_8162538 := by
    simpa [prefixWord, tailWord_8162538, baseEnd_8162538] using wordTrace_append hprefix tailTrace_8162538
  have hstable : (prefixWord ++ tailWord_8162538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162538).length < 2 ^ (prefixWord ++ tailWord_8162538).sum := by decide
  have hdescent : baseEnd_8162538 < baseStart_8162538 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162542 : List Nat := [4, 1, 2, 1, 1, 1, 6, 2, 1, 4]
def baseStart_8162542 : Nat := 118140960795 + 8162542 * 2 ^ 59
def prefixEnd_8162542 : Nat := 4983230072969 + 3 ^ 40 * 8162542 * 2
def baseEnd_8162542 : Nat := 1397102469503969416862053

theorem tailTrace_8162542 : CollatzResearch.WordTrace tailWord_8162542 prefixEnd_8162542 1397102469503969416862053 := by
  unfold tailWord_8162542
  simp only [CollatzResearch.WordTrace]
  refine ⟨37214045599313982504078235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198474909863007906688417253 37214045599313982504078235)
  ·
    refine ⟨55821068398970973756117353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37214045599313982504078235 55821068398970973756117353)
    ·
      refine ⟨41865801299228230317088015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55821068398970973756117353 41865801299228230317088015)
      ·
        refine ⟨62798701948842345475632023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41865801299228230317088015 62798701948842345475632023)
        ·
          refine ⟨94198052923263518213448035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62798701948842345475632023 94198052923263518213448035)
          ·
            refine ⟨141297079384895277320172053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94198052923263518213448035 141297079384895277320172053)
            ·
              refine ⟨6623300596166966124383065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141297079384895277320172053 6623300596166966124383065)
              ·
                refine ⟨4967475447125224593287299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6623300596166966124383065 4967475447125224593287299)
                ·
                  refine ⟨7451213170687836889930949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4967475447125224593287299 7451213170687836889930949)
                  ·
                    refine ⟨1397102469503969416862053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7451213170687836889930949 1397102469503969416862053)
                    ·
                      rfl

theorem cell23_8162542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_8162542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162542 prefixEnd_8162542 := by exact prefixLift 8162542
  have htrace : WordTrace (prefixWord ++ tailWord_8162542) baseStart_8162542 baseEnd_8162542 := by
    simpa [prefixWord, tailWord_8162542, baseEnd_8162542] using wordTrace_append hprefix tailTrace_8162542
  have hstable : (prefixWord ++ tailWord_8162542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162542).length < 2 ^ (prefixWord ++ tailWord_8162542).sum := by decide
  have hdescent : baseEnd_8162542 < baseStart_8162542 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162622 : List Nat := [4, 2, 1, 2, 1, 1, 1, 4, 3, 2, 2]
def baseStart_8162622 : Nat := 118140960795 + 8162622 * 2 ^ 59
def prefixEnd_8162622 : Nat := 4983230072969 + 3 ^ 40 * 8162622 * 2
def baseEnd_8162622 : Nat := 4191348486964267937585791

theorem tailTrace_8162622 : CollatzResearch.WordTrace tailWord_8162622 prefixEnd_8162622 4191348486964267937585791 := by
  unfold tailWord_8162622
  simp only [CollatzResearch.WordTrace]
  refine ⟨37214410329277754211942265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198476855089481355797025413 37214410329277754211942265)
  ·
    refine ⟨27910807746958315658956699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37214410329277754211942265 27910807746958315658956699)
    ·
      refine ⟨41866211620437473488435049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27910807746958315658956699 41866211620437473488435049)
      ·
        refine ⟨31399658715328105116326287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41866211620437473488435049 31399658715328105116326287)
        ·
          refine ⟨47099488072992157674489431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31399658715328105116326287 47099488072992157674489431)
          ·
            refine ⟨70649232109488236511734147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47099488072992157674489431 70649232109488236511734147)
            ·
              refine ⟨105973848164232354767601221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70649232109488236511734147 105973848164232354767601221)
              ·
                refine ⟨19870096530793566518925229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105973848164232354767601221 19870096530793566518925229)
                ·
                  refine ⟨7451286199047587444596961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19870096530793566518925229 7451286199047587444596961)
                  ·
                    refine ⟨5588464649285690583447721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7451286199047587444596961 5588464649285690583447721)
                    ·
                      refine ⟨4191348486964267937585791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5588464649285690583447721 4191348486964267937585791)
                      ·
                        rfl

theorem cell23_8162622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_8162622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162622 prefixEnd_8162622 := by exact prefixLift 8162622
  have htrace : WordTrace (prefixWord ++ tailWord_8162622) baseStart_8162622 baseEnd_8162622 := by
    simpa [prefixWord, tailWord_8162622, baseEnd_8162622] using wordTrace_append hprefix tailTrace_8162622
  have hstable : (prefixWord ++ tailWord_8162622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162622).length < 2 ^ (prefixWord ++ tailWord_8162622).sum := by decide
  have hdescent : baseEnd_8162622 < baseStart_8162622 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162638 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3]
def baseStart_8162638 : Nat := 118140960795 + 8162638 * 2 ^ 59
def prefixEnd_8162638 : Nat := 4983230072969 + 3 ^ 40 * 8162638 * 2
def baseEnd_8162638 : Nat := 4191356702654739874985717

theorem tailTrace_8162638 : CollatzResearch.WordTrace tailWord_8162638 prefixEnd_8162638 4191356702654739874985717 := by
  unfold tailWord_8162638
  simp only [CollatzResearch.WordTrace]
  refine ⟨37214483275270508553515071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198477244134776045618747045 37214483275270508553515071)
  ·
    refine ⟨55821724912905762830272607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37214483275270508553515071 55821724912905762830272607)
    ·
      refine ⟨83732587369358644245408911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55821724912905762830272607 83732587369358644245408911)
      ·
        refine ⟨125598881054037966368113367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83732587369358644245408911 125598881054037966368113367)
        ·
          refine ⟨188398321581056949552170051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125598881054037966368113367 188398321581056949552170051)
          ·
            refine ⟨282597482371585424328255077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188398321581056949552170051 282597482371585424328255077)
            ·
              refine ⟨52987027944672267061547827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 282597482371585424328255077 52987027944672267061547827)
              ·
                refine ⟨79480541917008400592321741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52987027944672267061547827 79480541917008400592321741)
                ·
                  refine ⟨29805203218878150222120653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79480541917008400592321741 29805203218878150222120653)
                  ·
                    refine ⟨11176951207079306333295245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29805203218878150222120653 11176951207079306333295245)
                    ·
                      refine ⟨4191356702654739874985717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11176951207079306333295245 4191356702654739874985717)
                      ·
                        rfl

theorem cell23_8162638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_8162638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162638 prefixEnd_8162638 := by exact prefixLift 8162638
  have htrace : WordTrace (prefixWord ++ tailWord_8162638) baseStart_8162638 baseEnd_8162638 := by
    simpa [prefixWord, tailWord_8162638, baseEnd_8162638] using wordTrace_append hprefix tailTrace_8162638
  have hstable : (prefixWord ++ tailWord_8162638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162638).length < 2 ^ (prefixWord ++ tailWord_8162638).sum := by decide
  have hdescent : baseEnd_8162638 < baseStart_8162638 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162655 : List Nat := [1, 1, 2, 3, 1, 2, 1, 6, 2, 1, 3]
def baseStart_8162655 : Nat := 118140960795 + 8162655 * 2 ^ 59
def prefixEnd_8162655 : Nat := 4983230072969 + 3 ^ 40 * 8162655 * 2
def baseEnd_8162655 : Nat := 4191365431825866308473139

theorem tailTrace_8162655 : CollatzResearch.WordTrace tailWord_8162655 prefixEnd_8162655 4191365431825866308473139 := by
  unfold tailWord_8162655
  simp only [CollatzResearch.WordTrace]
  refine ⟨297716486243102480331489419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198477657495401653554326279 297716486243102480331489419)
  ·
    refine ⟨446574729364653720497234129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297716486243102480331489419 446574729364653720497234129)
    ·
      refine ⟨334931047023490290372925597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446574729364653720497234129 334931047023490290372925597)
      ·
        refine ⟨125599142633808858889847099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334931047023490290372925597 125599142633808858889847099)
        ·
          refine ⟨188398713950713288334770649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125599142633808858889847099 188398713950713288334770649)
          ·
            refine ⟨141299035463034966251077987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188398713950713288334770649 141299035463034966251077987)
            ·
              refine ⟨211948553194552449376616981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141299035463034966251077987 211948553194552449376616981)
              ·
                refine ⟨9935088430994646064528921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 211948553194552449376616981 9935088430994646064528921)
                ·
                  refine ⟨7451316323245984548396691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9935088430994646064528921 7451316323245984548396691)
                  ·
                    refine ⟨11176974484868976822595037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7451316323245984548396691 11176974484868976822595037)
                    ·
                      refine ⟨4191365431825866308473139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11176974484868976822595037 4191365431825866308473139)
                      ·
                        rfl

theorem cell23_8162655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_8162655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162655 prefixEnd_8162655 := by exact prefixLift 8162655
  have htrace : WordTrace (prefixWord ++ tailWord_8162655) baseStart_8162655 baseEnd_8162655 := by
    simpa [prefixWord, tailWord_8162655, baseEnd_8162655] using wordTrace_append hprefix tailTrace_8162655
  have hstable : (prefixWord ++ tailWord_8162655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162655).length < 2 ^ (prefixWord ++ tailWord_8162655).sum := by decide
  have hdescent : baseEnd_8162655 < baseStart_8162655 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162656 : List Nat := [2, 1, 1, 3, 4, 2, 3, 2, 1, 2, 2]
def baseStart_8162656 : Nat := 118140960795 + 8162656 * 2 ^ 59
def prefixEnd_8162656 : Nat := 4983230072969 + 3 ^ 40 * 8162656 * 2
def baseEnd_8162656 : Nat := 4191365945306520804560635

theorem tailTrace_8162656 : CollatzResearch.WordTrace tailWord_8162656 prefixEnd_8162656 4191365945306520804560635 := by
  unfold tailWord_8162656
  simp only [CollatzResearch.WordTrace]
  refine ⟨148858261358049428751137911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198477681810732571668183881 148858261358049428751137911)
  ·
    refine ⟨223287392037074143126706867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148858261358049428751137911 223287392037074143126706867)
    ·
      refine ⟨334931088055611214690060301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223287392037074143126706867 334931088055611214690060301)
      ·
        refine ⟨125599158020854205508772613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334931088055611214690060301 125599158020854205508772613)
        ·
          refine ⟨23549842128910163532894865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125599158020854205508772613 23549842128910163532894865)
          ·
            refine ⟨17662381596682622649671149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23549842128910163532894865 17662381596682622649671149)
            ·
              refine ⟨6623393098755983493626681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17662381596682622649671149 6623393098755983493626681)
              ·
                refine ⟨4967544824066987620220011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6623393098755983493626681 4967544824066987620220011)
                ·
                  refine ⟨7451317236100481430330017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4967544824066987620220011 7451317236100481430330017)
                  ·
                    refine ⟨5588487927075361072747513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7451317236100481430330017 5588487927075361072747513)
                    ·
                      refine ⟨4191365945306520804560635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5588487927075361072747513 4191365945306520804560635)
                      ·
                        rfl

theorem cell23_8162656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2, 1, 2, 2].length) (baseStart_8162656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162656 prefixEnd_8162656 := by exact prefixLift 8162656
  have htrace : WordTrace (prefixWord ++ tailWord_8162656) baseStart_8162656 baseEnd_8162656 := by
    simpa [prefixWord, tailWord_8162656, baseEnd_8162656] using wordTrace_append hprefix tailTrace_8162656
  have hstable : (prefixWord ++ tailWord_8162656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162656).length < 2 ^ (prefixWord ++ tailWord_8162656).sum := by decide
  have hdescent : baseEnd_8162656 < baseStart_8162656 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162658 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 2, 7]
def baseStart_8162658 : Nat := 118140960795 + 8162658 * 2 ^ 59
def prefixEnd_8162658 : Nat := 4983230072969 + 3 ^ 40 * 8162658 * 2
def baseEnd_8162658 : Nat := 1397122324089276598911875

theorem tailTrace_8162658 : CollatzResearch.WordTrace tailWord_8162658 prefixEnd_8162658 1397122324089276598911875 := by
  unfold tailWord_8162658
  simp only [CollatzResearch.WordTrace]
  refine ⟨74429148915522902960962157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198477730441394407895899085 74429148915522902960962157)
  ·
    refine ⟨27910930843321088610360809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74429148915522902960962157 27910930843321088610360809)
    ·
      refine ⟨20933198132490816457770607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27910930843321088610360809 20933198132490816457770607)
      ·
        refine ⟨31399797198736224686655911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20933198132490816457770607 31399797198736224686655911)
        ·
          refine ⟨47099695798104337029983867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31399797198736224686655911 47099695798104337029983867)
          ·
            refine ⟨70649543697156505544975801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47099695798104337029983867 70649543697156505544975801)
            ·
              refine ⟨52987157772867379158731851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70649543697156505544975801 52987157772867379158731851)
              ·
                refine ⟨79480736659301068738097777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52987157772867379158731851 79480736659301068738097777)
                ·
                  refine ⟨59610552494475801553573333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79480736659301068738097777 59610552494475801553573333)
                  ·
                    refine ⟨1397122324089276598911875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59610552494475801553573333 1397122324089276598911875)
                    ·
                      rfl

theorem cell23_8162658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_8162658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162658 prefixEnd_8162658 := by exact prefixLift 8162658
  have htrace : WordTrace (prefixWord ++ tailWord_8162658) baseStart_8162658 baseEnd_8162658 := by
    simpa [prefixWord, tailWord_8162658, baseEnd_8162658] using wordTrace_append hprefix tailTrace_8162658
  have hstable : (prefixWord ++ tailWord_8162658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162658).length < 2 ^ (prefixWord ++ tailWord_8162658).sum := by decide
  have hdescent : baseEnd_8162658 < baseStart_8162658 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162666 : List Nat := [3, 1, 3, 3, 3, 1, 2, 1, 2, 4]
def baseStart_8162666 : Nat := 118140960795 + 8162666 * 2 ^ 59
def prefixEnd_8162666 : Nat := 4983230072969 + 3 ^ 40 * 8162666 * 2
def baseEnd_8162666 : Nat := 1397123693371021921811863

theorem tailTrace_8162666 : CollatzResearch.WordTrace tailWord_8162666 prefixEnd_8162666 1397123693371021921811863 := by
  unfold tailWord_8162666
  simp only [CollatzResearch.WordTrace]
  refine ⟨74429221861515657302534963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198477924964041752806759901 74429221861515657302534963)
  ·
    refine ⟨111643832792273485953802445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74429221861515657302534963 111643832792273485953802445)
    ·
      refine ⟨41866437297102557232675917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111643832792273485953802445 41866437297102557232675917)
      ·
        refine ⟨15699913986413458962253469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41866437297102557232675917 15699913986413458962253469)
        ·
          refine ⟨5887467744905047110845051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15699913986413458962253469 5887467744905047110845051)
          ·
            refine ⟨8831201617357570666267577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5887467744905047110845051 8831201617357570666267577)
            ·
              refine ⟨6623401213018177999700683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8831201617357570666267577 6623401213018177999700683)
              ·
                refine ⟨9935101819527266999551025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6623401213018177999700683 9935101819527266999551025)
                ·
                  refine ⟨7451326364645450249663269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9935101819527266999551025 7451326364645450249663269)
                  ·
                    refine ⟨1397123693371021921811863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7451326364645450249663269 1397123693371021921811863)
                    ·
                      rfl

theorem cell23_8162666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_8162666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162666 prefixEnd_8162666 := by exact prefixLift 8162666
  have htrace : WordTrace (prefixWord ++ tailWord_8162666) baseStart_8162666 baseEnd_8162666 := by
    simpa [prefixWord, tailWord_8162666, baseEnd_8162666] using wordTrace_append hprefix tailTrace_8162666
  have hstable : (prefixWord ++ tailWord_8162666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162666).length < 2 ^ (prefixWord ++ tailWord_8162666).sum := by decide
  have hdescent : baseEnd_8162666 < baseStart_8162666 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162671 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 1, 8]
def baseStart_8162671 : Nat := 118140960795 + 8162671 * 2 ^ 59
def prefixEnd_8162671 : Nat := 4983230072969 + 3 ^ 40 * 8162671 * 2
def baseEnd_8162671 : Nat := 1397124549172112748624355

theorem tailTrace_8162671 : CollatzResearch.WordTrace tailWord_8162671 prefixEnd_8162671 1397124549172112748624355 := by
  unfold tailWord_8162671
  simp only [CollatzResearch.WordTrace]
  refine ⟨297717069811044515064071867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198478046540696343376047911 297717069811044515064071867)
  ·
    refine ⟨446575604716566772596107801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297717069811044515064071867 446575604716566772596107801)
    ·
      refine ⟨334931703537425079447080851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446575604716566772596107801 334931703537425079447080851)
      ·
        refine ⟨502397555306137619170621277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334931703537425079447080851 502397555306137619170621277)
        ·
          refine ⟨188399083239801607188982979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 502397555306137619170621277 188399083239801607188982979)
          ·
            refine ⟨282598624859702410783474469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188399083239801607188982979 282598624859702410783474469)
            ·
              refine ⟨52987242161194202021901463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 282598624859702410783474469 52987242161194202021901463)
              ·
                refine ⟨79480863241791303032852195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52987242161194202021901463 79480863241791303032852195)
                ·
                  refine ⟨119221294862686954549278293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79480863241791303032852195 119221294862686954549278293)
                  ·
                    refine ⟨1397124549172112748624355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119221294862686954549278293 1397124549172112748624355)
                    ·
                      rfl

theorem cell23_8162671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 8].length) (baseStart_8162671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162671 prefixEnd_8162671 := by exact prefixLift 8162671
  have htrace : WordTrace (prefixWord ++ tailWord_8162671) baseStart_8162671 baseEnd_8162671 := by
    simpa [prefixWord, tailWord_8162671, baseEnd_8162671] using wordTrace_append hprefix tailTrace_8162671
  have hstable : (prefixWord ++ tailWord_8162671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162671).length < 2 ^ (prefixWord ++ tailWord_8162671).sum := by decide
  have hdescent : baseEnd_8162671 < baseStart_8162671 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162695 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 3, 4, 2]
def baseStart_8162695 : Nat := 118140960795 + 8162695 * 2 ^ 59
def prefixEnd_8162695 : Nat := 4983230072969 + 3 ^ 40 * 8162695 * 2
def baseEnd_8162695 : Nat := 4191385971052046151972955

theorem tailTrace_8162695 : CollatzResearch.WordTrace tailWord_8162695 prefixEnd_8162695 4191385971052046151972955 := by
  unfold tailWord_8162695
  simp only [CollatzResearch.WordTrace]
  refine ⟨297717945162957567162945539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198478630108638378108630359 297717945162957567162945539)
  ·
    refine ⟨446576917744436350744418309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297717945162957567162945539 446576917744436350744418309)
    ·
      refine ⟨83733172077081815764578433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 446576917744436350744418309 83733172077081815764578433)
      ·
        refine ⟨62799879057811361823433825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83733172077081815764578433 62799879057811361823433825)
        ·
          refine ⟨47099909293358521367575369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62799879057811361823433825 47099909293358521367575369)
          ·
            refine ⟨35324931970018891025681527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47099909293358521367575369 35324931970018891025681527)
            ·
              refine ⟨52987397955028336538522291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35324931970018891025681527 52987397955028336538522291)
              ·
                refine ⟨79481096932542504807783437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52987397955028336538522291 79481096932542504807783437)
                ·
                  refine ⟨29805411349703439302918789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79481096932542504807783437 29805411349703439302918789)
                  ·
                    refine ⟨5588514628069394869297273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29805411349703439302918789 5588514628069394869297273)
                    ·
                      refine ⟨4191385971052046151972955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5588514628069394869297273 4191385971052046151972955)
                      ·
                        rfl

theorem cell23_8162695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_8162695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162695 prefixEnd_8162695 := by exact prefixLift 8162695
  have htrace : WordTrace (prefixWord ++ tailWord_8162695) baseStart_8162695 baseEnd_8162695 := by
    simpa [prefixWord, tailWord_8162695, baseEnd_8162695] using wordTrace_append hprefix tailTrace_8162695
  have hstable : (prefixWord ++ tailWord_8162695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162695).length < 2 ^ (prefixWord ++ tailWord_8162695).sum := by decide
  have hdescent : baseEnd_8162695 < baseStart_8162695 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162706 : List Nat := [3, 2, 3, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_8162706 : Nat := 118140960795 + 8162706 * 2 ^ 59
def prefixEnd_8162706 : Nat := 4983230072969 + 3 ^ 40 * 8162706 * 2
def baseEnd_8162706 : Nat := 4191391619339245608935405

theorem tailTrace_8162706 : CollatzResearch.WordTrace tailWord_8162706 prefixEnd_8162706 4191391619339245608935405 := by
  unfold tailWord_8162706
  simp only [CollatzResearch.WordTrace]
  refine ⟨74429586591479429010398993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198478897577278477361063981 74429586591479429010398993)
  ·
    refine ⟨55822189943609571757799245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74429586591479429010398993 55822189943609571757799245)
    ·
      refine ⟨20933321228853589409174717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55822189943609571757799245 20933321228853589409174717)
      ·
        refine ⟨7849995460820096028440519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20933321228853589409174717 7849995460820096028440519)
        ·
          refine ⟨11774993191230144042660779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7849995460820096028440519 11774993191230144042660779)
          ·
            refine ⟨17662489786845216063991169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11774993191230144042660779 17662489786845216063991169)
            ·
              refine ⟨13246867340133912047993377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17662489786845216063991169 13246867340133912047993377)
              ·
                refine ⟨9935150505100434035995033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13246867340133912047993377 9935150505100434035995033)
                ·
                  refine ⟨7451362878825325526996275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9935150505100434035995033 7451362878825325526996275)
                  ·
                    refine ⟨11177044318237988290494413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7451362878825325526996275 11177044318237988290494413)
                    ·
                      refine ⟨4191391619339245608935405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11177044318237988290494413 4191391619339245608935405)
                      ·
                        rfl

theorem cell23_8162706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_8162706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162706 prefixEnd_8162706 := by exact prefixLift 8162706
  have htrace : WordTrace (prefixWord ++ tailWord_8162706) baseStart_8162706 baseEnd_8162706 := by
    simpa [prefixWord, tailWord_8162706, baseEnd_8162706] using wordTrace_append hprefix tailTrace_8162706
  have hstable : (prefixWord ++ tailWord_8162706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162706).length < 2 ^ (prefixWord ++ tailWord_8162706).sum := by decide
  have hdescent : baseEnd_8162706 < baseStart_8162706 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162731 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 2, 11]
def baseStart_8162731 : Nat := 118140960795 + 8162731 * 2 ^ 59
def prefixEnd_8162731 : Nat := 4983230072969 + 3 ^ 40 * 8162731 * 2
def baseEnd_8162731 : Nat := 1397134818785202670374263

theorem tailTrace_8162731 : CollatzResearch.WordTrace tailWord_8162731 prefixEnd_8162731 1397134818785202670374263 := by
  unfold tailWord_8162731
  simp only [CollatzResearch.WordTrace]
  refine ⟨297719258190827145311256047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198479505460551430207504031 297719258190827145311256047)
  ·
    refine ⟨446578887286240717966884071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297719258190827145311256047 446578887286240717966884071)
    ·
      refine ⟨669868330929361076950326107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446578887286240717966884071 669868330929361076950326107)
      ·
        refine ⟨1004802496394041615425489161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669868330929361076950326107 1004802496394041615425489161)
        ·
          refine ⟨753601872295531211569116871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1004802496394041615425489161 753601872295531211569116871)
          ·
            refine ⟨1130402808443296817353675307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753601872295531211569116871 1130402808443296817353675307)
            ·
              refine ⟨1695604212664945226030512961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130402808443296817353675307 1695604212664945226030512961)
              ·
                refine ⟨1271703159498708919522884721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1695604212664945226030512961 1271703159498708919522884721)
                ·
                  refine ⟨953777369624031689642163541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1271703159498708919522884721 953777369624031689642163541)
                  ·
                    refine ⟨1397134818785202670374263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 953777369624031689642163541 1397134818785202670374263)
                    ·
                      rfl

theorem cell23_8162731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 11].length) (baseStart_8162731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162731 prefixEnd_8162731 := by exact prefixLift 8162731
  have htrace : WordTrace (prefixWord ++ tailWord_8162731) baseStart_8162731 baseEnd_8162731 := by
    simpa [prefixWord, tailWord_8162731, baseEnd_8162731] using wordTrace_append hprefix tailTrace_8162731
  have hstable : (prefixWord ++ tailWord_8162731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162731).length < 2 ^ (prefixWord ++ tailWord_8162731).sum := by decide
  have hdescent : baseEnd_8162731 < baseStart_8162731 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162808 : List Nat := [2, 1, 2, 1, 1, 5, 1, 2, 8]
def baseStart_8162808 : Nat := 118140960795 + 8162808 * 2 ^ 59
def prefixEnd_8162808 : Nat := 4983230072969 + 3 ^ 40 * 8162808 * 2
def baseEnd_8162808 : Nat := 465715999374000467762215

theorem tailTrace_8162808 : CollatzResearch.WordTrace tailWord_8162808 prefixEnd_8162808 465715999374000467762215 := by
  unfold tailWord_8162808
  simp only [CollatzResearch.WordTrace]
  refine ⟨148861033305774093730904539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198481377741032124974539385 148861033305774093730904539)
  ·
    refine ⟨223291549958661140596356809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148861033305774093730904539 223291549958661140596356809)
    ·
      refine ⟨167468662468995855447267607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223291549958661140596356809 167468662468995855447267607)
      ·
        refine ⟨251202993703493783170901411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167468662468995855447267607 251202993703493783170901411)
        ·
          refine ⟨376804490555240674756352117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251202993703493783170901411 376804490555240674756352117)
          ·
            refine ⟨35325420989553813258408011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 376804490555240674756352117 35325420989553813258408011)
            ·
              refine ⟨52988131484330719887612017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35325420989553813258408011 52988131484330719887612017)
              ·
                refine ⟨39741098613248039915709013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52988131484330719887612017 39741098613248039915709013)
                ·
                  refine ⟨465715999374000467762215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39741098613248039915709013 465715999374000467762215)
                  ·
                    rfl

theorem cell23_8162808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 8].length) (baseStart_8162808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162808 prefixEnd_8162808 := by exact prefixLift 8162808
  have htrace : WordTrace (prefixWord ++ tailWord_8162808) baseStart_8162808 baseEnd_8162808 := by
    simpa [prefixWord, tailWord_8162808, baseEnd_8162808] using wordTrace_append hprefix tailTrace_8162808
  have hstable : (prefixWord ++ tailWord_8162808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162808).length < 2 ^ (prefixWord ++ tailWord_8162808).sum := by decide
  have hdescent : baseEnd_8162808 < baseStart_8162808 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162912 : List Nat := [2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 3]
def baseStart_8162912 : Nat := 118140960795 + 8162912 * 2 ^ 59
def prefixEnd_8162912 : Nat := 4983230072969 + 3 ^ 40 * 8162912 * 2
def baseEnd_8162912 : Nat := 4191497396354071802959457

theorem tailTrace_8162912 : CollatzResearch.WordTrace tailWord_8162912 prefixEnd_8162912 4191497396354071802959457 := by
  unfold tailWord_8162912
  simp only [CollatzResearch.WordTrace]
  refine ⟨148862929901585706611797495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198483906535447608815729993 148862929901585706611797495)
  ·
    refine ⟨223294394852378559917696243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148862929901585706611797495 223294394852378559917696243)
    ·
      refine ⟨334941592278567839876544365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223294394852378559917696243 334941592278567839876544365)
      ·
        refine ⟨125603097104462939953704137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334941592278567839876544365 125603097104462939953704137)
        ·
          refine ⟨94202322828347204965278103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125603097104462939953704137 94202322828347204965278103)
          ·
            refine ⟨141303484242520807447917155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94202322828347204965278103 141303484242520807447917155)
            ·
              refine ⟨211955226363781211171875733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141303484242520807447917155 211955226363781211171875733)
              ·
                refine ⟨9935401235802244273681675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 211955226363781211171875733 9935401235802244273681675)
                ·
                  refine ⟨14903101853703366410522513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9935401235802244273681675 14903101853703366410522513)
                  ·
                    refine ⟨11177326390277524807891885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14903101853703366410522513 11177326390277524807891885)
                    ·
                      refine ⟨4191497396354071802959457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11177326390277524807891885 4191497396354071802959457)
                      ·
                        rfl

theorem cell23_8162912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_8162912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162912 prefixEnd_8162912 := by exact prefixLift 8162912
  have htrace : WordTrace (prefixWord ++ tailWord_8162912) baseStart_8162912 baseEnd_8162912 := by
    simpa [prefixWord, tailWord_8162912, baseEnd_8162912] using wordTrace_append hprefix tailTrace_8162912
  have hstable : (prefixWord ++ tailWord_8162912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162912).length < 2 ^ (prefixWord ++ tailWord_8162912).sum := by decide
  have hdescent : baseEnd_8162912 < baseStart_8162912 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162922 : List Nat := [3, 1, 3, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_8162922 : Nat := 118140960795 + 8162922 * 2 ^ 59
def prefixEnd_8162922 : Nat := 4983230072969 + 3 ^ 40 * 8162922 * 2
def baseEnd_8162922 : Nat := 4191502531160616763834411

theorem tailTrace_8162922 : CollatzResearch.WordTrace tailWord_8162922 prefixEnd_8162922 4191502531160616763834411 := by
  unfold tailWord_8162922
  simp only [CollatzResearch.WordTrace]
  refine ⟨74431556133283796232864755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198484149688756789954306013 74431556133283796232864755)
  ·
    refine ⟨111647334199925694349297133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74431556133283796232864755 111647334199925694349297133)
    ·
      refine ⟨41867750324972135380986425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111647334199925694349297133 41867750324972135380986425)
      ·
        refine ⟨31400812743729101535739819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41867750324972135380986425 31400812743729101535739819)
        ·
          refine ⟨47101219115593652303609729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31400812743729101535739819 47101219115593652303609729)
          ·
            refine ⟨35325914336695239227707297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47101219115593652303609729 35325914336695239227707297)
            ·
              refine ⟨26494435752521429420780473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35325914336695239227707297 26494435752521429420780473)
              ·
                refine ⟨19870826814391072065585355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26494435752521429420780473 19870826814391072065585355)
                ·
                  refine ⟨29806240221586608098378033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19870826814391072065585355 29806240221586608098378033)
                  ·
                    refine ⟨22354680166189956073783525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29806240221586608098378033 22354680166189956073783525)
                    ·
                      refine ⟨4191502531160616763834411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22354680166189956073783525 4191502531160616763834411)
                      ·
                        rfl

theorem cell23_8162922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_8162922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162922 prefixEnd_8162922 := by exact prefixLift 8162922
  have htrace : WordTrace (prefixWord ++ tailWord_8162922) baseStart_8162922 baseEnd_8162922 := by
    simpa [prefixWord, tailWord_8162922, baseEnd_8162922] using wordTrace_append hprefix tailTrace_8162922
  have hstable : (prefixWord ++ tailWord_8162922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162922).length < 2 ^ (prefixWord ++ tailWord_8162922).sum := by decide
  have hdescent : baseEnd_8162922 < baseStart_8162922 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8162965 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 2, 3, 4]
def baseStart_8162965 : Nat := 118140960795 + 8162965 * 2 ^ 59
def prefixEnd_8162965 : Nat := 4983230072969 + 3 ^ 40 * 8162965 * 2
def baseEnd_8162965 : Nat := 4191524610828760095596713

theorem tailTrace_8162965 : CollatzResearch.WordTrace tailWord_8162965 prefixEnd_8162965 4191524610828760095596713 := by
  unfold tailWord_8162965
  simp only [CollatzResearch.WordTrace]
  refine ⟨297727792871979403275274349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198485195247986268850182899 297727792871979403275274349)
  ·
    refine ⟨111647922326992276228227881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297727792871979403275274349 111647922326992276228227881)
    ·
      refine ⟨83735941745244207171170911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111647922326992276228227881 83735941745244207171170911)
      ·
        refine ⟨125603912617866310756756367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83735941745244207171170911 125603912617866310756756367)
        ·
          refine ⟨188405868926799466135134551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125603912617866310756756367 188405868926799466135134551)
          ·
            refine ⟨282608803390199199202701827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188405868926799466135134551 282608803390199199202701827)
            ·
              refine ⟨423913205085298798804052741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282608803390199199202701827 423913205085298798804052741)
              ·
                refine ⟨79483725953493524775759889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 423913205085298798804052741 79483725953493524775759889)
                ·
                  refine ⟨59612794465120143581819917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79483725953493524775759889 59612794465120143581819917)
                  ·
                    refine ⟨22354797924420053843182469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59612794465120143581819917 22354797924420053843182469)
                    ·
                      refine ⟨4191524610828760095596713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22354797924420053843182469 4191524610828760095596713)
                      ·
                        rfl

theorem cell23_8162965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_8162965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8162965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8162965 prefixEnd_8162965 := by exact prefixLift 8162965
  have htrace : WordTrace (prefixWord ++ tailWord_8162965) baseStart_8162965 baseEnd_8162965 := by
    simpa [prefixWord, tailWord_8162965, baseEnd_8162965] using wordTrace_append hprefix tailTrace_8162965
  have hstable : (prefixWord ++ tailWord_8162965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8162965).length < 2 ^ (prefixWord ++ tailWord_8162965).sum := by decide
  have hdescent : baseEnd_8162965 < baseStart_8162965 := by decide
  rcases family_descends (prefixWord ++ tailWord_8162965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163012 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_8163012 : Nat := 118140960795 + 8163012 * 2 ^ 59
def prefixEnd_8163012 : Nat := 4983230072969 + 3 ^ 40 * 8163012 * 2
def baseEnd_8163012 : Nat := 4191548744419521411708997

theorem tailTrace_8163012 : CollatzResearch.WordTrace tailWord_8163012 prefixEnd_8163012 4191548744419521411708997 := by
  unfold tailWord_8163012
  simp only [CollatzResearch.WordTrace]
  refine ⟨148864753551404565151117645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198486338068539420201490193 148864753551404565151117645)
  ·
    refine ⟨55824282581776711931669117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148864753551404565151117645 55824282581776711931669117)
    ·
      refine ⟨20934105968166266974375919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55824282581776711931669117 20934105968166266974375919)
      ·
        refine ⟨31401158952249400461563879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20934105968166266974375919 31401158952249400461563879)
        ·
          refine ⟨47101738428374100692345819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31401158952249400461563879 47101738428374100692345819)
          ·
            refine ⟨70652607642561151038518729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47101738428374100692345819 70652607642561151038518729)
            ·
              refine ⟨52989455731920863278889047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70652607642561151038518729 52989455731920863278889047)
              ·
                refine ⟨79484183597881294918333571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52989455731920863278889047 79484183597881294918333571)
                ·
                  refine ⟨119226275396821942377500357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79484183597881294918333571 119226275396821942377500357)
                  ·
                    refine ⟨22354926636904114195781317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119226275396821942377500357 22354926636904114195781317)
                    ·
                      refine ⟨4191548744419521411708997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22354926636904114195781317 4191548744419521411708997)
                      ·
                        rfl

theorem cell23_8163012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_8163012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163012 prefixEnd_8163012 := by exact prefixLift 8163012
  have htrace : WordTrace (prefixWord ++ tailWord_8163012) baseStart_8163012 baseEnd_8163012 := by
    simpa [prefixWord, tailWord_8163012, baseEnd_8163012] using wordTrace_append hprefix tailTrace_8163012
  have hstable : (prefixWord ++ tailWord_8163012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163012).length < 2 ^ (prefixWord ++ tailWord_8163012).sum := by decide
  have hdescent : baseEnd_8163012 < baseStart_8163012 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163016 : List Nat := [2, 1, 3, 1, 2, 2, 3, 3, 2, 2, 2]
def baseStart_8163016 : Nat := 118140960795 + 8163016 * 2 ^ 59
def prefixEnd_8163016 : Nat := 4983230072969 + 3 ^ 40 * 8163016 * 2
def baseEnd_8163016 : Nat := 4191550798342139396058979

theorem tailTrace_8163016 : CollatzResearch.WordTrace tailWord_8163016 prefixEnd_8163016 4191550798342139396058979 := by
  unfold tailWord_8163016
  simp only [CollatzResearch.WordTrace]
  refine ⟨148864826497397319492690451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198486435329863092656920601 148864826497397319492690451)
  ·
    refine ⟨223297239746095979239035677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148864826497397319492690451 223297239746095979239035677)
    ·
      refine ⟨83736464904785992214638379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223297239746095979239035677 83736464904785992214638379)
      ·
        refine ⟨125604697357178988321957569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83736464904785992214638379 125604697357178988321957569)
        ·
          refine ⟨94203523017884241241468177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125604697357178988321957569 94203523017884241241468177)
          ·
            refine ⟨70652642263413180931101133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94203523017884241241468177 70652642263413180931101133)
            ·
              refine ⟨26494740848779942849162925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70652642263413180931101133 26494740848779942849162925)
              ·
                refine ⟨9935527818292478568436097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26494740848779942849162925 9935527818292478568436097)
                ·
                  refine ⟨7451645863719358926327073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9935527818292478568436097 7451645863719358926327073)
                  ·
                    refine ⟨5588734397789519194745305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7451645863719358926327073 5588734397789519194745305)
                    ·
                      refine ⟨4191550798342139396058979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5588734397789519194745305 4191550798342139396058979)
                      ·
                        rfl

theorem cell23_8163016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 2, 2, 2].length) (baseStart_8163016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163016 prefixEnd_8163016 := by exact prefixLift 8163016
  have htrace : WordTrace (prefixWord ++ tailWord_8163016) baseStart_8163016 baseEnd_8163016 := by
    simpa [prefixWord, tailWord_8163016, baseEnd_8163016] using wordTrace_append hprefix tailTrace_8163016
  have hstable : (prefixWord ++ tailWord_8163016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163016).length < 2 ^ (prefixWord ++ tailWord_8163016).sum := by decide
  have hdescent : baseEnd_8163016 < baseStart_8163016 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163020 : List Nat := [2, 2, 1, 5, 3, 1, 1, 2, 1, 3, 2]
def baseStart_8163020 : Nat := 118140960795 + 8163020 * 2 ^ 59
def prefixEnd_8163020 : Nat := 4983230072969 + 3 ^ 40 * 8163020 * 2
def baseEnd_8163020 : Nat := 4191552852264757380408961

theorem tailTrace_8163020 : CollatzResearch.WordTrace tailWord_8163020 prefixEnd_8163020 4191552852264757380408961 := by
  unfold tailWord_8163020
  simp only [CollatzResearch.WordTrace]
  refine ⟨148864899443390073834263257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198486532591186765112351009 148864899443390073834263257)
  ·
    refine ⟨111648674582542555375697443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148864899443390073834263257 111648674582542555375697443)
    ·
      refine ⟨167473011873813833063546165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111648674582542555375697443 167473011873813833063546165)
      ·
        refine ⟨15700594863170046849707453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167473011873813833063546165 15700594863170046849707453)
        ·
          refine ⟨5887723073688767568640295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15700594863170046849707453 5887723073688767568640295)
          ·
            refine ⟨8831584610533151352960443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5887723073688767568640295 8831584610533151352960443)
            ·
              refine ⟨13247376915799727029440665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8831584610533151352960443 13247376915799727029440665)
              ·
                refine ⟨9935532686849795272080499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13247376915799727029440665 9935532686849795272080499)
                ·
                  refine ⟨14903299030274692908120749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9935532686849795272080499 14903299030274692908120749)
                  ·
                    refine ⟨5588737136353009840545281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14903299030274692908120749 5588737136353009840545281)
                    ·
                      refine ⟨4191552852264757380408961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5588737136353009840545281 4191552852264757380408961)
                      ·
                        rfl

theorem cell23_8163020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_8163020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163020 prefixEnd_8163020 := by exact prefixLift 8163020
  have htrace : WordTrace (prefixWord ++ tailWord_8163020) baseStart_8163020 baseEnd_8163020 := by
    simpa [prefixWord, tailWord_8163020, baseEnd_8163020] using wordTrace_append hprefix tailTrace_8163020
  have hstable : (prefixWord ++ tailWord_8163020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163020).length < 2 ^ (prefixWord ++ tailWord_8163020).sum := by decide
  have hdescent : baseEnd_8163020 < baseStart_8163020 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163052 : List Nat := [2, 2, 1, 1, 2, 2, 4, 2, 2, 5]
def baseStart_8163052 : Nat := 118140960795 + 8163052 * 2 ^ 59
def prefixEnd_8163052 : Nat := 4983230072969 + 3 ^ 40 * 8163052 * 2
def baseEnd_8163052 : Nat := 1397189761215233751736271

theorem tailTrace_8163052 : CollatzResearch.WordTrace tailWord_8163052 prefixEnd_8163052 1397189761215233751736271 := by
  unfold tailWord_8163052
  simp only [CollatzResearch.WordTrace]
  refine ⟨148865483011332108566845705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198487310681776144755794273 148865483011332108566845705)
  ·
    refine ⟨111649112258499081425134279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148865483011332108566845705 111649112258499081425134279)
    ·
      refine ⟨167473668387748622137701419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111649112258499081425134279 167473668387748622137701419)
      ·
        refine ⟨251210502581622933206552129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167473668387748622137701419 251210502581622933206552129)
        ·
          refine ⟨188407876936217199904914097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251210502581622933206552129 188407876936217199904914097)
          ·
            refine ⟨141305907702162899928685573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188407876936217199904914097 141305907702162899928685573)
            ·
              refine ⟨26494857694155543736628545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141305907702162899928685573 26494857694155543736628545)
              ·
                refine ⟨19871143270616657802471409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26494857694155543736628545 19871143270616657802471409)
                ·
                  refine ⟨14903357452962493351853557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19871143270616657802471409 14903357452962493351853557)
                  ·
                    refine ⟨1397189761215233751736271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14903357452962493351853557 1397189761215233751736271)
                    ·
                      rfl

theorem cell23_8163052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 5].length) (baseStart_8163052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163052 prefixEnd_8163052 := by exact prefixLift 8163052
  have htrace : WordTrace (prefixWord ++ tailWord_8163052) baseStart_8163052 baseEnd_8163052 := by
    simpa [prefixWord, tailWord_8163052, baseEnd_8163052] using wordTrace_append hprefix tailTrace_8163052
  have hstable : (prefixWord ++ tailWord_8163052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163052).length < 2 ^ (prefixWord ++ tailWord_8163052).sum := by decide
  have hdescent : baseEnd_8163052 < baseStart_8163052 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163065 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 4, 8]
def baseStart_8163065 : Nat := 118140960795 + 8163065 * 2 ^ 59
def prefixEnd_8163065 : Nat := 4983230072969 + 3 ^ 40 * 8163065 * 2
def baseEnd_8163065 : Nat := 1397191986298069901448751

theorem tailTrace_8163065 : CollatzResearch.WordTrace tailWord_8163065 prefixEnd_8163065 1397191986298069901448751 := by
  unfold tailWord_8163065
  simp only [CollatzResearch.WordTrace]
  refine ⟨297731440171617120353914649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198487626781078080235943099 297731440171617120353914649)
  ·
    refine ⟨223298580128712840265435987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297731440171617120353914649 223298580128712840265435987)
    ·
      refine ⟨334947870193069260398153981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223298580128712840265435987 334947870193069260398153981)
      ·
        refine ⟨125605451322400972649307743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334947870193069260398153981 125605451322400972649307743)
        ·
          refine ⟨188408176983601458973961615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125605451322400972649307743 188408176983601458973961615)
          ·
            refine ⟨282612265475402188460942423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188408176983601458973961615 282612265475402188460942423)
            ·
              refine ⟨423918398213103282691413635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282612265475402188460942423 423918398213103282691413635)
              ·
                refine ⟨635877597319654924037120453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423918398213103282691413635 635877597319654924037120453)
                ·
                  refine ⟨119227049497435298256960085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 635877597319654924037120453 119227049497435298256960085)
                  ·
                    refine ⟨1397191986298069901448751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119227049497435298256960085 1397191986298069901448751)
                    ·
                      rfl

theorem cell23_8163065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 8].length) (baseStart_8163065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163065 prefixEnd_8163065 := by exact prefixLift 8163065
  have htrace : WordTrace (prefixWord ++ tailWord_8163065) baseStart_8163065 baseEnd_8163065 := by
    simpa [prefixWord, tailWord_8163065, baseEnd_8163065] using wordTrace_append hprefix tailTrace_8163065
  have hstable : (prefixWord ++ tailWord_8163065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163065).length < 2 ^ (prefixWord ++ tailWord_8163065).sum := by decide
  have hdescent : baseEnd_8163065 < baseStart_8163065 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163116 : List Nat := [2, 2, 1, 1, 1, 5, 2, 4, 1, 4]
def baseStart_8163116 : Nat := 118140960795 + 8163116 * 2 ^ 59
def prefixEnd_8163116 : Nat := 4983230072969 + 3 ^ 40 * 8163116 * 2
def baseEnd_8163116 : Nat := 1397200715469196334936173

theorem tailTrace_8163116 : CollatzResearch.WordTrace tailWord_8163116 prefixEnd_8163116 1397200715469196334936173 := by
  unfold tailWord_8163116
  simp only [CollatzResearch.WordTrace]
  refine ⟨148866650147216178032010601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198488866862954904042680801 148866650147216178032010601)
  ·
    refine ⟨111649987610412133524007951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148866650147216178032010601 111649987610412133524007951)
    ·
      refine ⟨167474981415618200286011927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111649987610412133524007951 167474981415618200286011927)
      ·
        refine ⟨251212472123427300429017891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167474981415618200286011927 251212472123427300429017891)
        ·
          refine ⟨376818708185140950643526837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251212472123427300429017891 376818708185140950643526837)
          ·
            refine ⟨35326753892356964122830641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 376818708185140950643526837 35326753892356964122830641)
            ·
              refine ⟨26495065419267723092122981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35326753892356964122830641 26495065419267723092122981)
              ·
                refine ⟨4967824766112698079773059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26495065419267723092122981 4967824766112698079773059)
                ·
                  refine ⟨7451737149169047119659589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4967824766112698079773059 7451737149169047119659589)
                  ·
                    refine ⟨1397200715469196334936173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7451737149169047119659589 1397200715469196334936173)
                    ·
                      rfl

theorem cell23_8163116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4, 1, 4].length) (baseStart_8163116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163116 prefixEnd_8163116 := by exact prefixLift 8163116
  have htrace : WordTrace (prefixWord ++ tailWord_8163116) baseStart_8163116 baseEnd_8163116 := by
    simpa [prefixWord, tailWord_8163116, baseEnd_8163116] using wordTrace_append hprefix tailTrace_8163116
  have hstable : (prefixWord ++ tailWord_8163116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163116).length < 2 ^ (prefixWord ++ tailWord_8163116).sum := by decide
  have hdescent : baseEnd_8163116 < baseStart_8163116 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163126 : List Nat := [5, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_8163126 : Nat := 118140960795 + 8163126 * 2 ^ 59
def prefixEnd_8163126 : Nat := 4983230072969 + 3 ^ 40 * 8163126 * 2
def baseEnd_8163126 : Nat := 4191607281214133965683473

theorem tailTrace_8163126 : CollatzResearch.WordTrace tailWord_8163126 prefixEnd_8163126 4191607281214133965683473 := by
  unfold tailWord_8163126
  simp only [CollatzResearch.WordTrace]
  refine ⟨18608354064024757985742827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198489110016264085181256821 18608354064024757985742827)
  ·
    refine ⟨27912531096037136978614241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18608354064024757985742827 27912531096037136978614241)
    ·
      refine ⟨20934398322027852733960681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27912531096037136978614241 20934398322027852733960681)
      ·
        refine ⟨15700798741520889550470511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20934398322027852733960681 15700798741520889550470511)
        ·
          refine ⟨23551198112281334325705767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15700798741520889550470511 23551198112281334325705767)
          ·
            refine ⟨35326797168422001488558651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23551198112281334325705767 35326797168422001488558651)
            ·
              refine ⟨52990195752633002232837977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35326797168422001488558651 52990195752633002232837977)
              ·
                refine ⟨39742646814474751674628483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52990195752633002232837977 39742646814474751674628483)
                ·
                  refine ⟨59613970221712127511942725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39742646814474751674628483 59613970221712127511942725)
                  ·
                    refine ⟨11177619416571023908489261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59613970221712127511942725 11177619416571023908489261)
                    ·
                      refine ⟨4191607281214133965683473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11177619416571023908489261 4191607281214133965683473)
                      ·
                        rfl

theorem cell23_8163126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_8163126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163126 prefixEnd_8163126 := by exact prefixLift 8163126
  have htrace : WordTrace (prefixWord ++ tailWord_8163126) baseStart_8163126 baseEnd_8163126 := by
    simpa [prefixWord, tailWord_8163126, baseEnd_8163126] using wordTrace_append hprefix tailTrace_8163126
  have hstable : (prefixWord ++ tailWord_8163126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163126).length < 2 ^ (prefixWord ++ tailWord_8163126).sum := by decide
  have hdescent : baseEnd_8163126 < baseStart_8163126 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163189 : List Nat := [1, 3, 4, 1, 1, 1, 2, 3, 1, 6]
def baseStart_8163189 : Nat := 118140960795 + 8163189 * 2 ^ 59
def prefixEnd_8163189 : Nat := 4983230072969 + 3 ^ 40 * 8163189 * 2
def baseEnd_8163189 : Nat := 1397213210165122406398561

theorem tailTrace_8163189 : CollatzResearch.WordTrace tailWord_8163189 prefixEnd_8163189 1397213210165122406398561 := by
  unfold tailWord_8163189
  simp only [CollatzResearch.WordTrace]
  refine ⟨297735962823167889531428621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198490641882111926354285747 297735962823167889531428621)
  ·
    refine ⟨111650986058687958574285733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297735962823167889531428621 111650986058687958574285733)
    ·
      refine ⟨20934559886003992232678575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111650986058687958574285733 20934559886003992232678575)
      ·
        refine ⟨31401839829005988349017863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20934559886003992232678575 31401839829005988349017863)
        ·
          refine ⟨47102759743508982523526795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31401839829005988349017863 47102759743508982523526795)
          ·
            refine ⟨70654139615263473785290193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47102759743508982523526795 70654139615263473785290193)
            ·
              refine ⟨52990604711447605338967645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70654139615263473785290193 52990604711447605338967645)
              ·
                refine ⟨19871476766792852002112867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52990604711447605338967645 19871476766792852002112867)
                ·
                  refine ⟨29807215150189278003169301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19871476766792852002112867 29807215150189278003169301)
                  ·
                    refine ⟨1397213210165122406398561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29807215150189278003169301 1397213210165122406398561)
                    ·
                      rfl

theorem cell23_8163189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_8163189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163189 prefixEnd_8163189 := by exact prefixLift 8163189
  have htrace : WordTrace (prefixWord ++ tailWord_8163189) baseStart_8163189 baseEnd_8163189 := by
    simpa [prefixWord, tailWord_8163189, baseEnd_8163189] using wordTrace_append hprefix tailTrace_8163189
  have hstable : (prefixWord ++ tailWord_8163189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163189).length < 2 ^ (prefixWord ++ tailWord_8163189).sum := by decide
  have hdescent : baseEnd_8163189 < baseStart_8163189 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163209 : List Nat := [1, 2, 1, 1, 5, 1, 3, 2, 1, 2, 4]
def baseStart_8163209 : Nat := 118140960795 + 8163209 * 2 ^ 59
def prefixEnd_8163209 : Nat := 4983230072969 + 3 ^ 40 * 8163209 * 2
def baseEnd_8163209 : Nat := 4191649900108457140945591

theorem tailTrace_8163209 : CollatzResearch.WordTrace tailWord_8163209 prefixEnd_8163209 4191649900108457140945591 := by
  unfold tailWord_8163209
  simp only [CollatzResearch.WordTrace]
  refine ⟨297736692283095432947156681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198491128188730288631437787 297736692283095432947156681)
  ·
    refine ⟨223302519212321574710367511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297736692283095432947156681 223302519212321574710367511)
    ·
      refine ⟨334953778818482362065551267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223302519212321574710367511 334953778818482362065551267)
      ·
        refine ⟨502430668227723543098326901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334953778818482362065551267 502430668227723543098326901)
        ·
          refine ⟨47102875146349082165468147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 502430668227723543098326901 47102875146349082165468147)
          ·
            refine ⟨70654312719523623248202221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47102875146349082165468147 70654312719523623248202221)
            ·
              refine ⟨26495367269821358718075833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70654312719523623248202221 26495367269821358718075833)
              ·
                refine ⟨19871525452366019038556875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26495367269821358718075833 19871525452366019038556875)
                ·
                  refine ⟨29807288178549028557835313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19871525452366019038556875 29807288178549028557835313)
                  ·
                    refine ⟨22355466133911771418376485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29807288178549028557835313 22355466133911771418376485)
                    ·
                      refine ⟨4191649900108457140945591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22355466133911771418376485 4191649900108457140945591)
                      ·
                        rfl

theorem cell23_8163209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 2, 4].length) (baseStart_8163209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163209 prefixEnd_8163209 := by exact prefixLift 8163209
  have htrace : WordTrace (prefixWord ++ tailWord_8163209) baseStart_8163209 baseEnd_8163209 := by
    simpa [prefixWord, tailWord_8163209, baseEnd_8163209] using wordTrace_append hprefix tailTrace_8163209
  have hstable : (prefixWord ++ tailWord_8163209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163209).length < 2 ^ (prefixWord ++ tailWord_8163209).sum := by decide
  have hdescent : baseEnd_8163209 < baseStart_8163209 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163224 : List Nat := [2, 1, 2, 6, 1, 2, 2, 2, 1, 1, 3]
def baseStart_8163224 : Nat := 118140960795 + 8163224 * 2 ^ 59
def prefixEnd_8163224 : Nat := 4983230072969 + 3 ^ 40 * 8163224 * 2
def baseEnd_8163224 : Nat := 4191657602318274582258023

theorem tailTrace_8163224 : CollatzResearch.WordTrace tailWord_8163224 prefixEnd_8163224 4191657602318274582258023 := by
  unfold tailWord_8163224
  simp only [CollatzResearch.WordTrace]
  refine ⟨148868619689020545254476363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198491492918694060339301817 148868619689020545254476363)
  ·
    refine ⟨223302929533530817881714545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148868619689020545254476363 223302929533530817881714545)
    ·
      refine ⟨167477197150148113411285909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223302929533530817881714545 167477197150148113411285909)
      ·
        refine ⟨7850493616413192816154027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 167477197150148113411285909 7850493616413192816154027)
        ·
          refine ⟨11775740424619789224231041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7850493616413192816154027 11775740424619789224231041)
          ·
            refine ⟨8831805318464841918173281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11775740424619789224231041 8831805318464841918173281)
            ·
              refine ⟨6623853988848631438629961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8831805318464841918173281 6623853988848631438629961)
              ·
                refine ⟨4967890491636473578972471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6623853988848631438629961 4967890491636473578972471)
                ·
                  refine ⟨7451835737454710368458707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4967890491636473578972471 7451835737454710368458707)
                  ·
                    refine ⟨11177753606182065552688061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7451835737454710368458707 11177753606182065552688061)
                    ·
                      refine ⟨4191657602318274582258023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11177753606182065552688061 4191657602318274582258023)
                      ·
                        rfl

theorem cell23_8163224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_8163224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163224 prefixEnd_8163224 := by exact prefixLift 8163224
  have htrace : WordTrace (prefixWord ++ tailWord_8163224) baseStart_8163224 baseEnd_8163224 := by
    simpa [prefixWord, tailWord_8163224, baseEnd_8163224] using wordTrace_append hprefix tailTrace_8163224
  have hstable : (prefixWord ++ tailWord_8163224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163224).length < 2 ^ (prefixWord ++ tailWord_8163224).sum := by decide
  have hdescent : baseEnd_8163224 < baseStart_8163224 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163256 : List Nat := [2, 1, 2, 1, 2, 3, 1, 3, 3, 3, 2]
def baseStart_8163256 : Nat := 118140960795 + 8163256 * 2 ^ 59
def prefixEnd_8163256 : Nat := 4983230072969 + 3 ^ 40 * 8163256 * 2
def baseEnd_8163256 : Nat := 4191674033699218457057875

theorem tailTrace_8163256 : CollatzResearch.WordTrace tailWord_8163256 prefixEnd_8163256 4191674033699218457057875 := by
  unfold tailWord_8163256
  simp only [CollatzResearch.WordTrace]
  refine ⟨148869203256962579987058811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198492271009283439982745081 148869203256962579987058811)
  ·
    refine ⟨223303804885443869980588217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148869203256962579987058811 223303804885443869980588217)
    ·
      refine ⟨167477853664082902485441163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223303804885443869980588217 167477853664082902485441163)
      ·
        refine ⟨251216780496124353728161745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167477853664082902485441163 251216780496124353728161745)
        ·
          refine ⟨188412585372093265296121309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251216780496124353728161745 188412585372093265296121309)
          ·
            refine ⟨70654719514534974486045491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188412585372093265296121309 70654719514534974486045491)
            ·
              refine ⟨105982079271802461729068237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70654719514534974486045491 105982079271802461729068237)
              ·
                refine ⟨39743279726925923148400589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105982079271802461729068237 39743279726925923148400589)
                ·
                  refine ⟨14903729897597221180650221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39743279726925923148400589 14903729897597221180650221)
                  ·
                    refine ⟨5588898711598957942743833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14903729897597221180650221 5588898711598957942743833)
                    ·
                      refine ⟨4191674033699218457057875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5588898711598957942743833 4191674033699218457057875)
                      ·
                        rfl

theorem cell23_8163256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 3, 3, 2].length) (baseStart_8163256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163256 prefixEnd_8163256 := by exact prefixLift 8163256
  have htrace : WordTrace (prefixWord ++ tailWord_8163256) baseStart_8163256 baseEnd_8163256 := by
    simpa [prefixWord, tailWord_8163256, baseEnd_8163256] using wordTrace_append hprefix tailTrace_8163256
  have hstable : (prefixWord ++ tailWord_8163256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163256).length < 2 ^ (prefixWord ++ tailWord_8163256).sum := by decide
  have hdescent : baseEnd_8163256 < baseStart_8163256 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163376 : List Nat := [2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 4]
def baseStart_8163376 : Nat := 118140960795 + 8163376 * 2 ^ 59
def prefixEnd_8163376 : Nat := 4983230072969 + 3 ^ 40 * 8163376 * 2
def baseEnd_8163376 : Nat := 4191735651377757987557323

theorem tailTrace_8163376 : CollatzResearch.WordTrace tailWord_8163376 prefixEnd_8163376 4191735651377757987557323 := by
  unfold tailWord_8163376
  simp only [CollatzResearch.WordTrace]
  refine ⟨148871391636745210234242991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198495188848993613645657321 148871391636745210234242991)
  ·
    refine ⟨223307087455117815351364487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148871391636745210234242991 223307087455117815351364487)
    ·
      refine ⟨334960631182676723027046731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223307087455117815351364487 334960631182676723027046731)
      ·
        refine ⟨502440946774015084540570097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334960631182676723027046731 502440946774015084540570097)
        ·
          refine ⟨376830710080511313405427573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502440946774015084540570097 376830710080511313405427573)
          ·
            refine ⟨35327879070047935631758835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 376830710080511313405427573 35327879070047935631758835)
            ·
              refine ⟨52991818605071903447638253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35327879070047935631758835 52991818605071903447638253)
              ·
                refine ⟨19871931976901963792864345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52991818605071903447638253 19871931976901963792864345)
                ·
                  refine ⟨14903948982676472844648259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19871931976901963792864345 14903948982676472844648259)
                  ·
                    refine ⟨22355923474014709266972389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14903948982676472844648259 22355923474014709266972389)
                    ·
                      refine ⟨4191735651377757987557323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22355923474014709266972389 4191735651377757987557323)
                      ·
                        rfl

theorem cell23_8163376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 4].length) (baseStart_8163376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163376 prefixEnd_8163376 := by exact prefixLift 8163376
  have htrace : WordTrace (prefixWord ++ tailWord_8163376) baseStart_8163376 baseEnd_8163376 := by
    simpa [prefixWord, tailWord_8163376, baseEnd_8163376] using wordTrace_append hprefix tailTrace_8163376
  have hstable : (prefixWord ++ tailWord_8163376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163376).length < 2 ^ (prefixWord ++ tailWord_8163376).sum := by decide
  have hdescent : baseEnd_8163376 < baseStart_8163376 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163393 : List Nat := [1, 2, 5, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_8163393 : Nat := 118140960795 + 8163393 * 2 ^ 59
def prefixEnd_8163393 : Nat := 4983230072969 + 3 ^ 40 * 8163393 * 2
def baseEnd_8163393 : Nat := 4191744380548884421044745

theorem tailTrace_8163393 : CollatzResearch.WordTrace tailWord_8163393 prefixEnd_8163393 4191744380548884421044745 := by
  unfold tailWord_8163393
  simp only [CollatzResearch.WordTrace]
  refine ⟨297743403314428832371854833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198495602209619221581236555 297743403314428832371854833)
  ·
    refine ⟨223307552485821624278891125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297743403314428832371854833 223307552485821624278891125)
    ·
      refine ⟨20935083045545777276146043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223307552485821624278891125 20935083045545777276146043)
      ·
        refine ⟨31402624568318665914219065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20935083045545777276146043 31402624568318665914219065)
        ·
          refine ⟨23551968426238999435664299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31402624568318665914219065 23551968426238999435664299)
          ·
            refine ⟨35327952639358499153496449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23551968426238999435664299 35327952639358499153496449)
            ·
              refine ⟨26495964479518874365122337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35327952639358499153496449 26495964479518874365122337)
              ·
                refine ⟨19871973359639155773841753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26495964479518874365122337 19871973359639155773841753)
                ·
                  refine ⟨14903980019729366830381315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19871973359639155773841753 14903980019729366830381315)
                  ·
                    refine ⟨22355970029594050245571973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14903980019729366830381315 22355970029594050245571973)
                    ·
                      refine ⟨4191744380548884421044745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22355970029594050245571973 4191744380548884421044745)
                      ·
                        rfl

theorem cell23_8163393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_8163393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163393 prefixEnd_8163393 := by exact prefixLift 8163393
  have htrace : WordTrace (prefixWord ++ tailWord_8163393) baseStart_8163393 baseEnd_8163393 := by
    simpa [prefixWord, tailWord_8163393, baseEnd_8163393] using wordTrace_append hprefix tailTrace_8163393
  have hstable : (prefixWord ++ tailWord_8163393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163393).length < 2 ^ (prefixWord ++ tailWord_8163393).sum := by decide
  have hdescent : baseEnd_8163393 < baseStart_8163393 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163403 : List Nat := [1, 1, 1, 1, 3, 1, 2, 8, 1, 4]
def baseStart_8163403 : Nat := 118140960795 + 8163403 * 2 ^ 59
def prefixEnd_8163403 : Nat := 4983230072969 + 3 ^ 40 * 8163403 * 2
def baseEnd_8163403 : Nat := 1397249838451809793973233

theorem tailTrace_8163403 : CollatzResearch.WordTrace tailWord_8163403 prefixEnd_8163403 1397249838451809793973233 := by
  unfold tailWord_8163403
  simp only [CollatzResearch.WordTrace]
  refine ⟨297743768044392604079718863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198495845362928402719812575 297743768044392604079718863)
  ·
    refine ⟨446615652066588906119578295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297743768044392604079718863 446615652066588906119578295)
    ·
      refine ⟨669923478099883359179367443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446615652066588906119578295 669923478099883359179367443)
      ·
        refine ⟨1004885217149825038769051165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669923478099883359179367443 1004885217149825038769051165)
        ·
          refine ⟨376831956431184389538394187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1004885217149825038769051165 376831956431184389538394187)
          ·
            refine ⟨565247934646776584307591281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376831956431184389538394187 565247934646776584307591281)
            ·
              refine ⟨423935950985082438230693461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 565247934646776584307591281 423935950985082438230693461)
              ·
                refine ⟨4967999425606434823015939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 423935950985082438230693461 4967999425606434823015939)
                ·
                  refine ⟨7451999138409652234523909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4967999425606434823015939 7451999138409652234523909)
                  ·
                    refine ⟨1397249838451809793973233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7451999138409652234523909 1397249838451809793973233)
                    ·
                      rfl

theorem cell23_8163403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8, 1, 4].length) (baseStart_8163403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163403 prefixEnd_8163403 := by exact prefixLift 8163403
  have htrace : WordTrace (prefixWord ++ tailWord_8163403) baseStart_8163403 baseEnd_8163403 := by
    simpa [prefixWord, tailWord_8163403, baseEnd_8163403] using wordTrace_append hprefix tailTrace_8163403
  have hstable : (prefixWord ++ tailWord_8163403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163403).length < 2 ^ (prefixWord ++ tailWord_8163403).sum := by decide
  have hdescent : baseEnd_8163403 < baseStart_8163403 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163410 : List Nat := [3, 2, 2, 1, 4, 1, 1, 1, 2, 4, 2]
def baseStart_8163410 : Nat := 118140960795 + 8163410 * 2 ^ 59
def prefixEnd_8163410 : Nat := 4983230072969 + 3 ^ 40 * 8163410 * 2
def baseEnd_8163410 : Nat := 4191753109720010854532167

theorem tailTrace_8163410 : CollatzResearch.WordTrace tailWord_8163410 prefixEnd_8163410 4191753109720010854532167 := by
  unfold tailWord_8163410
  simp only [CollatzResearch.WordTrace]
  refine ⟨74436005838841811068805921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198496015570244829516815789 74436005838841811068805921)
  ·
    refine ⟨55827004379131358301604441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74436005838841811068805921 55827004379131358301604441)
    ·
      refine ⟨41870253284348518726203331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55827004379131358301604441 41870253284348518726203331)
      ·
        refine ⟨62805379926522778089304997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41870253284348518726203331 62805379926522778089304997)
        ·
          refine ⟨11776008736223020891744687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62805379926522778089304997 11776008736223020891744687)
          ·
            refine ⟨17664013104334531337617031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11776008736223020891744687 17664013104334531337617031)
            ·
              refine ⟨26496019656501797006425547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17664013104334531337617031 26496019656501797006425547)
              ·
                refine ⟨39744029484752695509638321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26496019656501797006425547 39744029484752695509638321)
                ·
                  refine ⟨29808022113564521632228741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39744029484752695509638321 29808022113564521632228741)
                  ·
                    refine ⟨5589004146293347806042889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29808022113564521632228741 5589004146293347806042889)
                    ·
                      refine ⟨4191753109720010854532167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5589004146293347806042889 4191753109720010854532167)
                      ·
                        rfl

theorem cell23_8163410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_8163410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163410 prefixEnd_8163410 := by exact prefixLift 8163410
  have htrace : WordTrace (prefixWord ++ tailWord_8163410) baseStart_8163410 baseEnd_8163410 := by
    simpa [prefixWord, tailWord_8163410, baseEnd_8163410] using wordTrace_append hprefix tailTrace_8163410
  have hstable : (prefixWord ++ tailWord_8163410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163410).length < 2 ^ (prefixWord ++ tailWord_8163410).sum := by decide
  have hdescent : baseEnd_8163410 < baseStart_8163410 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163416 : List Nat := [2, 1, 2, 2, 1, 4, 2, 3, 6]
def baseStart_8163416 : Nat := 118140960795 + 8163416 * 2 ^ 59
def prefixEnd_8163416 : Nat := 4983230072969 + 3 ^ 40 * 8163416 * 2
def baseEnd_8163416 : Nat := 465750687844881981228571

theorem tailTrace_8163416 : CollatzResearch.WordTrace tailWord_8163416 prefixEnd_8163416 465750687844881981228571 := by
  unfold tailWord_8163416
  simp only [CollatzResearch.WordTrace]
  refine ⟨148872121096672753649971051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198496161462230338199961401 148872121096672753649971051)
  ·
    refine ⟨223308181645009130474956577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148872121096672753649971051 223308181645009130474956577)
    ·
      refine ⟨167481136233756847856217433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223308181645009130474956577 167481136233756847856217433)
      ·
        refine ⟨125610852175317635892163075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167481136233756847856217433 125610852175317635892163075)
        ·
          refine ⟨188416278262976453838244613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125610852175317635892163075 188416278262976453838244613)
          ·
            refine ⟨35328052174308085094670865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188416278262976453838244613 35328052174308085094670865)
            ·
              refine ⟨26496039130731063821003149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35328052174308085094670865 26496039130731063821003149)
              ·
                refine ⟨9936014674024148932876181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26496039130731063821003149 9936014674024148932876181)
                ·
                  refine ⟨465750687844881981228571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9936014674024148932876181 465750687844881981228571)
                  ·
                    rfl

theorem cell23_8163416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 6].length) (baseStart_8163416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163416 prefixEnd_8163416 := by exact prefixLift 8163416
  have htrace : WordTrace (prefixWord ++ tailWord_8163416) baseStart_8163416 baseEnd_8163416 := by
    simpa [prefixWord, tailWord_8163416, baseEnd_8163416] using wordTrace_append hprefix tailTrace_8163416
  have hstable : (prefixWord ++ tailWord_8163416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163416).length < 2 ^ (prefixWord ++ tailWord_8163416).sum := by decide
  have hdescent : baseEnd_8163416 < baseStart_8163416 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163460 : List Nat := [2, 3, 2, 1, 2, 1, 4, 1, 3, 1, 3]
def baseStart_8163460 : Nat := 118140960795 + 8163460 * 2 ^ 59
def prefixEnd_8163460 : Nat := 4983230072969 + 3 ^ 40 * 8163460 * 2
def baseEnd_8163460 : Nat := 4191778783752735658906937

theorem tailTrace_8163460 : CollatzResearch.WordTrace tailWord_8163460 prefixEnd_8163460 4191778783752735658906937 := by
  unfold tailWord_8163460
  simp only [CollatzResearch.WordTrace]
  refine ⟨148872923502593051407271917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198497231336790735209695889 148872923502593051407271917)
  ·
    refine ⟨55827346313472394277726969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148872923502593051407271917 55827346313472394277726969)
    ·
      refine ⟨41870509735104295708295227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55827346313472394277726969 41870509735104295708295227)
      ·
        refine ⟨62805764602656443562442841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41870509735104295708295227 62805764602656443562442841)
        ·
          refine ⟨47104323451992332671832131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62805764602656443562442841 47104323451992332671832131)
          ·
            refine ⟨70656485177988499007748197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47104323451992332671832131 70656485177988499007748197)
            ·
              refine ⟨13248090970872843563952787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70656485177988499007748197 13248090970872843563952787)
              ·
                refine ⟨19872136456309265345929181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13248090970872843563952787 19872136456309265345929181)
                ·
                  refine ⟨7452051171115974504723443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19872136456309265345929181 7452051171115974504723443)
                  ·
                    refine ⟨11178076756673961757085165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7452051171115974504723443 11178076756673961757085165)
                    ·
                      refine ⟨4191778783752735658906937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11178076756673961757085165 4191778783752735658906937)
                      ·
                        rfl

theorem cell23_8163460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_8163460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163460 prefixEnd_8163460 := by exact prefixLift 8163460
  have htrace : WordTrace (prefixWord ++ tailWord_8163460) baseStart_8163460 baseEnd_8163460 := by
    simpa [prefixWord, tailWord_8163460, baseEnd_8163460] using wordTrace_append hprefix tailTrace_8163460
  have hstable : (prefixWord ++ tailWord_8163460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163460).length < 2 ^ (prefixWord ++ tailWord_8163460).sum := by decide
  have hdescent : baseEnd_8163460 < baseStart_8163460 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163480 : List Nat := [2, 1, 2, 4, 3, 1, 2, 2, 1, 5]
def baseStart_8163480 : Nat := 118140960795 + 8163480 * 2 ^ 59
def prefixEnd_8163480 : Nat := 4983230072969 + 3 ^ 40 * 8163480 * 2
def baseEnd_8163480 : Nat := 1397263017788608526885615

theorem tailTrace_8163480 : CollatzResearch.WordTrace tailWord_8163480 prefixEnd_8163480 1397263017788608526885615 := by
  unfold tailWord_8163480
  simp only [CollatzResearch.WordTrace]
  refine ⟨148873288232556823115135947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198497717643409097486847929 148873288232556823115135947)
  ·
    refine ⟨223309932348835234672703921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148873288232556823115135947 223309932348835234672703921)
    ·
      refine ⟨167482449261626426004527941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223309932348835234672703921 167482449261626426004527941)
      ·
        refine ⟨31402959236554954875848989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167482449261626426004527941 31402959236554954875848989)
        ·
          refine ⟨11776109713708108078443371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31402959236554954875848989 11776109713708108078443371)
          ·
            refine ⟨17664164570562162117665057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11776109713708108078443371 17664164570562162117665057)
            ·
              refine ⟨13248123427921621588248793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17664164570562162117665057 13248123427921621588248793)
              ·
                refine ⟨9936092570941216191186595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13248123427921621588248793 9936092570941216191186595)
                ·
                  refine ⟨14904138856411824286779893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9936092570941216191186595 14904138856411824286779893)
                  ·
                    refine ⟨1397263017788608526885615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14904138856411824286779893 1397263017788608526885615)
                    ·
                      rfl

theorem cell23_8163480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 1, 5].length) (baseStart_8163480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163480 prefixEnd_8163480 := by exact prefixLift 8163480
  have htrace : WordTrace (prefixWord ++ tailWord_8163480) baseStart_8163480 baseEnd_8163480 := by
    simpa [prefixWord, tailWord_8163480, baseEnd_8163480] using wordTrace_append hprefix tailTrace_8163480
  have hstable : (prefixWord ++ tailWord_8163480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163480).length < 2 ^ (prefixWord ++ tailWord_8163480).sum := by decide
  have hdescent : baseEnd_8163480 < baseStart_8163480 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163546 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5]
def baseStart_8163546 : Nat := 118140960795 + 8163546 * 2 ^ 59
def prefixEnd_8163546 : Nat := 4983230072969 + 3 ^ 40 * 8163546 * 2
def baseEnd_8163546 : Nat := 4191822943089022322431541

theorem tailTrace_8163546 : CollatzResearch.WordTrace tailWord_8163546 prefixEnd_8163546 4191822943089022322431541 := by
  unfold tailWord_8163546
  simp only [CollatzResearch.WordTrace]
  refine ⟨74437245920718634875543623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198499322455249693001449661 74437245920718634875543623)
  ·
    refine ⟨111655868881077952313315435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74437245920718634875543623 111655868881077952313315435)
    ·
      refine ⟨167483803321616928469973153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111655868881077952313315435 167483803321616928469973153)
      ·
        refine ⟨125612852491212696352479865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167483803321616928469973153 125612852491212696352479865)
        ·
          refine ⟨94209639368409522264359899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125612852491212696352479865 94209639368409522264359899)
          ·
            refine ⟨141314459052614283396539849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94209639368409522264359899 141314459052614283396539849)
            ·
              refine ⟨105985844289460712547404887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141314459052614283396539849 105985844289460712547404887)
              ·
                refine ⟨158978766434191068821107331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105985844289460712547404887 158978766434191068821107331)
                ·
                  refine ⟨238468149651286603231660997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158978766434191068821107331 238468149651286603231660997)
                  ·
                    refine ⟨44712778059616238105936437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 238468149651286603231660997 44712778059616238105936437)
                    ·
                      refine ⟨4191822943089022322431541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44712778059616238105936437 4191822943089022322431541)
                      ·
                        rfl

theorem cell23_8163546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_8163546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163546 prefixEnd_8163546 := by exact prefixLift 8163546
  have htrace : WordTrace (prefixWord ++ tailWord_8163546) baseStart_8163546 baseEnd_8163546 := by
    simpa [prefixWord, tailWord_8163546, baseEnd_8163546] using wordTrace_append hprefix tailTrace_8163546
  have hstable : (prefixWord ++ tailWord_8163546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163546).length < 2 ^ (prefixWord ++ tailWord_8163546).sum := by decide
  have hdescent : baseEnd_8163546 < baseStart_8163546 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163567 : List Nat := [1, 1, 2, 1, 6, 2, 2, 2, 2, 1, 3]
def baseStart_8163567 : Nat := 118140960795 + 8163567 * 2 ^ 59
def prefixEnd_8163567 : Nat := 4983230072969 + 3 ^ 40 * 8163567 * 2
def baseEnd_8163567 : Nat := 4191833726182766740268945

theorem tailTrace_8163567 : CollatzResearch.WordTrace tailWord_8163567 prefixEnd_8163567 4191833726182766740268945 := by
  unfold tailWord_8163567
  simp only [CollatzResearch.WordTrace]
  refine ⟨297749749615798460088688955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198499833077198973392459303 297749749615798460088688955)
  ·
    refine ⟨446624624423697690133033433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297749749615798460088688955 446624624423697690133033433)
    ·
      refine ⟨334968468317773267599775075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446624624423697690133033433 334968468317773267599775075)
      ·
        refine ⟨502452702476659901399662613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334968468317773267599775075 502452702476659901399662613)
        ·
          refine ⟨23552470428593432878109185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 502452702476659901399662613 23552470428593432878109185)
          ·
            refine ⟨17664352821445074658581889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23552470428593432878109185 17664352821445074658581889)
            ·
              refine ⟨13248264616083805993936417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17664352821445074658581889 13248264616083805993936417)
              ·
                refine ⟨9936198462062854495452313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13248264616083805993936417 9936198462062854495452313)
                ·
                  refine ⟨7452148846547140871589235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9936198462062854495452313 7452148846547140871589235)
                  ·
                    refine ⟨11178223269820711307383853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7452148846547140871589235 11178223269820711307383853)
                    ·
                      refine ⟨4191833726182766740268945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11178223269820711307383853 4191833726182766740268945)
                      ·
                        rfl

theorem cell23_8163567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2, 1, 3].length) (baseStart_8163567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163567 prefixEnd_8163567 := by exact prefixLift 8163567
  have htrace : WordTrace (prefixWord ++ tailWord_8163567) baseStart_8163567 baseEnd_8163567 := by
    simpa [prefixWord, tailWord_8163567, baseEnd_8163567] using wordTrace_append hprefix tailTrace_8163567
  have hstable : (prefixWord ++ tailWord_8163567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163567).length < 2 ^ (prefixWord ++ tailWord_8163567).sum := by decide
  have hdescent : baseEnd_8163567 < baseStart_8163567 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163576 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 1, 3, 5]
def baseStart_8163576 : Nat := 118140960795 + 8163576 * 2 ^ 59
def prefixEnd_8163576 : Nat := 4983230072969 + 3 ^ 40 * 8163576 * 2
def baseEnd_8163576 : Nat := 4191838347508657205056403

theorem tailTrace_8163576 : CollatzResearch.WordTrace tailWord_8163576 prefixEnd_8163576 4191838347508657205056403 := by
  unfold tailWord_8163576
  simp only [CollatzResearch.WordTrace]
  refine ⟨148875038936382927312883291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198500051915177236417177721 148875038936382927312883291)
  ·
    refine ⟨223312558404574390969324937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148875038936382927312883291 223312558404574390969324937)
    ·
      refine ⟨167484418803430793226993703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223312558404574390969324937 167484418803430793226993703)
      ·
        refine ⟨251226628205146189840490555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167484418803430793226993703 251226628205146189840490555)
        ·
          refine ⟨376839942307719284760735833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251226628205146189840490555 376839942307719284760735833)
          ·
            refine ⟨282629956730789463570551875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376839942307719284760735833 282629956730789463570551875)
            ·
              refine ⟨423944935096184195355827813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282629956730789463570551875 423944935096184195355827813)
              ·
                refine ⟨79489675330534536629217715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 423944935096184195355827813 79489675330534536629217715)
                ·
                  refine ⟨119234512995801804943826573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79489675330534536629217715 119234512995801804943826573)
                  ·
                    refine ⟨44712942373425676853934965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119234512995801804943826573 44712942373425676853934965)
                    ·
                      refine ⟨4191838347508657205056403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44712942373425676853934965 4191838347508657205056403)
                      ·
                        rfl

theorem cell23_8163576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_8163576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163576 prefixEnd_8163576 := by exact prefixLift 8163576
  have htrace : WordTrace (prefixWord ++ tailWord_8163576) baseStart_8163576 baseEnd_8163576 := by
    simpa [prefixWord, tailWord_8163576, baseEnd_8163576] using wordTrace_append hprefix tailTrace_8163576
  have hstable : (prefixWord ++ tailWord_8163576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163576).length < 2 ^ (prefixWord ++ tailWord_8163576).sum := by decide
  have hdescent : baseEnd_8163576 < baseStart_8163576 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163624 : List Nat := [2, 1, 5, 1, 3, 1, 1, 1, 4, 2, 2]
def baseStart_8163624 : Nat := 118140960795 + 8163624 * 2 ^ 59
def prefixEnd_8163624 : Nat := 4983230072969 + 3 ^ 40 * 8163624 * 2
def baseEnd_8163624 : Nat := 4191862994580073017256183

theorem tailTrace_8163624 : CollatzResearch.WordTrace tailWord_8163624 prefixEnd_8163624 4191862994580073017256183 := by
  unfold tailWord_8163624
  simp only [CollatzResearch.WordTrace]
  refine ⟨148875914288295979411756963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198501219051061305882342617 148875914288295979411756963)
  ·
    refine ⟨223313871432443969117635445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148875914288295979411756963 223313871432443969117635445)
    ·
      refine ⟨20935675446791622104778323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223313871432443969117635445 20935675446791622104778323)
      ·
        refine ⟨31403513170187433157167485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20935675446791622104778323 31403513170187433157167485)
        ·
          refine ⟨11776317438820287433937807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31403513170187433157167485 11776317438820287433937807)
          ·
            refine ⟨17664476158230431150906711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11776317438820287433937807 17664476158230431150906711)
            ·
              refine ⟨26496714237345646726360067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17664476158230431150906711 26496714237345646726360067)
              ·
                refine ⟨39745071356018470089540101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26496714237345646726360067 39745071356018470089540101)
                ·
                  refine ⟨7452200879253463141788769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39745071356018470089540101 7452200879253463141788769)
                  ·
                    refine ⟨5589150659440097356341577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7452200879253463141788769 5589150659440097356341577)
                    ·
                      refine ⟨4191862994580073017256183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5589150659440097356341577 4191862994580073017256183)
                      ·
                        rfl

theorem cell23_8163624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_8163624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163624 prefixEnd_8163624 := by exact prefixLift 8163624
  have htrace : WordTrace (prefixWord ++ tailWord_8163624) baseStart_8163624 baseEnd_8163624 := by
    simpa [prefixWord, tailWord_8163624, baseEnd_8163624] using wordTrace_append hprefix tailTrace_8163624
  have hstable : (prefixWord ++ tailWord_8163624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163624).length < 2 ^ (prefixWord ++ tailWord_8163624).sum := by decide
  have hdescent : baseEnd_8163624 < baseStart_8163624 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163641 : List Nat := [1, 2, 1, 6, 1, 2, 3, 1, 2, 2, 2]
def baseStart_8163641 : Nat := 118140960795 + 8163641 * 2 ^ 59
def prefixEnd_8163641 : Nat := 4983230072969 + 3 ^ 40 * 8163641 * 2
def baseEnd_8163641 : Nat := 4191871723751199450743605

theorem tailTrace_8163641 : CollatzResearch.WordTrace tailWord_8163641 prefixEnd_8163641 4191871723751199450743605 := by
  unfold tailWord_8163641
  simp only [CollatzResearch.WordTrace]
  refine ⟨297752448617530370726882777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198501632411686913817921851 297752448617530370726882777)
  ·
    refine ⟨223314336463147778045162083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297752448617530370726882777 223314336463147778045162083)
    ·
      refine ⟨334971504694721667067743125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223314336463147778045162083 334971504694721667067743125)
      ·
        refine ⟨15701789282565078143800459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 334971504694721667067743125 15701789282565078143800459)
        ·
          refine ⟨23552683923847617215700689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15701789282565078143800459 23552683923847617215700689)
          ·
            refine ⟨17664512942885712911775517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23552683923847617215700689 17664512942885712911775517)
            ·
              refine ⟨6624192353582142341915819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17664512942885712911775517 6624192353582142341915819)
              ·
                refine ⟨9936288530373213512873729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6624192353582142341915819 9936288530373213512873729)
                ·
                  refine ⟨7452216397779910134655297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9936288530373213512873729 7452216397779910134655297)
                  ·
                    refine ⟨5589162298334932600991473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7452216397779910134655297 5589162298334932600991473)
                    ·
                      refine ⟨4191871723751199450743605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5589162298334932600991473 4191871723751199450743605)
                      ·
                        rfl

theorem cell23_8163641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_8163641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163641 prefixEnd_8163641 := by exact prefixLift 8163641
  have htrace : WordTrace (prefixWord ++ tailWord_8163641) baseStart_8163641 baseEnd_8163641 := by
    simpa [prefixWord, tailWord_8163641, baseEnd_8163641] using wordTrace_append hprefix tailTrace_8163641
  have hstable : (prefixWord ++ tailWord_8163641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163641).length < 2 ^ (prefixWord ++ tailWord_8163641).sum := by decide
  have hdescent : baseEnd_8163641 < baseStart_8163641 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163774 : List Nat := [4, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2]
def baseStart_8163774 : Nat := 118140960795 + 8163774 * 2 ^ 59
def prefixEnd_8163774 : Nat := 4983230072969 + 3 ^ 40 * 8163774 * 2
def baseEnd_8163774 : Nat := 4191940016678247430380493

theorem tailTrace_8163774 : CollatzResearch.WordTrace tailWord_8163774 prefixEnd_8163774 4191940016678247430380493 := by
  unfold tailWord_8163774
  simp only [CollatzResearch.WordTrace]
  refine ⟨37219662440756066805184297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198504866350699022960982917 37219662440756066805184297)
  ·
    refine ⟨27914746830567050103888223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37219662440756066805184297 27914746830567050103888223)
    ·
      refine ⟨41872120245850575155832335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27914746830567050103888223 41872120245850575155832335)
      ·
        refine ⟨62808180368775862733748503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41872120245850575155832335 62808180368775862733748503)
        ·
          refine ⟨94212270553163794100622755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62808180368775862733748503 94212270553163794100622755)
          ·
            refine ⟨141318405829745691150934133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94212270553163794100622755 141318405829745691150934133)
            ·
              refine ⟨13248600546538658545400075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141318405829745691150934133 13248600546538658545400075)
              ·
                refine ⟨19872900819807987818100113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13248600546538658545400075 19872900819807987818100113)
                ·
                  refine ⟨14904675614855990863575085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19872900819807987818100113 14904675614855990863575085)
                  ·
                    refine ⟨5589253355570996573840657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14904675614855990863575085 5589253355570996573840657)
                    ·
                      refine ⟨4191940016678247430380493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5589253355570996573840657 4191940016678247430380493)
                      ·
                        rfl

theorem cell23_8163774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_8163774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163774 prefixEnd_8163774 := by exact prefixLift 8163774
  have htrace : WordTrace (prefixWord ++ tailWord_8163774) baseStart_8163774 baseEnd_8163774 := by
    simpa [prefixWord, tailWord_8163774, baseEnd_8163774] using wordTrace_append hprefix tailTrace_8163774
  have hstable : (prefixWord ++ tailWord_8163774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163774).length < 2 ^ (prefixWord ++ tailWord_8163774).sum := by decide
  have hdescent : baseEnd_8163774 < baseStart_8163774 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163784 : List Nat := [2, 1, 3, 1, 3, 4, 2, 1, 1, 5]
def baseStart_8163784 : Nat := 118140960795 + 8163784 * 2 ^ 59
def prefixEnd_8163784 : Nat := 4983230072969 + 3 ^ 40 * 8163784 * 2
def baseEnd_8163784 : Nat := 1397315050494930797085149

theorem tailTrace_8163784 : CollatzResearch.WordTrace tailWord_8163784 prefixEnd_8163784 1397315050494930797085149 := by
  unfold tailWord_8163784
  simp only [CollatzResearch.WordTrace]
  refine ⟨148878832128006153074669203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198505109504008204099558937 148878832128006153074669203)
  ·
    refine ⟨223318248192009229612003805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148878832128006153074669203 223318248192009229612003805)
    ·
      refine ⟨83744343072003461104501427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223318248192009229612003805 83744343072003461104501427)
      ·
        refine ⟨125616514608005191656752141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83744343072003461104501427 125616514608005191656752141)
        ·
          refine ⟨47106192978001946871282053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125616514608005191656752141 47106192978001946871282053)
          ·
            refine ⟨8832411183375365038365385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47106192978001946871282053 8832411183375365038365385)
            ·
              refine ⟨6624308387531523778774039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8832411183375365038365385 6624308387531523778774039)
              ·
                refine ⟨9936462581297285668161059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6624308387531523778774039 9936462581297285668161059)
                ·
                  refine ⟨14904693871945928502241589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9936462581297285668161059 14904693871945928502241589)
                  ·
                    refine ⟨1397315050494930797085149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14904693871945928502241589 1397315050494930797085149)
                    ·
                      rfl

theorem cell23_8163784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_8163784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163784 prefixEnd_8163784 := by exact prefixLift 8163784
  have htrace : WordTrace (prefixWord ++ tailWord_8163784) baseStart_8163784 baseEnd_8163784 := by
    simpa [prefixWord, tailWord_8163784, baseEnd_8163784] using wordTrace_append hprefix tailTrace_8163784
  have hstable : (prefixWord ++ tailWord_8163784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163784).length < 2 ^ (prefixWord ++ tailWord_8163784).sum := by decide
  have hdescent : baseEnd_8163784 < baseStart_8163784 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163787 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 7, 2, 2]
def baseStart_8163787 : Nat := 118140960795 + 8163787 * 2 ^ 59
def prefixEnd_8163787 : Nat := 4983230072969 + 3 ^ 40 * 8163787 * 2
def baseEnd_8163787 : Nat := 4191946691926755879517933

theorem tailTrace_8163787 : CollatzResearch.WordTrace tailWord_8163787 prefixEnd_8163787 4191946691926755879517933 := by
  unfold tailWord_8163787
  simp only [CollatzResearch.WordTrace]
  refine ⟨297757773675001437661697615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198505182450000958441131743 297757773675001437661697615)
  ·
    refine ⟨446636660512502156492546423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297757773675001437661697615 446636660512502156492546423)
    ·
      refine ⟨669954990768753234738819635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446636660512502156492546423 669954990768753234738819635)
      ·
        refine ⟨1004932486153129852108229453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669954990768753234738819635 1004932486153129852108229453)
        ·
          refine ⟨376849682307423694540586045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1004932486153129852108229453 376849682307423694540586045)
          ·
            refine ⟨141318630865283885452719767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 376849682307423694540586045 141318630865283885452719767)
            ·
              refine ⟨211977946297925828179079651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141318630865283885452719767 211977946297925828179079651)
              ·
                refine ⟨317966919446888742268619477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211977946297925828179079651 317966919446888742268619477)
                ·
                  refine ⟨7452349674536454896920769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 317966919446888742268619477 7452349674536454896920769)
                  ·
                    refine ⟨5589262255902341172690577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7452349674536454896920769 5589262255902341172690577)
                    ·
                      refine ⟨4191946691926755879517933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5589262255902341172690577 4191946691926755879517933)
                      ·
                        rfl

theorem cell23_8163787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7, 2, 2].length) (baseStart_8163787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163787 prefixEnd_8163787 := by exact prefixLift 8163787
  have htrace : WordTrace (prefixWord ++ tailWord_8163787) baseStart_8163787 baseEnd_8163787 := by
    simpa [prefixWord, tailWord_8163787, baseEnd_8163787] using wordTrace_append hprefix tailTrace_8163787
  have hstable : (prefixWord ++ tailWord_8163787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163787).length < 2 ^ (prefixWord ++ tailWord_8163787).sum := by decide
  have hdescent : baseEnd_8163787 < baseStart_8163787 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163790 : List Nat := [4, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5]
def baseStart_8163790 : Nat := 118140960795 + 8163790 * 2 ^ 59
def prefixEnd_8163790 : Nat := 4983230072969 + 3 ^ 40 * 8163790 * 2
def baseEnd_8163790 : Nat := 4191948232368719367780419

theorem tailTrace_8163790 : CollatzResearch.WordTrace tailWord_8163790 prefixEnd_8163790 4191948232368719367780419 := by
  unfold tailWord_8163790
  simp only [CollatzResearch.WordTrace]
  refine ⟨37219735386748821146757103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198505255395993712782704549 37219735386748821146757103)
  ·
    refine ⟨55829603080123231720135655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37219735386748821146757103 55829603080123231720135655)
    ·
      refine ⟨83744404620184847580203483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55829603080123231720135655 83744404620184847580203483)
      ·
        refine ⟨125616606930277271370305225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83744404620184847580203483 125616606930277271370305225)
        ·
          refine ⟨94212455197707953527728919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125616606930277271370305225 94212455197707953527728919)
          ·
            refine ⟨141318682796561930291593379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94212455197707953527728919 141318682796561930291593379)
            ·
              refine ⟨211978024194842895437390069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141318682796561930291593379 211978024194842895437390069)
              ·
                refine ⟨19872939768266521447255319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 211978024194842895437390069 19872939768266521447255319)
                ·
                  refine ⟨29809409652399782170882979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19872939768266521447255319 29809409652399782170882979)
                  ·
                    refine ⟨44714114478599673256324469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29809409652399782170882979 44714114478599673256324469)
                    ·
                      refine ⟨4191948232368719367780419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44714114478599673256324469 4191948232368719367780419)
                      ·
                        rfl

theorem cell23_8163790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_8163790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163790 prefixEnd_8163790 := by exact prefixLift 8163790
  have htrace : WordTrace (prefixWord ++ tailWord_8163790) baseStart_8163790 baseEnd_8163790 := by
    simpa [prefixWord, tailWord_8163790, baseEnd_8163790] using wordTrace_append hprefix tailTrace_8163790
  have hstable : (prefixWord ++ tailWord_8163790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163790).length < 2 ^ (prefixWord ++ tailWord_8163790).sum := by decide
  have hdescent : baseEnd_8163790 < baseStart_8163790 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163797 : List Nat := [1, 3, 2, 3, 1, 3, 1, 1, 4, 4]
def baseStart_8163797 : Nat := 118140960795 + 8163797 * 2 ^ 59
def prefixEnd_8163797 : Nat := 4983230072969 + 3 ^ 40 * 8163797 * 2
def baseEnd_8163797 : Nat := 1397317275577766946797629

theorem tailTrace_8163797 : CollatzResearch.WordTrace tailWord_8163797 prefixEnd_8163797 1397317275577766946797629 := by
  unfold tailWord_8163797
  simp only [CollatzResearch.WordTrace]
  refine ⟨297758138404965209369561645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198505425603310139579707763 297758138404965209369561645)
  ·
    refine ⟨111659301901861953513585617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297758138404965209369561645 111659301901861953513585617)
    ·
      refine ⟨83744476426396465135189213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111659301901861953513585617 83744476426396465135189213)
      ·
        refine ⟨31404178659898674425695955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83744476426396465135189213 31404178659898674425695955)
        ·
          refine ⟨47106267989848011638543933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31404178659898674425695955 47106267989848011638543933)
          ·
            refine ⟨17664850496193004364453975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47106267989848011638543933 17664850496193004364453975)
            ·
              refine ⟨26497275744289506546680963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17664850496193004364453975 26497275744289506546680963)
              ·
                refine ⟨39745913616434259820021445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26497275744289506546680963 39745913616434259820021445)
                ·
                  refine ⟨7452358803081423716254021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39745913616434259820021445 7452358803081423716254021)
                  ·
                    refine ⟨1397317275577766946797629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7452358803081423716254021 1397317275577766946797629)
                    ·
                      rfl

theorem cell23_8163797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_8163797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163797 prefixEnd_8163797 := by exact prefixLift 8163797
  have htrace : WordTrace (prefixWord ++ tailWord_8163797) baseStart_8163797 baseEnd_8163797 := by
    simpa [prefixWord, tailWord_8163797, baseEnd_8163797] using wordTrace_append hprefix tailTrace_8163797
  have hstable : (prefixWord ++ tailWord_8163797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163797).length < 2 ^ (prefixWord ++ tailWord_8163797).sum := by decide
  have hdescent : baseEnd_8163797 < baseStart_8163797 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163821 : List Nat := [1, 5, 1, 3, 1, 1, 2, 2, 3, 2, 2]
def baseStart_8163821 : Nat := 118140960795 + 8163821 * 2 ^ 59
def prefixEnd_8163821 : Nat := 4983230072969 + 3 ^ 40 * 8163821 * 2
def baseEnd_8163821 : Nat := 4191964150269008746492777

theorem tailTrace_8163821 : CollatzResearch.WordTrace tailWord_8163821 prefixEnd_8163821 4191964150269008746492777 := by
  unfold tailWord_8163821
  simp only [CollatzResearch.WordTrace]
  refine ⟨297759013756878261468435317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198506009171252174312290211 297759013756878261468435317)
  ·
    refine ⟨27914907539707337012665811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 297759013756878261468435317 27914907539707337012665811)
    ·
      refine ⟨41872361309561005518998717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27914907539707337012665811 41872361309561005518998717)
      ·
        refine ⟨15702135491085377069624519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41872361309561005518998717 15702135491085377069624519)
        ·
          refine ⟨23553203236628065604436779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15702135491085377069624519 23553203236628065604436779)
          ·
            refine ⟨35329804854942098406655169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23553203236628065604436779 35329804854942098406655169)
            ·
              refine ⟨26497353641206573804991377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35329804854942098406655169 26497353641206573804991377)
              ·
                refine ⟨19873015230904930353743533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26497353641206573804991377 19873015230904930353743533)
                ·
                  refine ⟨7452380711589348882653825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19873015230904930353743533 7452380711589348882653825)
                  ·
                    refine ⟨5589285533692011661990369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7452380711589348882653825 5589285533692011661990369)
                    ·
                      refine ⟨4191964150269008746492777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5589285533692011661990369 4191964150269008746492777)
                      ·
                        rfl

theorem cell23_8163821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_8163821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163821 prefixEnd_8163821 := by exact prefixLift 8163821
  have htrace : WordTrace (prefixWord ++ tailWord_8163821) baseStart_8163821 baseEnd_8163821 := by
    simpa [prefixWord, tailWord_8163821, baseEnd_8163821] using wordTrace_append hprefix tailTrace_8163821
  have hstable : (prefixWord ++ tailWord_8163821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163821).length < 2 ^ (prefixWord ++ tailWord_8163821).sum := by decide
  have hdescent : baseEnd_8163821 < baseStart_8163821 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163837 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 6, 1, 3]
def baseStart_8163837 : Nat := 118140960795 + 8163837 * 2 ^ 59
def prefixEnd_8163837 : Nat := 4983230072969 + 3 ^ 40 * 8163837 * 2
def baseEnd_8163837 : Nat := 4191972365959480683892703

theorem tailTrace_8163837 : CollatzResearch.WordTrace tailWord_8163837 prefixEnd_8163837 4191972365959480683892703 := by
  unfold tailWord_8163837
  simp only [CollatzResearch.WordTrace]
  refine ⟨297759597324820296201017765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198506398216546864134011843 297759597324820296201017765)
  ·
    refine ⟨55829924498403805537690831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297759597324820296201017765 55829924498403805537690831)
    ·
      refine ⟨83744886747605708306536247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55829924498403805537690831 83744886747605708306536247)
      ·
        refine ⟨125617330121408562459804371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83744886747605708306536247 125617330121408562459804371)
        ·
          refine ⟨188425995182112843689706557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125617330121408562459804371 188425995182112843689706557)
          ·
            refine ⟨70659748193292316383639959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188425995182112843689706557 70659748193292316383639959)
            ·
              refine ⟨105989622289938474575459939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70659748193292316383639959 105989622289938474575459939)
              ·
                refine ⟨158984433434907711863189909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105989622289938474575459939 158984433434907711863189909)
                ·
                  refine ⟨7452395317261298993587027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158984433434907711863189909 7452395317261298993587027)
                  ·
                    refine ⟨11178592975891948490380541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7452395317261298993587027 11178592975891948490380541)
                    ·
                      refine ⟨4191972365959480683892703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11178592975891948490380541 4191972365959480683892703)
                      ·
                        rfl

theorem cell23_8163837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_8163837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163837 prefixEnd_8163837 := by exact prefixLift 8163837
  have htrace : WordTrace (prefixWord ++ tailWord_8163837) baseStart_8163837 baseEnd_8163837 := by
    simpa [prefixWord, tailWord_8163837, baseEnd_8163837] using wordTrace_append hprefix tailTrace_8163837
  have hstable : (prefixWord ++ tailWord_8163837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163837).length < 2 ^ (prefixWord ++ tailWord_8163837).sum := by decide
  have hdescent : baseEnd_8163837 < baseStart_8163837 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163850 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 2, 2, 5]
def baseStart_8163850 : Nat := 118140960795 + 8163850 * 2 ^ 59
def prefixEnd_8163850 : Nat := 4983230072969 + 3 ^ 40 * 8163850 * 2
def baseEnd_8163850 : Nat := 4191979041207989133030143

theorem tailTrace_8163850 : CollatzResearch.WordTrace tailWord_8163850 prefixEnd_8163850 4191979041207989133030143 := by
  unfold tailWord_8163850
  simp only [CollatzResearch.WordTrace]
  refine ⟨74440017868443299855310251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198506714315848799614160669 74440017868443299855310251)
  ·
    refine ⟨111660026802664949782965377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74440017868443299855310251 111660026802664949782965377)
    ·
      refine ⟨83745020101998712337224033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111660026802664949782965377 83745020101998712337224033)
      ·
        refine ⟨62808765076499034252918025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83745020101998712337224033 62808765076499034252918025)
        ·
          refine ⟨47106573807374275689688519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62808765076499034252918025 47106573807374275689688519)
          ·
            refine ⟨70659860711061413534532779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47106573807374275689688519 70659860711061413534532779)
            ·
              refine ⟨105989791066592120301799169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70659860711061413534532779 105989791066592120301799169)
              ·
                refine ⟨79492343299944090226349377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105989791066592120301799169 79492343299944090226349377)
                ·
                  refine ⟨59619257474958067669762033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79492343299944090226349377 59619257474958067669762033)
                  ·
                    refine ⟨44714443106218550752321525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59619257474958067669762033 44714443106218550752321525)
                    ·
                      refine ⟨4191979041207989133030143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44714443106218550752321525 4191979041207989133030143)
                      ·
                        rfl

theorem cell23_8163850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_8163850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163850 prefixEnd_8163850 := by exact prefixLift 8163850
  have htrace : WordTrace (prefixWord ++ tailWord_8163850) baseStart_8163850 baseEnd_8163850 := by
    simpa [prefixWord, tailWord_8163850, baseEnd_8163850] using wordTrace_append hprefix tailTrace_8163850
  have hstable : (prefixWord ++ tailWord_8163850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163850).length < 2 ^ (prefixWord ++ tailWord_8163850).sum := by decide
  have hdescent : baseEnd_8163850 < baseStart_8163850 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163854 : List Nat := [4, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3]
def baseStart_8163854 : Nat := 118140960795 + 8163854 * 2 ^ 59
def prefixEnd_8163854 : Nat := 4983230072969 + 3 ^ 40 * 8163854 * 2
def baseEnd_8163854 : Nat := 4191981095130607117380125

theorem tailTrace_8163854 : CollatzResearch.WordTrace tailWord_8163854 prefixEnd_8163854 4191981095130607117380125 := by
  unfold tailWord_8163854
  simp only [CollatzResearch.WordTrace]
  refine ⟨37220027170719838513048327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198506811577172472069591077 37220027170719838513048327)
  ·
    refine ⟨55830040756079757769572491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37220027170719838513048327 55830040756079757769572491)
    ·
      refine ⟨83745061134119636654358737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55830040756079757769572491 83745061134119636654358737)
      ·
        refine ⟨62808795850589727490769053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83745061134119636654358737 62808795850589727490769053)
        ·
          refine ⟨23553298443971147809038395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62808795850589727490769053 23553298443971147809038395)
          ·
            refine ⟨35329947665956721713557593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23553298443971147809038395 35329947665956721713557593)
            ·
              refine ⟨26497460749467541285168195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35329947665956721713557593 26497460749467541285168195)
              ·
                refine ⟨39746191124201311927752293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26497460749467541285168195 39746191124201311927752293)
                ·
                  refine ⟨7452410835787745986453555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39746191124201311927752293 7452410835787745986453555)
                  ·
                    refine ⟨11178616253681618979680333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7452410835787745986453555 11178616253681618979680333)
                    ·
                      refine ⟨4191981095130607117380125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11178616253681618979680333 4191981095130607117380125)
                      ·
                        rfl

theorem cell23_8163854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_8163854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163854 prefixEnd_8163854 := by exact prefixLift 8163854
  have htrace : WordTrace (prefixWord ++ tailWord_8163854) baseStart_8163854 baseEnd_8163854 := by
    simpa [prefixWord, tailWord_8163854, baseEnd_8163854] using wordTrace_append hprefix tailTrace_8163854
  have hstable : (prefixWord ++ tailWord_8163854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163854).length < 2 ^ (prefixWord ++ tailWord_8163854).sum := by decide
  have hdescent : baseEnd_8163854 < baseStart_8163854 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163911 : List Nat := [1, 1, 4, 1, 4, 1, 1, 4, 2, 2, 2]
def baseStart_8163911 : Nat := 118140960795 + 8163911 * 2 ^ 59
def prefixEnd_8163911 : Nat := 4983230072969 + 3 ^ 40 * 8163911 * 2
def baseEnd_8163911 : Nat := 4192010363527913394367363

theorem tailTrace_8163911 : CollatzResearch.WordTrace tailWord_8163911 prefixEnd_8163911 4192010363527913394367363 := by
  unfold tailWord_8163911
  simp only [CollatzResearch.WordTrace]
  refine ⟨297762296326552206839211587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198508197551034804559474391 297762296326552206839211587)
  ·
    refine ⟨446643444489828310258817381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297762296326552206839211587 446643444489828310258817381)
    ·
      refine ⟨83745645841842808173528259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 446643444489828310258817381 83745645841842808173528259)
      ·
        refine ⟨125618468762764212260292389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83745645841842808173528259 125618468762764212260292389)
        ·
          refine ⟨23553462893018289798804823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125618468762764212260292389 23553462893018289798804823)
          ·
            refine ⟨35330194339527434698207235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23553462893018289798804823 35330194339527434698207235)
            ·
              refine ⟨52995291509291152047310853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35330194339527434698207235 52995291509291152047310853)
              ·
                refine ⟨9936617157992091008870785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52995291509291152047310853 9936617157992091008870785)
                ·
                  refine ⟨7452462868494068256653089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9936617157992091008870785 7452462868494068256653089)
                  ·
                    refine ⟨5589347151370551192489817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7452462868494068256653089 5589347151370551192489817)
                    ·
                      refine ⟨4192010363527913394367363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5589347151370551192489817 4192010363527913394367363)
                      ·
                        rfl

theorem cell23_8163911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2, 2, 2].length) (baseStart_8163911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163911 prefixEnd_8163911 := by exact prefixLift 8163911
  have htrace : WordTrace (prefixWord ++ tailWord_8163911) baseStart_8163911 baseEnd_8163911 := by
    simpa [prefixWord, tailWord_8163911, baseEnd_8163911] using wordTrace_append hprefix tailTrace_8163911
  have hstable : (prefixWord ++ tailWord_8163911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163911).length < 2 ^ (prefixWord ++ tailWord_8163911).sum := by decide
  have hdescent : baseEnd_8163911 < baseStart_8163911 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163927 : List Nat := [1, 1, 3, 2, 2, 2, 3, 1, 2, 3, 3]
def baseStart_8163927 : Nat := 118140960795 + 8163927 * 2 ^ 59
def prefixEnd_8163927 : Nat := 4983230072969 + 3 ^ 40 * 8163927 * 2
def baseEnd_8163927 : Nat := 4192018579218385331767289

theorem tailTrace_8163927 : CollatzResearch.WordTrace tailWord_8163927 prefixEnd_8163927 4192018579218385331767289 := by
  unfold tailWord_8163927
  simp only [CollatzResearch.WordTrace]
  refine ⟨297762879894494241571794035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198508586596329494381196023 297762879894494241571794035)
  ·
    refine ⟨446644319841741362357691053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297762879894494241571794035 446644319841741362357691053)
    ·
      refine ⟨167491619940653010884134145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446644319841741362357691053 167491619940653010884134145)
      ·
        refine ⟨125618714955489758163100609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167491619940653010884134145 125618714955489758163100609)
        ·
          refine ⟨94214036216617318622325457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125618714955489758163100609 94214036216617318622325457)
          ·
            refine ⟨70660527162462988966744093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94214036216617318622325457 70660527162462988966744093)
            ·
              refine ⟨26497697685923620862529035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70660527162462988966744093 26497697685923620862529035)
              ·
                refine ⟨39746546528885431293793553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26497697685923620862529035 39746546528885431293793553)
                ·
                  refine ⟨29809909896664073470345165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39746546528885431293793553 29809909896664073470345165)
                  ·
                    refine ⟨11178716211249027551379437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29809909896664073470345165 11178716211249027551379437)
                    ·
                      refine ⟨4192018579218385331767289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11178716211249027551379437 4192018579218385331767289)
                      ·
                        rfl

theorem cell23_8163927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_8163927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163927 prefixEnd_8163927 := by exact prefixLift 8163927
  have htrace : WordTrace (prefixWord ++ tailWord_8163927) baseStart_8163927 baseEnd_8163927 := by
    simpa [prefixWord, tailWord_8163927, baseEnd_8163927] using wordTrace_append hprefix tailTrace_8163927
  have hstable : (prefixWord ++ tailWord_8163927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163927).length < 2 ^ (prefixWord ++ tailWord_8163927).sum := by decide
  have hdescent : baseEnd_8163927 < baseStart_8163927 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8163987 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 4, 2, 3]
def baseStart_8163987 : Nat := 118140960795 + 8163987 * 2 ^ 59
def prefixEnd_8163987 : Nat := 4983230072969 + 3 ^ 40 * 8163987 * 2
def baseEnd_8163987 : Nat := 4192049388057655097017013

theorem tailTrace_8163987 : CollatzResearch.WordTrace tailWord_8163987 prefixEnd_8163987 4192049388057655097017013 := by
  unfold tailWord_8163987
  simp only [CollatzResearch.WordTrace]
  refine ⟨297765068274276871818978215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198510045516184581212652143 297765068274276871818978215)
  ·
    refine ⟨446647602411415307728467323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297765068274276871818978215 446647602411415307728467323)
    ·
      refine ⟨669971403617122961592700985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446647602411415307728467323 669971403617122961592700985)
      ·
        refine ⟨502478552712842221194525739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 669971403617122961592700985 502478552712842221194525739)
        ·
          refine ⟨753717829069263331791788609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502478552712842221194525739 753717829069263331791788609)
          ·
            refine ⟨565288371801947498843841457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 753717829069263331791788609 565288371801947498843841457)
            ·
              refine ⟨423966278851460624132881093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 565288371801947498843841457 423966278851460624132881093)
              ·
                refine ⟨79493677284648867024915205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 423966278851460624132881093 79493677284648867024915205)
                ·
                  refine ⟨14905064490871662567171601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79493677284648867024915205 14905064490871662567171601)
                  ·
                    refine ⟨11178798368153746925378701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14905064490871662567171601 11178798368153746925378701)
                    ·
                      refine ⟨4192049388057655097017013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11178798368153746925378701 4192049388057655097017013)
                      ·
                        rfl

theorem cell23_8163987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2, 3].length) (baseStart_8163987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8163987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8163987 prefixEnd_8163987 := by exact prefixLift 8163987
  have htrace : WordTrace (prefixWord ++ tailWord_8163987) baseStart_8163987 baseEnd_8163987 := by
    simpa [prefixWord, tailWord_8163987, baseEnd_8163987] using wordTrace_append hprefix tailTrace_8163987
  have hstable : (prefixWord ++ tailWord_8163987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8163987).length < 2 ^ (prefixWord ++ tailWord_8163987).sum := by decide
  have hdescent : baseEnd_8163987 < baseStart_8163987 := by decide
  rcases family_descends (prefixWord ++ tailWord_8163987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164004 : List Nat := [2, 3, 1, 2, 2, 1, 2, 3, 2, 2, 3]
def baseStart_8164004 : Nat := 118140960795 + 8164004 * 2 ^ 59
def prefixEnd_8164004 : Nat := 4983230072969 + 3 ^ 40 * 8164004 * 2
def baseEnd_8164004 : Nat := 4192058117228781530504435

theorem tailTrace_8164004 : CollatzResearch.WordTrace tailWord_8164004 prefixEnd_8164004 4192058117228781530504435 := by
  unfold tailWord_8164004
  simp only [CollatzResearch.WordTrace]
  refine ⟨148882844157607641861173533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198510458876810189148231377 148882844157607641861173533)
  ·
    refine ⟨55831066559102865697940075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148882844157607641861173533 55831066559102865697940075)
    ·
      refine ⟨83746599838654298546910113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55831066559102865697940075 83746599838654298546910113)
      ·
        refine ⟨62809949878990723910182585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83746599838654298546910113 62809949878990723910182585)
        ·
          refine ⟨47107462409243042932636939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62809949878990723910182585 47107462409243042932636939)
          ·
            refine ⟨70661193613864564398955409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47107462409243042932636939 70661193613864564398955409)
            ·
              refine ⟨52995895210398423299216557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70661193613864564398955409 52995895210398423299216557)
              ·
                refine ⟨19873460703899408737206209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52995895210398423299216557 19873460703899408737206209)
                ·
                  refine ⟨14905095527924556552904657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19873460703899408737206209 14905095527924556552904657)
                  ·
                    refine ⟨11178821645943417414678493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14905095527924556552904657 11178821645943417414678493)
                    ·
                      refine ⟨4192058117228781530504435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11178821645943417414678493 4192058117228781530504435)
                      ·
                        rfl

theorem cell23_8164004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_8164004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164004 prefixEnd_8164004 := by exact prefixLift 8164004
  have htrace : WordTrace (prefixWord ++ tailWord_8164004) baseStart_8164004 baseEnd_8164004 := by
    simpa [prefixWord, tailWord_8164004, baseEnd_8164004] using wordTrace_append hprefix tailTrace_8164004
  have hstable : (prefixWord ++ tailWord_8164004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164004).length < 2 ^ (prefixWord ++ tailWord_8164004).sum := by decide
  have hdescent : baseEnd_8164004 < baseStart_8164004 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164021 : List Nat := [1, 3, 3, 3, 1, 2, 1, 2, 2, 2, 3]
def baseStart_8164021 : Nat := 118140960795 + 8164021 * 2 ^ 59
def prefixEnd_8164021 : Nat := 4983230072969 + 3 ^ 40 * 8164021 * 2
def baseEnd_8164021 : Nat := 4192066846399907963991857

theorem tailTrace_8164021 : CollatzResearch.WordTrace tailWord_8164021 prefixEnd_8164021 4192066846399907963991857 := by
  unfold tailWord_8164021
  simp only [CollatzResearch.WordTrace]
  refine ⟨297766308356153695625715917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198510872237435797083810611 297766308356153695625715917)
  ·
    refine ⟨111662365633557635859643469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297766308356153695625715917 111662365633557635859643469)
    ·
      refine ⟨41873387112584113447366301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111662365633557635859643469 41873387112584113447366301)
      ·
        refine ⟨15702520167219042542762363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41873387112584113447366301 15702520167219042542762363)
        ·
          refine ⟨23553780250828563814143545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15702520167219042542762363 23553780250828563814143545)
          ·
            refine ⟨17665335188121422860607659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23553780250828563814143545 17665335188121422860607659)
            ·
              refine ⟨26498002782182134290911489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17665335188121422860607659 26498002782182134290911489)
              ·
                refine ⟨19873502086636600718183617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26498002782182134290911489 19873502086636600718183617)
                ·
                  refine ⟨14905126564977450538637713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19873502086636600718183617 14905126564977450538637713)
                  ·
                    refine ⟨11178844923733087903978285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14905126564977450538637713 11178844923733087903978285)
                    ·
                      refine ⟨4192066846399907963991857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11178844923733087903978285 4192066846399907963991857)
                      ·
                        rfl

theorem cell23_8164021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_8164021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164021 prefixEnd_8164021 := by exact prefixLift 8164021
  have htrace : WordTrace (prefixWord ++ tailWord_8164021) baseStart_8164021 baseEnd_8164021 := by
    simpa [prefixWord, tailWord_8164021, baseEnd_8164021] using wordTrace_append hprefix tailTrace_8164021
  have hstable : (prefixWord ++ tailWord_8164021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164021).length < 2 ^ (prefixWord ++ tailWord_8164021).sum := by decide
  have hdescent : baseEnd_8164021 < baseStart_8164021 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164028 : List Nat := [2, 2, 2, 3, 1, 1, 5, 2, 1, 4]
def baseStart_8164028 : Nat := 118140960795 + 8164028 * 2 ^ 59
def prefixEnd_8164028 : Nat := 4983230072969 + 3 ^ 40 * 8164028 * 2
def baseEnd_8164028 : Nat := 1397356813588163145534775

theorem tailTrace_8164028 : CollatzResearch.WordTrace tailWord_8164028 prefixEnd_8164028 1397356813588163145534775 := by
  unfold tailWord_8164028
  simp only [CollatzResearch.WordTrace]
  refine ⟨148883281833564167910610369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198511042444752223880813825 148883281833564167910610369)
  ·
    refine ⟨111662461375173125932957777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148883281833564167910610369 111662461375173125932957777)
    ·
      refine ⟨83746846031379844449718333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111662461375173125932957777 83746846031379844449718333)
      ·
        refine ⟨31405067261767441668644375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83746846031379844449718333 31405067261767441668644375)
        ·
          refine ⟨47107600892651162502966563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31405067261767441668644375 47107600892651162502966563)
          ·
            refine ⟨70661401338976743754449845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47107600892651162502966563 70661401338976743754449845)
            ·
              refine ⟨6624506375529069726979673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70661401338976743754449845 6624506375529069726979673)
              ·
                refine ⟨4968379781646802295234755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6624506375529069726979673 4968379781646802295234755)
                ·
                  refine ⟨7452569672470203442852133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4968379781646802295234755 7452569672470203442852133)
                  ·
                    refine ⟨1397356813588163145534775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7452569672470203442852133 1397356813588163145534775)
                    ·
                      rfl

theorem cell23_8164028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_8164028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164028 prefixEnd_8164028 := by exact prefixLift 8164028
  have htrace : WordTrace (prefixWord ++ tailWord_8164028) baseStart_8164028 baseEnd_8164028 := by
    simpa [prefixWord, tailWord_8164028, baseEnd_8164028] using wordTrace_append hprefix tailTrace_8164028
  have hstable : (prefixWord ++ tailWord_8164028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164028).length < 2 ^ (prefixWord ++ tailWord_8164028).sum := by decide
  have hdescent : baseEnd_8164028 < baseStart_8164028 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164087 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 4]
def baseStart_8164087 : Nat := 118140960795 + 8164087 * 2 ^ 59
def prefixEnd_8164087 : Nat := 4983230072969 + 3 ^ 40 * 8164087 * 2
def baseEnd_8164087 : Nat := 4192100736123104705766553

theorem tailTrace_8164087 : CollatzResearch.WordTrace tailWord_8164087 prefixEnd_8164087 4192100736123104705766553 := by
  unfold tailWord_8164087
  simp only [CollatzResearch.WordTrace]
  refine ⟨297768715573914588897618515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198512477049276392598412343 297768715573914588897618515)
  ·
    refine ⟨446653073360871883346427773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297768715573914588897618515 446653073360871883346427773)
    ·
      refine ⟨167494902510326956254910415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446653073360871883346427773 167494902510326956254910415)
      ·
        refine ⟨251242353765490434382365623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167494902510326956254910415 251242353765490434382365623)
        ·
          refine ⟨376863530648235651573548435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251242353765490434382365623 376863530648235651573548435)
          ·
            refine ⟨565295295972353477360322653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376863530648235651573548435 565295295972353477360322653)
            ·
              refine ⟨211985735989632554010120995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 565295295972353477360322653 211985735989632554010120995)
              ·
                refine ⟨317978603984448831015181493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211985735989632554010120995 317978603984448831015181493)
                ·
                  refine ⟨29810494123542077907673265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 317978603984448831015181493 29810494123542077907673265)
                  ·
                    refine ⟨22357870592656558430754949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29810494123542077907673265 22357870592656558430754949)
                    ·
                      refine ⟨4192100736123104705766553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22357870592656558430754949 4192100736123104705766553)
                      ·
                        rfl

theorem cell23_8164087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_8164087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164087 prefixEnd_8164087 := by exact prefixLift 8164087
  have htrace : WordTrace (prefixWord ++ tailWord_8164087) baseStart_8164087 baseEnd_8164087 := by
    simpa [prefixWord, tailWord_8164087, baseEnd_8164087] using wordTrace_append hprefix tailTrace_8164087
  have hstable : (prefixWord ++ tailWord_8164087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164087).length < 2 ^ (prefixWord ++ tailWord_8164087).sum := by decide
  have hdescent : baseEnd_8164087 < baseStart_8164087 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164104 : List Nat := [2, 1, 3, 2, 2, 2, 1, 3, 1, 2, 4]
def baseStart_8164104 : Nat := 118140960795 + 8164104 * 2 ^ 59
def prefixEnd_8164104 : Nat := 4983230072969 + 3 ^ 40 * 8164104 * 2
def baseEnd_8164104 : Nat := 4192109465294231139253975

theorem tailTrace_8164104 : CollatzResearch.WordTrace tailWord_8164104 prefixEnd_8164104 4192109465294231139253975 := by
  unfold tailWord_8164104
  simp only [CollatzResearch.WordTrace]
  refine ⟨148884667807426500400493683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198512890409902000533991577 148884667807426500400493683)
  ·
    refine ⟨223327001711139750600740525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148884667807426500400493683 223327001711139750600740525)
    ·
      refine ⟨83747625641677406475277697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223327001711139750600740525 83747625641677406475277697)
      ·
        refine ⟨62810719231258054856458273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83747625641677406475277697 62810719231258054856458273)
        ·
          refine ⟨47108039423443541142343705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62810719231258054856458273 47108039423443541142343705)
          ·
            refine ⟨35331029567582655856757779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47108039423443541142343705 35331029567582655856757779)
            ·
              refine ⟨52996544351373983785136669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35331029567582655856757779 52996544351373983785136669)
              ·
                refine ⟨19873704131765243919426251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52996544351373983785136669 19873704131765243919426251)
                ·
                  refine ⟨29810556197647865879139377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19873704131765243919426251 29810556197647865879139377)
                  ·
                    refine ⟨22357917148235899409354533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29810556197647865879139377 22357917148235899409354533)
                    ·
                      refine ⟨4192109465294231139253975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22357917148235899409354533 4192109465294231139253975)
                      ·
                        rfl

theorem cell23_8164104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_8164104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164104 prefixEnd_8164104 := by exact prefixLift 8164104
  have htrace : WordTrace (prefixWord ++ tailWord_8164104) baseStart_8164104 baseEnd_8164104 := by
    simpa [prefixWord, tailWord_8164104, baseEnd_8164104] using wordTrace_append hprefix tailTrace_8164104
  have hstable : (prefixWord ++ tailWord_8164104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164104).length < 2 ^ (prefixWord ++ tailWord_8164104).sum := by decide
  have hdescent : baseEnd_8164104 < baseStart_8164104 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164128 : List Nat := [2, 1, 1, 5, 1, 2, 4, 1, 1, 2, 3]
def baseStart_8164128 : Nat := 118140960795 + 8164128 * 2 ^ 59
def prefixEnd_8164128 : Nat := 4983230072969 + 3 ^ 40 * 8164128 * 2
def baseEnd_8164128 : Nat := 4192121788829939045353865

theorem tailTrace_8164128 : CollatzResearch.WordTrace tailWord_8164128 prefixEnd_8164128 4192121788829939045353865 := by
  unfold tailWord_8164128
  simp only [CollatzResearch.WordTrace]
  refine ⟨148885105483383026449930519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198513473977844035266574025 148885105483383026449930519)
  ·
    refine ⟨223327658225074539674895779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148885105483383026449930519 223327658225074539674895779)
    ·
      refine ⟨334991487337611809512343669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223327658225074539674895779 334991487337611809512343669)
      ·
        refine ⟨31405451937901107141782219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 334991487337611809512343669 31405451937901107141782219)
        ·
          refine ⟨47108177906851660712673329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31405451937901107141782219 47108177906851660712673329)
          ·
            refine ⟨35331133430138745534504997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47108177906851660712673329 35331133430138745534504997)
            ·
              refine ⟨6624587518151014787719687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35331133430138745534504997 6624587518151014787719687)
              ·
                refine ⟨9936881277226522181579531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6624587518151014787719687 9936881277226522181579531)
                ·
                  refine ⟨14905321915839783272369297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9936881277226522181579531 14905321915839783272369297)
                  ·
                    refine ⟨11178991436879837454276973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14905321915839783272369297 11178991436879837454276973)
                    ·
                      refine ⟨4192121788829939045353865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11178991436879837454276973 4192121788829939045353865)
                      ·
                        rfl

theorem cell23_8164128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_8164128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164128 prefixEnd_8164128 := by exact prefixLift 8164128
  have htrace : WordTrace (prefixWord ++ tailWord_8164128) baseStart_8164128 baseEnd_8164128 := by
    simpa [prefixWord, tailWord_8164128, baseEnd_8164128] using wordTrace_append hprefix tailTrace_8164128
  have hstable : (prefixWord ++ tailWord_8164128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164128).length < 2 ^ (prefixWord ++ tailWord_8164128).sum := by decide
  have hdescent : baseEnd_8164128 < baseStart_8164128 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164137 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 2, 2, 5]
def baseStart_8164137 : Nat := 118140960795 + 8164137 * 2 ^ 59
def prefixEnd_8164137 : Nat := 4983230072969 + 3 ^ 40 * 8164137 * 2
def baseEnd_8164137 : Nat := 4192126410155829510141323

theorem tailTrace_8164137 : CollatzResearch.WordTrace tailWord_8164137 prefixEnd_8164137 4192126410155829510141323 := by
  unfold tailWord_8164137
  simp only [CollatzResearch.WordTrace]
  refine ⟨297770539223733447436938665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198513692815822298291292443 297770539223733447436938665)
  ·
    refine ⟨223327904417800085577703999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297770539223733447436938665 223327904417800085577703999)
    ·
      refine ⟨334991856626700128366555999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223327904417800085577703999 334991856626700128366555999)
      ·
        refine ⟨502487784940050192549833999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334991856626700128366555999 502487784940050192549833999)
        ·
          refine ⟨753731677410075288824750999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502487784940050192549833999 753731677410075288824750999)
          ·
            refine ⟨1130597516115112933237126499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753731677410075288824750999 1130597516115112933237126499)
            ·
              refine ⟨1695896274172669399855689749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130597516115112933237126499 1695896274172669399855689749)
              ·
                refine ⟨79495137851843878118235457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1695896274172669399855689749 79495137851843878118235457)
                ·
                  refine ⟨59621353388882908588676593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79495137851843878118235457 59621353388882908588676593)
                  ·
                    refine ⟨44716015041662181441507445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59621353388882908588676593 44716015041662181441507445)
                    ·
                      refine ⟨4192126410155829510141323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44716015041662181441507445 4192126410155829510141323)
                      ·
                        rfl

theorem cell23_8164137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 2, 5].length) (baseStart_8164137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164137 prefixEnd_8164137 := by exact prefixLift 8164137
  have htrace : WordTrace (prefixWord ++ tailWord_8164137) baseStart_8164137 baseEnd_8164137 := by
    simpa [prefixWord, tailWord_8164137, baseEnd_8164137] using wordTrace_append hprefix tailTrace_8164137
  have hstable : (prefixWord ++ tailWord_8164137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164137).length < 2 ^ (prefixWord ++ tailWord_8164137).sum := by decide
  have hdescent : baseEnd_8164137 < baseStart_8164137 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164142 : List Nat := [4, 1, 3, 2, 1, 1, 2, 4, 1, 2, 2]
def baseStart_8164142 : Nat := 118140960795 + 8164142 * 2 ^ 59
def prefixEnd_8164142 : Nat := 4983230072969 + 3 ^ 40 * 8164142 * 2
def baseEnd_8164142 : Nat := 4192128977559101990578801

theorem tailTrace_8164142 : CollatzResearch.WordTrace tailWord_8164142 prefixEnd_8164142 4192128977559101990578801 := by
  unfold tailWord_8164142
  simp only [CollatzResearch.WordTrace]
  refine ⟨37221340198589416661358835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198513814392476888860580453 37221340198589416661358835)
  ·
    refine ⟨55832010297884124992038253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37221340198589416661358835 55832010297884124992038253)
    ·
      refine ⟨20937003861706546872014345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55832010297884124992038253 20937003861706546872014345)
      ·
        refine ⟨15702752896279910154010759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20937003861706546872014345 15702752896279910154010759)
        ·
          refine ⟨23554129344419865231016139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15702752896279910154010759 23554129344419865231016139)
          ·
            refine ⟨35331194016629797846524209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23554129344419865231016139 35331194016629797846524209)
            ·
              refine ⟨26498395512472348384893157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35331194016629797846524209 26498395512472348384893157)
              ·
                refine ⟨4968449158588565322167467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26498395512472348384893157 4968449158588565322167467)
                ·
                  refine ⟨7452673737882847983251201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4968449158588565322167467 7452673737882847983251201)
                  ·
                    refine ⟨5589505303412135987438401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7452673737882847983251201 5589505303412135987438401)
                    ·
                      refine ⟨4192128977559101990578801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5589505303412135987438401 4192128977559101990578801)
                      ·
                        rfl

theorem cell23_8164142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_8164142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164142 prefixEnd_8164142 := by exact prefixLift 8164142
  have htrace : WordTrace (prefixWord ++ tailWord_8164142) baseStart_8164142 baseEnd_8164142 := by
    simpa [prefixWord, tailWord_8164142, baseEnd_8164142] using wordTrace_append hprefix tailTrace_8164142
  have hstable : (prefixWord ++ tailWord_8164142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164142).length < 2 ^ (prefixWord ++ tailWord_8164142).sum := by decide
  have hdescent : baseEnd_8164142 < baseStart_8164142 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164168 : List Nat := [2, 1, 3, 1, 1, 3, 4, 2, 1, 3, 2]
def baseStart_8164168 : Nat := 118140960795 + 8164168 * 2 ^ 59
def prefixEnd_8164168 : Nat := 4983230072969 + 3 ^ 40 * 8164168 * 2
def baseEnd_8164168 : Nat := 4192142328056118888853681

theorem tailTrace_8164168 : CollatzResearch.WordTrace tailWord_8164168 prefixEnd_8164168 4192142328056118888853681 := by
  unfold tailWord_8164168
  simp only [CollatzResearch.WordTrace]
  refine ⟨148885834943310569865658579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198514446591080759820878105 148885834943310569865658579)
  ·
    refine ⟨223328752414965854798487869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148885834943310569865658579 223328752414965854798487869)
    ·
      refine ⟨83748282155612195549432951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223328752414965854798487869 83748282155612195549432951)
      ·
        refine ⟨125622423233418293324149427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83748282155612195549432951 125622423233418293324149427)
        ·
          refine ⟨188433634850127439986224141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125622423233418293324149427 188433634850127439986224141)
          ·
            refine ⟨70662613068797789994834053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188433634850127439986224141 70662613068797789994834053)
            ·
              refine ⟨13249239950399585624031385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70662613068797789994834053 13249239950399585624031385)
              ·
                refine ⟨9936929962799689218023539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13249239950399585624031385 9936929962799689218023539)
                ·
                  refine ⟨14905394944199533827035309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9936929962799689218023539 14905394944199533827035309)
                  ·
                    refine ⟨5589523104074825185138241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14905394944199533827035309 5589523104074825185138241)
                    ·
                      refine ⟨4192142328056118888853681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5589523104074825185138241 4192142328056118888853681)
                      ·
                        rfl

theorem cell23_8164168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 1, 3, 2].length) (baseStart_8164168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164168 prefixEnd_8164168 := by exact prefixLift 8164168
  have htrace : WordTrace (prefixWord ++ tailWord_8164168) baseStart_8164168 baseEnd_8164168 := by
    simpa [prefixWord, tailWord_8164168, baseEnd_8164168] using wordTrace_append hprefix tailTrace_8164168
  have hstable : (prefixWord ++ tailWord_8164168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164168).length < 2 ^ (prefixWord ++ tailWord_8164168).sum := by decide
  have hdescent : baseEnd_8164168 < baseStart_8164168 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164181 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 3, 4, 2]
def baseStart_8164181 : Nat := 118140960795 + 8164181 * 2 ^ 59
def prefixEnd_8164181 : Nat := 4983230072969 + 3 ^ 40 * 8164181 * 2
def baseEnd_8164181 : Nat := 4192149003304627337991121

theorem tailTrace_8164181 : CollatzResearch.WordTrace tailWord_8164181 prefixEnd_8164181 4192149003304627337991121 := by
  unfold tailWord_8164181
  simp only [CollatzResearch.WordTrace]
  refine ⟨297772144035574042951540397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198514762690382695301026931 297772144035574042951540397)
  ·
    refine ⟨111664554013340266106827649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297772144035574042951540397 111664554013340266106827649)
    ·
      refine ⟨83748415510005199580120737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111664554013340266106827649 83748415510005199580120737)
      ·
        refine ⟨62811311632503899685090553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83748415510005199580120737 62811311632503899685090553)
        ·
          refine ⟨47108483724377924763817915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62811311632503899685090553 47108483724377924763817915)
          ·
            refine ⟨70662725586566887145726873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47108483724377924763817915 70662725586566887145726873)
            ·
              refine ⟨52997044189925165359295155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70662725586566887145726873 52997044189925165359295155)
              ·
                refine ⟨79495566284887748038942733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52997044189925165359295155 79495566284887748038942733)
                ·
                  refine ⟨29810837356832905514603525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79495566284887748038942733 29810837356832905514603525)
                  ·
                    refine ⟨5589532004406169783988161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29810837356832905514603525 5589532004406169783988161)
                    ·
                      refine ⟨4192149003304627337991121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5589532004406169783988161 4192149003304627337991121)
                      ·
                        rfl

theorem cell23_8164181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_8164181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164181 prefixEnd_8164181 := by exact prefixLift 8164181
  have htrace : WordTrace (prefixWord ++ tailWord_8164181) baseStart_8164181 baseEnd_8164181 := by
    simpa [prefixWord, tailWord_8164181, baseEnd_8164181] using wordTrace_append hprefix tailTrace_8164181
  have hstable : (prefixWord ++ tailWord_8164181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164181).length < 2 ^ (prefixWord ++ tailWord_8164181).sum := by decide
  have hdescent : baseEnd_8164181 < baseStart_8164181 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164255 : List Nat := [1, 1, 2, 5, 2, 3, 2, 2, 5]
def baseStart_8164255 : Nat := 118140960795 + 8164255 * 2 ^ 59
def prefixEnd_8164255 : Nat := 4983230072969 + 3 ^ 40 * 8164255 * 2
def baseEnd_8164255 : Nat := 465798555652562227607309

theorem tailTrace_8164255 : CollatzResearch.WordTrace tailWord_8164255 prefixEnd_8164255 465798555652562227607309 := by
  unfold tailWord_8164255
  simp only [CollatzResearch.WordTrace]
  refine ⟨297774843037305953589734219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198516562024870635726489479 297774843037305953589734219)
  ·
    refine ⟨446662264555958930384601329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297774843037305953589734219 446662264555958930384601329)
    ·
      refine ⟨334996698416969197788450997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446662264555958930384601329 334996698416969197788450997)
      ·
        refine ⟨31405940476590862292667281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 334996698416969197788450997 31405940476590862292667281)
        ·
          refine ⟨23554455357443146719500461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31405940476590862292667281 23554455357443146719500461)
          ·
            refine ⟨8832920759041180019812673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23554455357443146719500461 8832920759041180019812673)
            ·
              refine ⟨6624690569280885014859505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8832920759041180019812673 6624690569280885014859505)
              ·
                refine ⟨4968517926960663761144629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6624690569280885014859505 4968517926960663761144629)
                ·
                  refine ⟨465798555652562227607309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4968517926960663761144629 465798555652562227607309)
                  ·
                    rfl

theorem cell23_8164255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2, 5].length) (baseStart_8164255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164255 prefixEnd_8164255 := by exact prefixLift 8164255
  have htrace : WordTrace (prefixWord ++ tailWord_8164255) baseStart_8164255 baseEnd_8164255 := by
    simpa [prefixWord, tailWord_8164255, baseEnd_8164255] using wordTrace_append hprefix tailTrace_8164255
  have hstable : (prefixWord ++ tailWord_8164255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164255).length < 2 ^ (prefixWord ++ tailWord_8164255).sum := by decide
  have hdescent : baseEnd_8164255 < baseStart_8164255 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164258 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 2, 5, 2]
def baseStart_8164258 : Nat := 118140960795 + 8164258 * 2 ^ 59
def prefixEnd_8164258 : Nat := 4983230072969 + 3 ^ 40 * 8164258 * 2
def baseEnd_8164258 : Nat := 4192188541315023536728267

theorem tailTrace_8164258 : CollatzResearch.WordTrace tailWord_8164258 prefixEnd_8164258 4192188541315023536728267 := by
  unfold tailWord_8164258
  simp only [CollatzResearch.WordTrace]
  refine ⟨74443738114073771275523357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198516634970863390068062285 74443738114073771275523357)
  ·
    refine ⟨27916401792777664228321259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74443738114073771275523357 27916401792777664228321259)
    ·
      refine ⟨41874602689166496342481889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27916401792777664228321259 41874602689166496342481889)
      ·
        refine ⟨31405952016874872256861417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41874602689166496342481889 31405952016874872256861417)
        ·
          refine ⟨23554464012656154192646063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31405952016874872256861417 23554464012656154192646063)
          ·
            refine ⟨35331696018984231288969095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23554464012656154192646063 35331696018984231288969095)
            ·
              refine ⟨52997544028476346933453643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35331696018984231288969095 52997544028476346933453643)
              ·
                refine ⟨79496316042714520400180465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52997544028476346933453643 79496316042714520400180465)
                ·
                  refine ⟨59622237032035890300135349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79496316042714520400180465 59622237032035890300135349)
                  ·
                    refine ⟨5589584721753364715637689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59622237032035890300135349 5589584721753364715637689)
                    ·
                      refine ⟨4192188541315023536728267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5589584721753364715637689 4192188541315023536728267)
                      ·
                        rfl

theorem cell23_8164258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_8164258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164258 prefixEnd_8164258 := by exact prefixLift 8164258
  have htrace : WordTrace (prefixWord ++ tailWord_8164258) baseStart_8164258 baseEnd_8164258 := by
    simpa [prefixWord, tailWord_8164258, baseEnd_8164258] using wordTrace_append hprefix tailTrace_8164258
  have hstable : (prefixWord ++ tailWord_8164258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164258).length < 2 ^ (prefixWord ++ tailWord_8164258).sum := by decide
  have hdescent : baseEnd_8164258 < baseStart_8164258 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164281 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 5, 4]
def baseStart_8164281 : Nat := 118140960795 + 8164281 * 2 ^ 59
def prefixEnd_8164281 : Nat := 4983230072969 + 3 ^ 40 * 8164281 * 2
def baseEnd_8164281 : Nat := 1397400117123358982246887

theorem tailTrace_8164281 : CollatzResearch.WordTrace tailWord_8164281 prefixEnd_8164281 1397400117123358982246887 := by
  unfold tailWord_8164281
  simp only [CollatzResearch.WordTrace]
  refine ⟨297775791335211760030180697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198517194223474506686787131 297775791335211760030180697)
  ·
    refine ⟨223331843501408820022635523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297775791335211760030180697 223331843501408820022635523)
    ·
      refine ⟨334997765252113230033953285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223331843501408820022635523 334997765252113230033953285)
      ·
        refine ⟨62812080984771230631366241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 334997765252113230033953285 62812080984771230631366241)
        ·
          refine ⟨47109060738578422973524681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62812080984771230631366241 47109060738578422973524681)
          ·
            refine ⟨35331795553933817230143511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47109060738578422973524681 35331795553933817230143511)
            ·
              refine ⟨52997693330900725845215267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35331795553933817230143511 52997693330900725845215267)
              ·
                refine ⟨79496539996351088767822901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52997693330900725845215267 79496539996351088767822901)
                ·
                  refine ⟨7452800624657914571983397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79496539996351088767822901 7452800624657914571983397)
                  ·
                    refine ⟨1397400117123358982246887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7452800624657914571983397 1397400117123358982246887)
                    ·
                      rfl

theorem cell23_8164281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5, 4].length) (baseStart_8164281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164281 prefixEnd_8164281 := by exact prefixLift 8164281
  have htrace : WordTrace (prefixWord ++ tailWord_8164281) baseStart_8164281 baseEnd_8164281 := by
    simpa [prefixWord, tailWord_8164281, baseEnd_8164281] using wordTrace_append hprefix tailTrace_8164281
  have hstable : (prefixWord ++ tailWord_8164281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164281).length < 2 ^ (prefixWord ++ tailWord_8164281).sum := by decide
  have hdescent : baseEnd_8164281 < baseStart_8164281 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164285 : List Nat := [1, 4, 1, 2, 5, 1, 1, 1, 2, 5]
def baseStart_8164285 : Nat := 118140960795 + 8164285 * 2 ^ 59
def prefixEnd_8164285 : Nat := 4983230072969 + 3 ^ 40 * 8164285 * 2
def baseEnd_8164285 : Nat := 1397400801764231643696881

theorem tailTrace_8164285 : CollatzResearch.WordTrace tailWord_8164285 prefixEnd_8164285 1397400801764231643696881 := by
  unfold tailWord_8164285
  simp only [CollatzResearch.WordTrace]
  refine ⟨297775937227197268713326309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198517291484798179142217539 297775937227197268713326309)
  ·
    refine ⟨55832988230099487883748683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297775937227197268713326309 55832988230099487883748683)
    ·
      refine ⟨83749482345149231825623025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55832988230099487883748683 83749482345149231825623025)
      ·
        refine ⟨62812111758861923869217269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83749482345149231825623025 62812111758861923869217269)
        ·
          refine ⟨5888635477393305362739119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62812111758861923869217269 5888635477393305362739119)
          ·
            refine ⟨8832953216089958044108679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5888635477393305362739119 8832953216089958044108679)
            ·
              refine ⟨13249429824134937066163019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8832953216089958044108679 13249429824134937066163019)
              ·
                refine ⟨19874144736202405599244529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13249429824134937066163019 19874144736202405599244529)
                ·
                  refine ⟨14905608552151804199433397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19874144736202405599244529 14905608552151804199433397)
                  ·
                    refine ⟨1397400801764231643696881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14905608552151804199433397 1397400801764231643696881)
                    ·
                      rfl

theorem cell23_8164285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_8164285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164285 prefixEnd_8164285 := by exact prefixLift 8164285
  have htrace : WordTrace (prefixWord ++ tailWord_8164285) baseStart_8164285 baseEnd_8164285 := by
    simpa [prefixWord, tailWord_8164285, baseEnd_8164285] using wordTrace_append hprefix tailTrace_8164285
  have hstable : (prefixWord ++ tailWord_8164285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164285).length < 2 ^ (prefixWord ++ tailWord_8164285).sum := by decide
  have hdescent : baseEnd_8164285 < baseStart_8164285 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164288 : List Nat := [2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 4]
def baseStart_8164288 : Nat := 118140960795 + 8164288 * 2 ^ 59
def prefixEnd_8164288 : Nat := 4983230072969 + 3 ^ 40 * 8164288 * 2
def baseEnd_8164288 : Nat := 4192203945734658419353129

theorem tailTrace_8164288 : CollatzResearch.WordTrace tailWord_8164288 prefixEnd_8164288 4192203945734658419353129 := by
  unfold tailWord_8164288
  simp only [CollatzResearch.WordTrace]
  refine ⟨148888023323093200112842759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198517364430790933483790345 148888023323093200112842759)
  ·
    refine ⟨223332034984639800169264139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148888023323093200112842759 223332034984639800169264139)
    ·
      refine ⟨334998052476959700253896209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223332034984639800169264139 334998052476959700253896209)
      ·
        refine ⟨251248539357719775190422157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334998052476959700253896209 251248539357719775190422157)
        ·
          refine ⟨94218202259144915696408309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251248539357719775190422157 94218202259144915696408309)
          ·
            refine ⟨8832956461794835846538279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94218202259144915696408309 8832956461794835846538279)
            ·
              refine ⟨13249434692692253769807419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8832956461794835846538279 13249434692692253769807419)
              ·
                refine ⟨19874152039038380654711129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13249434692692253769807419 19874152039038380654711129)
                ·
                  refine ⟨14905614029278785491033347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19874152039038380654711129 14905614029278785491033347)
                  ·
                    refine ⟨22358421043918178236550021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14905614029278785491033347 22358421043918178236550021)
                    ·
                      refine ⟨4192203945734658419353129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22358421043918178236550021 4192203945734658419353129)
                      ·
                        rfl

theorem cell23_8164288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 4].length) (baseStart_8164288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164288 prefixEnd_8164288 := by exact prefixLift 8164288
  have htrace : WordTrace (prefixWord ++ tailWord_8164288) baseStart_8164288 baseEnd_8164288 := by
    simpa [prefixWord, tailWord_8164288, baseEnd_8164288] using wordTrace_append hprefix tailTrace_8164288
  have hstable : (prefixWord ++ tailWord_8164288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164288).length < 2 ^ (prefixWord ++ tailWord_8164288).sum := by decide
  have hdescent : baseEnd_8164288 < baseStart_8164288 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164324 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 2, 9]
def baseStart_8164324 : Nat := 118140960795 + 8164324 * 2 ^ 59
def prefixEnd_8164324 : Nat := 4983230072969 + 3 ^ 40 * 8164324 * 2
def baseEnd_8164324 : Nat := 1397407477012740092834321

theorem tailTrace_8164324 : CollatzResearch.WordTrace tailWord_8164324 prefixEnd_8164324 1397407477012740092834321 := by
  unfold tailWord_8164324
  simp only [CollatzResearch.WordTrace]
  refine ⟨148888679837027989186998013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198518239782703985582664017 148888679837027989186998013)
  ·
    refine ⟨55833254938885495945124255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148888679837027989186998013 55833254938885495945124255)
    ·
      refine ⟨83749882408328243917686383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55833254938885495945124255 83749882408328243917686383)
      ·
        refine ⟨125624823612492365876529575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83749882408328243917686383 125624823612492365876529575)
        ·
          refine ⟨188437235418738548814794363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125624823612492365876529575 188437235418738548814794363)
          ·
            refine ⟨282655853128107823222191545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188437235418738548814794363 282655853128107823222191545)
            ·
              refine ⟨211991889846080867416643659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282655853128107823222191545 211991889846080867416643659)
              ·
                refine ⟨317987834769121301124965489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211991889846080867416643659 317987834769121301124965489)
                ·
                  refine ⟨238490876076840975843724117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317987834769121301124965489 238490876076840975843724117)
                  ·
                    refine ⟨1397407477012740092834321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 238490876076840975843724117 1397407477012740092834321)
                    ·
                      rfl

theorem cell23_8164324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_8164324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164324 prefixEnd_8164324 := by exact prefixLift 8164324
  have htrace : WordTrace (prefixWord ++ tailWord_8164324) baseStart_8164324 baseEnd_8164324 := by
    simpa [prefixWord, tailWord_8164324, baseEnd_8164324] using wordTrace_append hprefix tailTrace_8164324
  have hstable : (prefixWord ++ tailWord_8164324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164324).length < 2 ^ (prefixWord ++ tailWord_8164324).sum := by decide
  have hdescent : baseEnd_8164324 < baseStart_8164324 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164348 : List Nat := [2, 2, 2, 1, 2, 3, 2, 1, 1, 5, 2]
def baseStart_8164348 : Nat := 118140960795 + 8164348 * 2 ^ 59
def prefixEnd_8164348 : Nat := 4983230072969 + 3 ^ 40 * 8164348 * 2
def baseEnd_8164348 : Nat := 4192234754573928184602853

theorem tailTrace_8164348 : CollatzResearch.WordTrace tailWord_8164348 prefixEnd_8164348 4192234754573928184602853 := by
  unfold tailWord_8164348
  simp only [CollatzResearch.WordTrace]
  refine ⟨148889117512984515236434849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198518823350646020315246465 148889117512984515236434849)
  ·
    refine ⟨111666838134738386427326137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148889117512984515236434849 111666838134738386427326137)
    ·
      refine ⟨83750128601053789820494603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111666838134738386427326137 83750128601053789820494603)
      ·
        refine ⟨125625192901580684730741905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83750128601053789820494603 125625192901580684730741905)
        ·
          refine ⟨94218894676185513548056429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125625192901580684730741905 94218894676185513548056429)
          ·
            refine ⟨35332085503569567580521161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94218894676185513548056429 35332085503569567580521161)
            ·
              refine ⟨26499064127677175685390871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35332085503569567580521161 26499064127677175685390871)
              ·
                refine ⟨39748596191515763528086307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26499064127677175685390871 39748596191515763528086307)
                ·
                  refine ⟨59622894287273645292129461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39748596191515763528086307 59622894287273645292129461)
                  ·
                    refine ⟨5589646339431904246137137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59622894287273645292129461 5589646339431904246137137)
                    ·
                      refine ⟨4192234754573928184602853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5589646339431904246137137 4192234754573928184602853)
                      ·
                        rfl

theorem cell23_8164348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 1, 5, 2].length) (baseStart_8164348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164348 prefixEnd_8164348 := by exact prefixLift 8164348
  have htrace : WordTrace (prefixWord ++ tailWord_8164348) baseStart_8164348 baseEnd_8164348 := by
    simpa [prefixWord, tailWord_8164348, baseEnd_8164348] using wordTrace_append hprefix tailTrace_8164348
  have hstable : (prefixWord ++ tailWord_8164348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164348).length < 2 ^ (prefixWord ++ tailWord_8164348).sum := by decide
  have hdescent : baseEnd_8164348 < baseStart_8164348 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164408 : List Nat := [2, 1, 2, 1, 5, 2, 1, 2, 1, 2, 4]
def baseStart_8164408 : Nat := 118140960795 + 8164408 * 2 ^ 59
def prefixEnd_8164408 : Nat := 4983230072969 + 3 ^ 40 * 8164408 * 2
def baseEnd_8164408 : Nat := 4192265563413197949852577

theorem tailTrace_8164408 : CollatzResearch.WordTrace tailWord_8164408 prefixEnd_8164408 4192265563413197949852577 := by
  unfold tailWord_8164408
  simp only [CollatzResearch.WordTrace]
  refine ⟨148890211702875830360026939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198520282270501107146702585 148890211702875830360026939)
  ·
    refine ⟨223335317554313745540040409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148890211702875830360026939 223335317554313745540040409)
    ·
      refine ⟨167501488165735309155030307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223335317554313745540040409 167501488165735309155030307)
      ·
        refine ⟨251252232248602963732545461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167501488165735309155030307 251252232248602963732545461)
        ·
          refine ⟨23554896773306527849926137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 251252232248602963732545461 23554896773306527849926137)
          ·
            refine ⟨17666172579979895887444603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23554896773306527849926137 17666172579979895887444603)
            ·
              refine ⟨26499258869969843831166905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17666172579979895887444603 26499258869969843831166905)
              ·
                refine ⟨19874444152477382873375179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26499258869969843831166905 19874444152477382873375179)
                ·
                  refine ⟨29811666228716074310062769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19874444152477382873375179 29811666228716074310062769)
                  ·
                    refine ⟨22358749671537055732547077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29811666228716074310062769 22358749671537055732547077)
                    ·
                      refine ⟨4192265563413197949852577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22358749671537055732547077 4192265563413197949852577)
                      ·
                        rfl

theorem cell23_8164408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_8164408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164408 prefixEnd_8164408 := by exact prefixLift 8164408
  have htrace : WordTrace (prefixWord ++ tailWord_8164408) baseStart_8164408 baseEnd_8164408 := by
    simpa [prefixWord, tailWord_8164408, baseEnd_8164408] using wordTrace_append hprefix tailTrace_8164408
  have hstable : (prefixWord ++ tailWord_8164408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164408).length < 2 ^ (prefixWord ++ tailWord_8164408).sum := by decide
  have hdescent : baseEnd_8164408 < baseStart_8164408 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164422 : List Nat := [6, 1, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_8164422 : Nat := 118140960795 + 8164422 * 2 ^ 59
def prefixEnd_8164422 : Nat := 4983230072969 + 3 ^ 40 * 8164422 * 2
def baseEnd_8164422 : Nat := 1397424250714120298359171

theorem tailTrace_8164422 : CollatzResearch.WordTrace tailWord_8164422 prefixEnd_8164422 1397424250714120298359171 := by
  unfold tailWord_8164422
  simp only [CollatzResearch.WordTrace]
  refine ⟨9305654188365654409720735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 198520622685133960740709013 9305654188365654409720735)
  ·
    refine ⟨13958481282548481614581103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9305654188365654409720735 13958481282548481614581103)
    ·
      refine ⟨20937721923822722421871655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13958481282548481614581103 20937721923822722421871655)
      ·
        refine ⟨31406582885734083632807483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20937721923822722421871655 31406582885734083632807483)
        ·
          refine ⟨47109874328601125449211225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31406582885734083632807483 47109874328601125449211225)
          ·
            refine ⟨35332405746450844086908419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47109874328601125449211225 35332405746450844086908419)
            ·
              refine ⟨52998608619676266130362629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35332405746450844086908419 52998608619676266130362629)
              ·
                refine ⟨9937239116189299899442993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52998608619676266130362629 9937239116189299899442993)
                ·
                  refine ⟨7452929337141974924582245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9937239116189299899442993 7452929337141974924582245)
                  ·
                    refine ⟨1397424250714120298359171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7452929337141974924582245 1397424250714120298359171)
                    ·
                      rfl

theorem cell23_8164422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_8164422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164422 prefixEnd_8164422 := by exact prefixLift 8164422
  have htrace : WordTrace (prefixWord ++ tailWord_8164422) baseStart_8164422 baseEnd_8164422 := by
    simpa [prefixWord, tailWord_8164422, baseEnd_8164422] using wordTrace_append hprefix tailTrace_8164422
  have hstable : (prefixWord ++ tailWord_8164422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164422).length < 2 ^ (prefixWord ++ tailWord_8164422).sum := by decide
  have hdescent : baseEnd_8164422 < baseStart_8164422 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164446 : List Nat := [4, 4, 1, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_8164446 : Nat := 118140960795 + 8164446 * 2 ^ 59
def prefixEnd_8164446 : Nat := 4983230072969 + 3 ^ 40 * 8164446 * 2
def baseEnd_8164446 : Nat := 4192285075678068801177403

theorem tailTrace_8164446 : CollatzResearch.WordTrace tailWord_8164446 prefixEnd_8164446 4192285075678068801177403 := by
  unfold tailWord_8164446
  simp only [CollatzResearch.WordTrace]
  refine ⟨37222726172451749151242149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198521206253075995473291461 37222726172451749151242149)
  ·
    refine ⟨6979261157334702965857903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37222726172451749151242149 6979261157334702965857903)
    ·
      refine ⟨10468891736002054448786855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6979261157334702965857903 10468891736002054448786855)
      ·
        refine ⟨15703337604003081673180283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10468891736002054448786855 15703337604003081673180283)
        ·
          refine ⟨23555006406004622509770425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15703337604003081673180283 23555006406004622509770425)
          ·
            refine ⟨17666254804503466882327819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23555006406004622509770425 17666254804503466882327819)
            ·
              refine ⟨26499382206755200323491729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17666254804503466882327819 26499382206755200323491729)
              ·
                refine ⟨19874536655066400242618797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26499382206755200323491729 19874536655066400242618797)
                ·
                  refine ⟨7452951245649900090982049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19874536655066400242618797 7452951245649900090982049)
                  ·
                    refine ⟨5589713434237425068236537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7452951245649900090982049 5589713434237425068236537)
                    ·
                      refine ⟨4192285075678068801177403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5589713434237425068236537 4192285075678068801177403)
                      ·
                        rfl

theorem cell23_8164446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_8164446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164446 prefixEnd_8164446 := by exact prefixLift 8164446
  have htrace : WordTrace (prefixWord ++ tailWord_8164446) baseStart_8164446 baseEnd_8164446 := by
    simpa [prefixWord, tailWord_8164446, baseEnd_8164446] using wordTrace_append hprefix tailTrace_8164446
  have hstable : (prefixWord ++ tailWord_8164446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164446).length < 2 ^ (prefixWord ++ tailWord_8164446).sum := by decide
  have hdescent : baseEnd_8164446 < baseStart_8164446 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164451 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 4]
def baseStart_8164451 : Nat := 118140960795 + 8164451 * 2 ^ 59
def prefixEnd_8164451 : Nat := 4983230072969 + 3 ^ 40 * 8164451 * 2
def baseEnd_8164451 : Nat := 4192287643081341281614879

theorem tailTrace_8164451 : CollatzResearch.WordTrace tailWord_8164451 prefixEnd_8164451 4192287643081341281614879 := by
  unfold tailWord_8164451
  simp only [CollatzResearch.WordTrace]
  refine ⟨297781991744595879063869207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198521327829730586042579471 297781991744595879063869207)
  ·
    refine ⟨446672987616893818595803811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297781991744595879063869207 446672987616893818595803811)
    ·
      refine ⟨670009481425340727893705717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446672987616893818595803811 670009481425340727893705717)
      ·
        refine ⟨62813388883625693240034911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 670009481425340727893705717 62813388883625693240034911)
        ·
          refine ⟨94220083325438539860052367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62813388883625693240034911 94220083325438539860052367)
          ·
            refine ⟨141330124988157809790078551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94220083325438539860052367 141330124988157809790078551)
            ·
              refine ⟨211995187482236714685117827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141330124988157809790078551 211995187482236714685117827)
              ·
                refine ⟨317992781223355072027676741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211995187482236714685117827 317992781223355072027676741)
                ·
                  refine ⟨59623646479379076005189389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 317992781223355072027676741 59623646479379076005189389)
                  ·
                    refine ⟨22358867429767153501946021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59623646479379076005189389 22358867429767153501946021)
                    ·
                      refine ⟨4192287643081341281614879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22358867429767153501946021 4192287643081341281614879)
                      ·
                        rfl

theorem cell23_8164451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_8164451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164451 prefixEnd_8164451 := by exact prefixLift 8164451
  have htrace : WordTrace (prefixWord ++ tailWord_8164451) baseStart_8164451 baseEnd_8164451 := by
    simpa [prefixWord, tailWord_8164451, baseEnd_8164451] using wordTrace_append hprefix tailTrace_8164451
  have hstable : (prefixWord ++ tailWord_8164451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164451).length < 2 ^ (prefixWord ++ tailWord_8164451).sum := by decide
  have hdescent : baseEnd_8164451 < baseStart_8164451 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164455 : List Nat := [1, 1, 5, 1, 1, 3, 2, 1, 3, 3, 2]
def baseStart_8164455 : Nat := 118140960795 + 8164455 * 2 ^ 59
def prefixEnd_8164455 : Nat := 4983230072969 + 3 ^ 40 * 8164455 * 2
def baseEnd_8164455 : Nat := 4192289697003959265964861

theorem tailTrace_8164455 : CollatzResearch.WordTrace tailWord_8164455 prefixEnd_8164455 4192289697003959265964861 := by
  unfold tailWord_8164455
  simp only [CollatzResearch.WordTrace]
  refine ⟨297782137636581387747014819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198521425091054258498009879 297782137636581387747014819)
  ·
    refine ⟨446673206454872081620522229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297782137636581387747014819 446673206454872081620522229)
    ·
      refine ⟨41875613105144257651923959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 446673206454872081620522229 41875613105144257651923959)
      ·
        refine ⟨62813419657716386477885939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41875613105144257651923959 62813419657716386477885939)
        ·
          refine ⟨94220129486574579716828909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62813419657716386477885939 94220129486574579716828909)
          ·
            refine ⟨35332548557465467393810841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94220129486574579716828909 35332548557465467393810841)
            ·
              refine ⟨26499411418099100545358131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35332548557465467393810841 26499411418099100545358131)
              ·
                refine ⟨39749117127148650818037197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26499411418099100545358131 39749117127148650818037197)
                ·
                  refine ⟨14905918922680744056763949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39749117127148650818037197 14905918922680744056763949)
                  ·
                    refine ⟨5589719596005279021286481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14905918922680744056763949 5589719596005279021286481)
                    ·
                      refine ⟨4192289697003959265964861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5589719596005279021286481 4192289697003959265964861)
                      ·
                        rfl

theorem cell23_8164455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_8164455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164455 prefixEnd_8164455 := by exact prefixLift 8164455
  have htrace : WordTrace (prefixWord ++ tailWord_8164455) baseStart_8164455 baseEnd_8164455 := by
    simpa [prefixWord, tailWord_8164455, baseEnd_8164455] using wordTrace_append hprefix tailTrace_8164455
  have hstable : (prefixWord ++ tailWord_8164455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164455).length < 2 ^ (prefixWord ++ tailWord_8164455).sum := by decide
  have hdescent : baseEnd_8164455 < baseStart_8164455 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164471 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 5]
def baseStart_8164471 : Nat := 118140960795 + 8164471 * 2 ^ 59
def prefixEnd_8164471 : Nat := 4983230072969 + 3 ^ 40 * 8164471 * 2
def baseEnd_8164471 : Nat := 4192297912694431203364787

theorem tailTrace_8164471 : CollatzResearch.WordTrace tailWord_8164471 prefixEnd_8164471 4192297912694431203364787 := by
  unfold tailWord_8164471
  simp only [CollatzResearch.WordTrace]
  refine ⟨297782721204523422479597267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198521814136348948319731511 297782721204523422479597267)
  ·
    refine ⟨446674081806785133719395901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297782721204523422479597267 446674081806785133719395901)
    ·
      refine ⟨167502780677544425144773463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446674081806785133719395901 167502780677544425144773463)
      ·
        refine ⟨251254171016316637717160195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167502780677544425144773463 251254171016316637717160195)
        ·
          refine ⟨376881256524474956575740293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251254171016316637717160195 376881256524474956575740293)
          ·
            refine ⟨70665235598339054357951305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 376881256524474956575740293 70665235598339054357951305)
            ·
              refine ⟨52998926698754290768463479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70665235598339054357951305 52998926698754290768463479)
              ·
                refine ⟨79498390048131436152695219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52998926698754290768463479 79498390048131436152695219)
                ·
                  refine ⟨119247585072197154229042829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79498390048131436152695219 119247585072197154229042829)
                  ·
                    refine ⟨44717844402073932835891061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119247585072197154229042829 44717844402073932835891061)
                    ·
                      refine ⟨4192297912694431203364787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44717844402073932835891061 4192297912694431203364787)
                      ·
                        rfl

theorem cell23_8164471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_8164471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164471 prefixEnd_8164471 := by exact prefixLift 8164471
  have htrace : WordTrace (prefixWord ++ tailWord_8164471) baseStart_8164471 baseEnd_8164471 := by
    simpa [prefixWord, tailWord_8164471, baseEnd_8164471] using wordTrace_append hprefix tailTrace_8164471
  have hstable : (prefixWord ++ tailWord_8164471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164471).length < 2 ^ (prefixWord ++ tailWord_8164471).sum := by decide
  have hdescent : baseEnd_8164471 < baseStart_8164471 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164472 : List Nat := [2, 1, 2, 1, 1, 1, 8, 1, 1, 3, 2]
def baseStart_8164472 : Nat := 118140960795 + 8164472 * 2 ^ 59
def prefixEnd_8164472 : Nat := 4983230072969 + 3 ^ 40 * 8164472 * 2
def baseEnd_8164472 : Nat := 4192298426175085699452283

theorem tailTrace_8164472 : CollatzResearch.WordTrace tailWord_8164472 prefixEnd_8164472 4192298426175085699452283 := by
  unfold tailWord_8164472
  simp only [CollatzResearch.WordTrace]
  refine ⟨148891378838759899825191835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198521838451679866433589113 148891378838759899825191835)
  ·
    refine ⟨223337068258139849737787753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148891378838759899825191835 223337068258139849737787753)
    ·
      refine ⟨167502801193604887303340815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223337068258139849737787753 167502801193604887303340815)
      ·
        refine ⟨251254201790407330955011223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167502801193604887303340815 251254201790407330955011223)
        ·
          refine ⟨376881302685610996432516835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251254201790407330955011223 376881302685610996432516835)
          ·
            refine ⟨565321954028416494648775253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376881302685610996432516835 565321954028416494648775253)
            ·
              refine ⟨6624866648770505796665335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 565321954028416494648775253 6624866648770505796665335)
              ·
                refine ⟨9937299973155758694998003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6624866648770505796665335 9937299973155758694998003)
                ·
                  refine ⟨14905949959733638042497005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9937299973155758694998003 14905949959733638042497005)
                  ·
                    refine ⟨5589731234900114265936377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14905949959733638042497005 5589731234900114265936377)
                    ·
                      refine ⟨4192298426175085699452283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5589731234900114265936377 4192298426175085699452283)
                      ·
                        rfl

theorem cell23_8164472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 1, 3, 2].length) (baseStart_8164472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164472 prefixEnd_8164472 := by exact prefixLift 8164472
  have htrace : WordTrace (prefixWord ++ tailWord_8164472) baseStart_8164472 baseEnd_8164472 := by
    simpa [prefixWord, tailWord_8164472, baseEnd_8164472] using wordTrace_append hprefix tailTrace_8164472
  have hstable : (prefixWord ++ tailWord_8164472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164472).length < 2 ^ (prefixWord ++ tailWord_8164472).sum := by decide
  have hdescent : baseEnd_8164472 < baseStart_8164472 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164508 : List Nat := [2, 2, 3, 2, 1, 2, 2, 2, 7]
def baseStart_8164508 : Nat := 118140960795 + 8164508 * 2 ^ 59
def prefixEnd_8164508 : Nat := 4983230072969 + 3 ^ 40 * 8164508 * 2
def baseEnd_8164508 : Nat := 465812990164294173178013

theorem tailTrace_8164508 : CollatzResearch.WordTrace tailWord_8164508 prefixEnd_8164508 465812990164294173178013 := by
  unfold tailWord_8164508
  simp only [CollatzResearch.WordTrace]
  refine ⟨148892035352694688899347089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198522713803592918532462785 148892035352694688899347089)
  ·
    refine ⟨111669026514521016674510317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148892035352694688899347089 111669026514521016674510317)
    ·
      refine ⟨41875884942945381252941369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111669026514521016674510317 41875884942945381252941369)
      ·
        refine ⟨31406913707209035939706027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41875884942945381252941369 31406913707209035939706027)
        ·
          refine ⟨47110370560813553909559041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31406913707209035939706027 47110370560813553909559041)
          ·
            refine ⟨35332777920610165432169281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47110370560813553909559041 35332777920610165432169281)
            ·
              refine ⟨26499583440457624074126961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35332777920610165432169281 26499583440457624074126961)
              ·
                refine ⟨19874687580343218055595221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26499583440457624074126961 19874687580343218055595221)
                ·
                  refine ⟨465812990164294173178013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19874687580343218055595221 465812990164294173178013)
                  ·
                    rfl

theorem cell23_8164508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 7].length) (baseStart_8164508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164508 prefixEnd_8164508 := by exact prefixLift 8164508
  have htrace : WordTrace (prefixWord ++ tailWord_8164508) baseStart_8164508 baseEnd_8164508 := by
    simpa [prefixWord, tailWord_8164508, baseEnd_8164508] using wordTrace_append hprefix tailTrace_8164508
  have hstable : (prefixWord ++ tailWord_8164508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164508).length < 2 ^ (prefixWord ++ tailWord_8164508).sum := by decide
  have hdescent : baseEnd_8164508 < baseStart_8164508 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164595 : List Nat := [1, 1, 1, 2, 2, 5, 2, 2, 2, 2, 3]
def baseStart_8164595 : Nat := 118140960795 + 8164595 * 2 ^ 59
def prefixEnd_8164595 : Nat := 4983230072969 + 3 ^ 40 * 8164595 * 2
def baseEnd_8164595 : Nat := 4192361584295588718214217

theorem tailTrace_8164595 : CollatzResearch.WordTrace tailWord_8164595 prefixEnd_8164595 4192361584295588718214217 := by
  unfold tailWord_8164595
  simp only [CollatzResearch.WordTrace]
  refine ⟨297787243856074191657111239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198524829237382794438074159 297787243856074191657111239)
  ·
    refine ⟨446680865784111287485666859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297787243856074191657111239 446680865784111287485666859)
    ·
      refine ⟨670021298676166931228500289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446680865784111287485666859 670021298676166931228500289)
      ·
        refine ⟨502515974007125198421375217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 670021298676166931228500289 502515974007125198421375217)
        ·
          refine ⟨376886980505343898816031413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502515974007125198421375217 376886980505343898816031413)
          ·
            refine ⟨35333154422375990514002945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 376886980505343898816031413 35333154422375990514002945)
            ·
              refine ⟨26499865816781992885502209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35333154422375990514002945 26499865816781992885502209)
              ·
                refine ⟨19874899362586494664126657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26499865816781992885502209 19874899362586494664126657)
                ·
                  refine ⟨14906174521939870998094993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19874899362586494664126657 14906174521939870998094993)
                  ·
                    refine ⟨11179630891454903248571245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14906174521939870998094993 11179630891454903248571245)
                    ·
                      refine ⟨4192361584295588718214217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11179630891454903248571245 4192361584295588718214217)
                      ·
                        rfl

theorem cell23_8164595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2, 3].length) (baseStart_8164595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164595 prefixEnd_8164595 := by exact prefixLift 8164595
  have htrace : WordTrace (prefixWord ++ tailWord_8164595) baseStart_8164595 baseEnd_8164595 := by
    simpa [prefixWord, tailWord_8164595, baseEnd_8164595] using wordTrace_append hprefix tailTrace_8164595
  have hstable : (prefixWord ++ tailWord_8164595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164595).length < 2 ^ (prefixWord ++ tailWord_8164595).sum := by decide
  have hdescent : baseEnd_8164595 < baseStart_8164595 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164602 : List Nat := [3, 1, 1, 1, 1, 4, 3, 4, 1, 4]
def baseStart_8164602 : Nat := 118140960795 + 8164602 * 2 ^ 59
def prefixEnd_8164602 : Nat := 4983230072969 + 3 ^ 40 * 8164602 * 2
def baseEnd_8164602 : Nat := 1397455059553390063608895

theorem tailTrace_8164602 : CollatzResearch.WordTrace tailWord_8164602 prefixEnd_8164602 1397455059553390063608895 := by
  unfold tailWord_8164602
  simp only [CollatzResearch.WordTrace]
  refine ⟨74446874791762207963154015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198524999444699221235077373 74446874791762207963154015)
  ·
    refine ⟨111670312187643311944731023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74446874791762207963154015 111670312187643311944731023)
    ·
      refine ⟨167505468281464967917096535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111670312187643311944731023 167505468281464967917096535)
      ·
        refine ⟨251258202422197451875644803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167505468281464967917096535 251258202422197451875644803)
        ·
          refine ⟨376887303633296177813467205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251258202422197451875644803 376887303633296177813467205)
          ·
            refine ⟨70666369431243033340025101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 376887303633296177813467205 70666369431243033340025101)
            ·
              refine ⟨26499888536716137502509413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70666369431243033340025101 26499888536716137502509413)
              ·
                refine ⟨4968729100634275781720515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26499888536716137502509413 4968729100634275781720515)
                ·
                  refine ⟨7453093650951413672580773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4968729100634275781720515 7453093650951413672580773)
                  ·
                    refine ⟨1397455059553390063608895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7453093650951413672580773 1397455059553390063608895)
                    ·
                      rfl

theorem cell23_8164602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4, 1, 4].length) (baseStart_8164602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164602 prefixEnd_8164602 := by exact prefixLift 8164602
  have htrace : WordTrace (prefixWord ++ tailWord_8164602) baseStart_8164602 baseEnd_8164602 := by
    simpa [prefixWord, tailWord_8164602, baseEnd_8164602] using wordTrace_append hprefix tailTrace_8164602
  have hstable : (prefixWord ++ tailWord_8164602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164602).length < 2 ^ (prefixWord ++ tailWord_8164602).sum := by decide
  have hdescent : baseEnd_8164602 < baseStart_8164602 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164608 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 3]
def baseStart_8164608 : Nat := 118140960795 + 8164608 * 2 ^ 59
def prefixEnd_8164608 : Nat := 4983230072969 + 3 ^ 40 * 8164608 * 2
def baseEnd_8164608 : Nat := 4192368259544097167351657

theorem tailTrace_8164608 : CollatzResearch.WordTrace tailWord_8164608 prefixEnd_8164608 4192368259544097167351657 := by
  unfold tailWord_8164608
  simp only [CollatzResearch.WordTrace]
  refine ⟨148893859002513547438667239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198525145336684729918222985 148893859002513547438667239)
  ·
    refine ⟨223340788503770321158000859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148893859002513547438667239 223340788503770321158000859)
    ·
      refine ⟨335011182755655481737001289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223340788503770321158000859 335011182755655481737001289)
      ·
        refine ⟨251258387066741611302750967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335011182755655481737001289 251258387066741611302750967)
        ·
          refine ⟨376887580600112416954126451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251258387066741611302750967 376887580600112416954126451)
          ·
            refine ⟨565331370900168625431189677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376887580600112416954126451 565331370900168625431189677)
            ·
              refine ⟨211999264087563234536696129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 565331370900168625431189677 211999264087563234536696129)
              ·
                refine ⟨158999448065672425902522097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211999264087563234536696129 158999448065672425902522097)
                ·
                  refine ⟨119249586049254319426891573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158999448065672425902522097 119249586049254319426891573)
                  ·
                    refine ⟨11179648692117592446271085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 119249586049254319426891573 11179648692117592446271085)
                    ·
                      refine ⟨4192368259544097167351657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11179648692117592446271085 4192368259544097167351657)
                      ·
                        rfl

theorem cell23_8164608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 3].length) (baseStart_8164608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164608 prefixEnd_8164608 := by exact prefixLift 8164608
  have htrace : WordTrace (prefixWord ++ tailWord_8164608) baseStart_8164608 baseEnd_8164608 := by
    simpa [prefixWord, tailWord_8164608, baseEnd_8164608] using wordTrace_append hprefix tailTrace_8164608
  have hstable : (prefixWord ++ tailWord_8164608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164608).length < 2 ^ (prefixWord ++ tailWord_8164608).sum := by decide
  have hdescent : baseEnd_8164608 < baseStart_8164608 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164626 : List Nat := [3, 2, 4, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_8164626 : Nat := 118140960795 + 8164626 * 2 ^ 59
def prefixEnd_8164626 : Nat := 4983230072969 + 3 ^ 40 * 8164626 * 2
def baseEnd_8164626 : Nat := 4192377502195878096926575

theorem tailTrace_8164626 : CollatzResearch.WordTrace tailWord_8164626 prefixEnd_8164626 4192377502195878096926575 := by
  unfold tailWord_8164626
  simp only [CollatzResearch.WordTrace]
  refine ⟨74447093629740470987872433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198525583012641255967659821 74447093629740470987872433)
  ·
    refine ⟨55835320222305353240904325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74447093629740470987872433 55835320222305353240904325)
    ·
      refine ⟨10469122541682253732669561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55835320222305353240904325 10469122541682253732669561)
      ·
        refine ⟨7851841906261690299502171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10469122541682253732669561 7851841906261690299502171)
        ·
          refine ⟨11777762859392535449253257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7851841906261690299502171 11777762859392535449253257)
          ·
            refine ⟨8833322144544401586939943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11777762859392535449253257 8833322144544401586939943)
            ·
              refine ⟨13249983216816602380409915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8833322144544401586939943 13249983216816602380409915)
              ·
                refine ⟨19874974825224903570614873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13249983216816602380409915 19874974825224903570614873)
                ·
                  refine ⟨14906231118918677677961155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19874974825224903570614873 14906231118918677677961155)
                  ·
                    refine ⟨22359346678378016516941733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14906231118918677677961155 22359346678378016516941733)
                    ·
                      refine ⟨4192377502195878096926575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22359346678378016516941733 4192377502195878096926575)
                      ·
                        rfl

theorem cell23_8164626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_8164626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164626 prefixEnd_8164626 := by exact prefixLift 8164626
  have htrace : WordTrace (prefixWord ++ tailWord_8164626) baseStart_8164626 baseEnd_8164626 := by
    simpa [prefixWord, tailWord_8164626, baseEnd_8164626] using wordTrace_append hprefix tailTrace_8164626
  have hstable : (prefixWord ++ tailWord_8164626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164626).length < 2 ^ (prefixWord ++ tailWord_8164626).sum := by decide
  have hdescent : baseEnd_8164626 < baseStart_8164626 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164659 : List Nat := [1, 1, 1, 2, 5, 2, 2, 4, 1, 1, 3]
def baseStart_8164659 : Nat := 118140960795 + 8164659 * 2 ^ 59
def prefixEnd_8164659 : Nat := 4983230072969 + 3 ^ 40 * 8164659 * 2
def baseEnd_8164659 : Nat := 4192394447057476467813923

theorem tailTrace_8164659 : CollatzResearch.WordTrace tailWord_8164659 prefixEnd_8164659 4192394447057476467813923 := by
  unfold tailWord_8164659
  simp only [CollatzResearch.WordTrace]
  refine ⟨297789578127842330587441031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198526385418561553724960687 297789578127842330587441031)
  ·
    refine ⟨446684367191763495881161547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297789578127842330587441031 446684367191763495881161547)
    ·
      refine ⟨670026550787645243821742321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446684367191763495881161547 670026550787645243821742321)
      ·
        refine ⟨502519913090733932866306741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 670026550787645243821742321 502519913090733932866306741)
        ·
          refine ⟨47111241852256306206216257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 502519913090733932866306741 47111241852256306206216257)
          ·
            refine ⟨35333431389192229654662193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47111241852256306206216257 35333431389192229654662193)
            ·
              refine ⟨26500073541894172240996645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35333431389192229654662193 26500073541894172240996645)
              ·
                refine ⟨4968763789105157295186871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26500073541894172240996645 4968763789105157295186871)
                ·
                  refine ⟨7453145683657735942780307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4968763789105157295186871 7453145683657735942780307)
                  ·
                    refine ⟨11179718525486603914170461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7453145683657735942780307 11179718525486603914170461)
                    ·
                      refine ⟨4192394447057476467813923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11179718525486603914170461 4192394447057476467813923)
                      ·
                        rfl

theorem cell23_8164659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4, 1, 1, 3].length) (baseStart_8164659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164659 prefixEnd_8164659 := by exact prefixLift 8164659
  have htrace : WordTrace (prefixWord ++ tailWord_8164659) baseStart_8164659 baseEnd_8164659 := by
    simpa [prefixWord, tailWord_8164659, baseEnd_8164659] using wordTrace_append hprefix tailTrace_8164659
  have hstable : (prefixWord ++ tailWord_8164659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164659).length < 2 ^ (prefixWord ++ tailWord_8164659).sum := by decide
  have hdescent : baseEnd_8164659 < baseStart_8164659 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164688 : List Nat := [2, 1, 1, 1, 1, 5, 3, 9]
def baseStart_8164688 : Nat := 118140960795 + 8164688 * 2 ^ 59
def prefixEnd_8164688 : Nat := 4983230072969 + 3 ^ 40 * 8164688 * 2
def baseEnd_8164688 : Nat := 155274419925794698309307

theorem tailTrace_8164688 : CollatzResearch.WordTrace tailWord_8164688 prefixEnd_8164688 155274419925794698309307 := by
  unfold tailWord_8164688
  simp only [CollatzResearch.WordTrace]
  refine ⟨148895317922368634270123359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198527090563158179026831145 148895317922368634270123359)
  ·
    refine ⟨223342976883552951405185039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148895317922368634270123359 223342976883552951405185039)
    ·
      refine ⟨335014465325329427107777559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223342976883552951405185039 335014465325329427107777559)
      ·
        refine ⟨502521697987994140661666339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335014465325329427107777559 502521697987994140661666339)
        ·
          refine ⟨753782546981991210992499509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502521697987994140661666339 753782546981991210992499509)
          ·
            refine ⟨70667113779561676030546829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 753782546981991210992499509 70667113779561676030546829)
            ·
              refine ⟨26500167667335628511455061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70667113779561676030546829 26500167667335628511455061)
              ·
                refine ⟨155274419925794698309307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26500167667335628511455061 155274419925794698309307)
                ·
                  rfl

theorem cell23_8164688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 9].length) (baseStart_8164688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164688 prefixEnd_8164688 := by exact prefixLift 8164688
  have htrace : WordTrace (prefixWord ++ tailWord_8164688) baseStart_8164688 baseEnd_8164688 := by
    simpa [prefixWord, tailWord_8164688, baseEnd_8164688] using wordTrace_append hprefix tailTrace_8164688
  have hstable : (prefixWord ++ tailWord_8164688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164688).length < 2 ^ (prefixWord ++ tailWord_8164688).sum := by decide
  have hdescent : baseEnd_8164688 < baseStart_8164688 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164716 : List Nat := [2, 2, 1, 1, 5, 3, 1, 1, 3, 2, 2]
def baseStart_8164716 : Nat := 118140960795 + 8164716 * 2 ^ 59
def prefixEnd_8164716 : Nat := 4983230072969 + 3 ^ 40 * 8164716 * 2
def baseEnd_8164716 : Nat := 4192423715454782744801161

theorem tailTrace_8164716 : CollatzResearch.WordTrace tailWord_8164716 prefixEnd_8164716 4192423715454782744801161 := by
  unfold tailWord_8164716
  simp only [CollatzResearch.WordTrace]
  refine ⟨148895828544317914661133001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198527771392423886214844001 148895828544317914661133001)
  ·
    refine ⟨111671871408238435995849751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148895828544317914661133001 111671871408238435995849751)
    ·
      refine ⟨167507807112357653993774627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111671871408238435995849751 167507807112357653993774627)
      ·
        refine ⟨251261710668536480990661941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167507807112357653993774627 251261710668536480990661941)
        ·
          refine ⟨23555785375175295092874557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 251261710668536480990661941 23555785375175295092874557)
          ·
            refine ⟨8833419515690735659827959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23555785375175295092874557 8833419515690735659827959)
            ·
              refine ⟨13250129273536103489741939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8833419515690735659827959 13250129273536103489741939)
              ·
                refine ⟨19875193910304155234612909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13250129273536103489741939 19875193910304155234612909)
                ·
                  refine ⟨7453197716364058212979841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19875193910304155234612909 7453197716364058212979841)
                  ·
                    refine ⟨5589898287273043659734881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7453197716364058212979841 5589898287273043659734881)
                    ·
                      refine ⟨4192423715454782744801161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5589898287273043659734881 4192423715454782744801161)
                      ·
                        rfl

theorem cell23_8164716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 2, 2].length) (baseStart_8164716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164716 prefixEnd_8164716 := by exact prefixLift 8164716
  have htrace : WordTrace (prefixWord ++ tailWord_8164716) baseStart_8164716 baseEnd_8164716 := by
    simpa [prefixWord, tailWord_8164716, baseEnd_8164716] using wordTrace_append hprefix tailTrace_8164716
  have hstable : (prefixWord ++ tailWord_8164716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164716).length < 2 ^ (prefixWord ++ tailWord_8164716).sum := by decide
  have hdescent : baseEnd_8164716 < baseStart_8164716 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164772 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 5, 4, 2]
def baseStart_8164772 : Nat := 118140960795 + 8164772 * 2 ^ 59
def prefixEnd_8164772 : Nat := 4983230072969 + 3 ^ 40 * 8164772 * 2
def baseEnd_8164772 : Nat := 4192452470371434525700903

theorem tailTrace_8164772 : CollatzResearch.WordTrace tailWord_8164772 prefixEnd_8164772 4192452470371434525700903 := by
  unfold tailWord_8164772
  simp only [CollatzResearch.WordTrace]
  refine ⟨148896849788216475443152285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198529133050955300590869713 148896849788216475443152285)
  ·
    refine ⟨55836318670581178291182107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148896849788216475443152285 55836318670581178291182107)
    ·
      refine ⟨83754478005871767436773161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55836318670581178291182107 83754478005871767436773161)
      ·
        refine ⟨62815858504403825577579871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83754478005871767436773161 62815858504403825577579871)
        ·
          refine ⟨94223787756605738366369807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62815858504403825577579871 94223787756605738366369807)
          ·
            refine ⟨141335681634908607549554711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94223787756605738366369807 141335681634908607549554711)
            ·
              refine ⟨212003522452362911324332067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141335681634908607549554711 212003522452362911324332067)
              ·
                refine ⟨318005283678544366986498101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212003522452362911324332067 318005283678544366986498101)
                ·
                  refine ⟨29812995344863534404984197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 318005283678544366986498101 29812995344863534404984197)
                  ·
                    refine ⟨5589936627161912700934537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29812995344863534404984197 5589936627161912700934537)
                    ·
                      refine ⟨4192452470371434525700903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5589936627161912700934537 4192452470371434525700903)
                      ·
                        rfl

theorem cell23_8164772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_8164772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164772 prefixEnd_8164772 := by exact prefixLift 8164772
  have htrace : WordTrace (prefixWord ++ tailWord_8164772) baseStart_8164772 baseEnd_8164772 := by
    simpa [prefixWord, tailWord_8164772, baseEnd_8164772] using wordTrace_append hprefix tailTrace_8164772
  have hstable : (prefixWord ++ tailWord_8164772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164772).length < 2 ^ (prefixWord ++ tailWord_8164772).sum := by decide
  have hdescent : baseEnd_8164772 < baseStart_8164772 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164789 : List Nat := [1, 3, 3, 2, 2, 1, 1, 3, 1, 4, 2]
def baseStart_8164789 : Nat := 118140960795 + 8164789 * 2 ^ 59
def prefixEnd_8164789 : Nat := 4983230072969 + 3 ^ 40 * 8164789 * 2
def baseEnd_8164789 : Nat := 4192461199542560959188325

theorem tailTrace_8164789 : CollatzResearch.WordTrace tailWord_8164789 prefixEnd_8164789 4192461199542560959188325 := by
  unfold tailWord_8164789
  simp only [CollatzResearch.WordTrace]
  refine ⟨297794319617371362789673421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198529546411580908526448947 297794319617371362789673421)
  ·
    refine ⟨111672869856514261046127533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297794319617371362789673421 111672869856514261046127533)
    ·
      refine ⟨41877326196192847892297825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111672869856514261046127533 41877326196192847892297825)
      ·
        refine ⟨31407994647144635919223369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41877326196192847892297825 31407994647144635919223369)
        ·
          refine ⟨23555995985358476939417527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31407994647144635919223369 23555995985358476939417527)
          ·
            refine ⟨35333993978037715409126291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23555995985358476939417527 35333993978037715409126291)
            ·
              refine ⟨53000990967056573113689437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35333993978037715409126291 53000990967056573113689437)
              ·
                refine ⟨19875371612646214917633539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53000990967056573113689437 19875371612646214917633539)
                ·
                  refine ⟨29813057418969322376450309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19875371612646214917633539 29813057418969322376450309)
                  ·
                    refine ⟨5589948266056747945584433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29813057418969322376450309 5589948266056747945584433)
                    ·
                      refine ⟨4192461199542560959188325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5589948266056747945584433 4192461199542560959188325)
                      ·
                        rfl

theorem cell23_8164789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_8164789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164789 prefixEnd_8164789 := by exact prefixLift 8164789
  have htrace : WordTrace (prefixWord ++ tailWord_8164789) baseStart_8164789 baseEnd_8164789 := by
    simpa [prefixWord, tailWord_8164789, baseEnd_8164789] using wordTrace_append hprefix tailTrace_8164789
  have hstable : (prefixWord ++ tailWord_8164789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164789).length < 2 ^ (prefixWord ++ tailWord_8164789).sum := by decide
  have hdescent : baseEnd_8164789 < baseStart_8164789 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164829 : List Nat := [1, 4, 3, 1, 1, 2, 2, 4, 5]
def baseStart_8164829 : Nat := 118140960795 + 8164829 * 2 ^ 59
def prefixEnd_8164829 : Nat := 4983230072969 + 3 ^ 40 * 8164829 * 2
def baseEnd_8164829 : Nat := 465831304307637866965349

theorem tailTrace_8164829 : CollatzResearch.WordTrace tailWord_8164829 prefixEnd_8164829 465831304307637866965349 := by
  unfold tailWord_8164829
  simp only [CollatzResearch.WordTrace]
  refine ⟨297795778537226449621129541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198530519024817633080753027 297795778537226449621129541)
  ·
    refine ⟨55836708475729959303961789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297795778537226449621129541 55836708475729959303961789)
    ·
      refine ⟨20938765678398734738985671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55836708475729959303961789 20938765678398734738985671)
      ·
        refine ⟨31408148517598102108478507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20938765678398734738985671 31408148517598102108478507)
        ·
          refine ⟨47112222776397153162717761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31408148517598102108478507 47112222776397153162717761)
          ·
            refine ⟨35334167082297864872038321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47112222776397153162717761 35334167082297864872038321)
            ·
              refine ⟨26500625311723398654028741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35334167082297864872038321 26500625311723398654028741)
              ·
                refine ⟨4968867245948137247630389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26500625311723398654028741 4968867245948137247630389)
                ·
                  refine ⟨465831304307637866965349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4968867245948137247630389 465831304307637866965349)
                  ·
                    rfl

theorem cell23_8164829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4, 5].length) (baseStart_8164829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164829 prefixEnd_8164829 := by exact prefixLift 8164829
  have htrace : WordTrace (prefixWord ++ tailWord_8164829) baseStart_8164829 baseEnd_8164829 := by
    simpa [prefixWord, tailWord_8164829, baseEnd_8164829] using wordTrace_append hprefix tailTrace_8164829
  have hstable : (prefixWord ++ tailWord_8164829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164829).length < 2 ^ (prefixWord ++ tailWord_8164829).sum := by decide
  have hdescent : baseEnd_8164829 < baseStart_8164829 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164832 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 2, 5, 2]
def baseStart_8164832 : Nat := 118140960795 + 8164832 * 2 ^ 59
def prefixEnd_8164832 : Nat := 4983230072969 + 3 ^ 40 * 8164832 * 2
def baseEnd_8164832 : Nat := 4192483279210704290950627

theorem tailTrace_8164832 : CollatzResearch.WordTrace tailWord_8164832 prefixEnd_8164832 4192483279210704290950627 := by
  unfold tailWord_8164832
  simp only [CollatzResearch.WordTrace]
  refine ⟨148897943978107790566744375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198530591970810387422325833 148897943978107790566744375)
  ·
    refine ⟨223346915967161685850116563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148897943978107790566744375 223346915967161685850116563)
    ·
      refine ⟨335020373950742528775174845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223346915967161685850116563 335020373950742528775174845)
      ·
        refine ⟨125632640231528448290690567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335020373950742528775174845 125632640231528448290690567)
        ·
          refine ⟨188448960347292672436035851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125632640231528448290690567 188448960347292672436035851)
          ·
            refine ⟨282673440520939008654053777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188448960347292672436035851 282673440520939008654053777)
            ·
              refine ⟨212005080390704256490540333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282673440520939008654053777 212005080390704256490540333)
              ·
                refine ⟨79501905146514096183952625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212005080390704256490540333 79501905146514096183952625)
                ·
                  refine ⟨59626428859885572137964469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79501905146514096183952625 59626428859885572137964469)
                  ·
                    refine ⟨5589977705614272387934169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59626428859885572137964469 5589977705614272387934169)
                    ·
                      refine ⟨4192483279210704290950627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5589977705614272387934169 4192483279210704290950627)
                      ·
                        rfl

theorem cell23_8164832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 2, 5, 2].length) (baseStart_8164832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164832 prefixEnd_8164832 := by exact prefixLift 8164832
  have htrace : WordTrace (prefixWord ++ tailWord_8164832) baseStart_8164832 baseEnd_8164832 := by
    simpa [prefixWord, tailWord_8164832, baseEnd_8164832] using wordTrace_append hprefix tailTrace_8164832
  have hstable : (prefixWord ++ tailWord_8164832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164832).length < 2 ^ (prefixWord ++ tailWord_8164832).sum := by decide
  have hdescent : baseEnd_8164832 < baseStart_8164832 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164872 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 5, 4]
def baseStart_8164872 : Nat := 118140960795 + 8164872 * 2 ^ 59
def prefixEnd_8164872 : Nat := 4983230072969 + 3 ^ 40 * 8164872 * 2
def baseEnd_8164872 : Nat := 1397501272812294711483481

theorem tailTrace_8164872 : CollatzResearch.WordTrace tailWord_8164872 prefixEnd_8164872 1397501272812294711483481 := by
  unfold tailWord_8164872
  simp only [CollatzResearch.WordTrace]
  refine ⟨148898673438035333982472435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198531564584047111976629913 148898673438035333982472435)
  ·
    refine ⟨223348010157053000973708653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148898673438035333982472435 223348010157053000973708653)
    ·
      refine ⟨83755503808894875365140745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223348010157053000973708653 83755503808894875365140745)
      ·
        refine ⟨62816627856671156523855559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83755503808894875365140745 62816627856671156523855559)
        ·
          refine ⟨94224941785006734785783339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62816627856671156523855559 94224941785006734785783339)
          ·
            refine ⟨141337412677510102178675009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94224941785006734785783339 141337412677510102178675009)
            ·
              refine ⟨106003059508132576634006257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141337412677510102178675009 106003059508132576634006257)
              ·
                refine ⟨79502294631099432475504693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106003059508132576634006257 79502294631099432475504693)
                ·
                  refine ⟨7453340121665571794578565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79502294631099432475504693 7453340121665571794578565)
                  ·
                    refine ⟨1397501272812294711483481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7453340121665571794578565 1397501272812294711483481)
                    ·
                      rfl

theorem cell23_8164872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_8164872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164872 prefixEnd_8164872 := by exact prefixLift 8164872
  have htrace : WordTrace (prefixWord ++ tailWord_8164872) baseStart_8164872 baseEnd_8164872 := by
    simpa [prefixWord, tailWord_8164872, baseEnd_8164872] using wordTrace_append hprefix tailTrace_8164872
  have hstable : (prefixWord ++ tailWord_8164872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164872).length < 2 ^ (prefixWord ++ tailWord_8164872).sum := by decide
  have hdescent : baseEnd_8164872 < baseStart_8164872 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8164996 : List Nat := [2, 3, 2, 1, 4, 1, 1, 1, 4, 4]
def baseStart_8164996 : Nat := 118140960795 + 8164996 * 2 ^ 59
def prefixEnd_8164996 : Nat := 4983230072969 + 3 ^ 40 * 8164996 * 2
def baseEnd_8164996 : Nat := 1397522496679347216433291

theorem tailTrace_8164996 : CollatzResearch.WordTrace tailWord_8164996 prefixEnd_8164996 1397522496679347216433291 := by
  unfold tailWord_8164996
  simp only [CollatzResearch.WordTrace]
  refine ⟨148900934763810718571229421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198534579685080958094972561 148900934763810718571229421)
  ·
    refine ⟨55837850536429019464211033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148900934763810718571229421 55837850536429019464211033)
    ·
      refine ⟨41878387902321764598158275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55837850536429019464211033 41878387902321764598158275)
      ·
        refine ⟨62817581853482646897237413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41878387902321764598158275 62817581853482646897237413)
        ·
          refine ⟨11778296597527996293232015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62817581853482646897237413 11778296597527996293232015)
          ·
            refine ⟨17667444896291994439848023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11778296597527996293232015 17667444896291994439848023)
            ·
              refine ⟨26501167344437991659772035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17667444896291994439848023 26501167344437991659772035)
              ·
                refine ⟨39751751016656987489658053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26501167344437991659772035 39751751016656987489658053)
                ·
                  refine ⟨7453453315623185154310885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39751751016656987489658053 7453453315623185154310885)
                  ·
                    refine ⟨1397522496679347216433291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7453453315623185154310885 1397522496679347216433291)
                    ·
                      rfl

theorem cell23_8164996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_8164996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8164996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8164996 prefixEnd_8164996 := by exact prefixLift 8164996
  have htrace : WordTrace (prefixWord ++ tailWord_8164996) baseStart_8164996 baseEnd_8164996 := by
    simpa [prefixWord, tailWord_8164996, baseEnd_8164996] using wordTrace_append hprefix tailTrace_8164996
  have hstable : (prefixWord ++ tailWord_8164996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8164996).length < 2 ^ (prefixWord ++ tailWord_8164996).sum := by decide
  have hdescent : baseEnd_8164996 < baseStart_8164996 := by decide
  rcases family_descends (prefixWord ++ tailWord_8164996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165003 : List Nat := [1, 1, 1, 1, 4, 1, 3, 6, 1, 2, 2]
def baseStart_8165003 : Nat := 118140960795 + 8165003 * 2 ^ 59
def prefixEnd_8165003 : Nat := 4983230072969 + 3 ^ 40 * 8165003 * 2
def baseEnd_8165003 : Nat := 4192571084402623121912341

theorem tailTrace_8165003 : CollatzResearch.WordTrace tailWord_8165003 prefixEnd_8165003 4192571084402623121912341 := by
  unfold tailWord_8165003
  simp only [CollatzResearch.WordTrace]
  refine ⟨297802124838596077337963663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198534749892397384891975775 297802124838596077337963663)
  ·
    refine ⟨446703187257894116006945495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297802124838596077337963663 446703187257894116006945495)
    ·
      refine ⟨670054780886841174010418243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446703187257894116006945495 670054780886841174010418243)
      ·
        refine ⟨1005082171330261761015627365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670054780886841174010418243 1005082171330261761015627365)
        ·
          refine ⟨188452907124424080190430131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1005082171330261761015627365 188452907124424080190430131)
          ·
            refine ⟨282679360686636120285645197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188452907124424080190430131 282679360686636120285645197)
            ·
              refine ⟨106004760257488545107116949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282679360686636120285645197 106004760257488545107116949)
              ·
                refine ⟨4968973137069775551896107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106004760257488545107116949 4968973137069775551896107)
                ·
                  refine ⟨7453459705604663327844161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4968973137069775551896107 7453459705604663327844161)
                  ·
                    refine ⟨5590094779203497495883121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7453459705604663327844161 5590094779203497495883121)
                    ·
                      refine ⟨4192571084402623121912341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5590094779203497495883121 4192571084402623121912341)
                      ·
                        rfl

theorem cell23_8165003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6, 1, 2, 2].length) (baseStart_8165003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165003 prefixEnd_8165003 := by exact prefixLift 8165003
  have htrace : WordTrace (prefixWord ++ tailWord_8165003) baseStart_8165003 baseEnd_8165003 := by
    simpa [prefixWord, tailWord_8165003, baseEnd_8165003] using wordTrace_append hprefix tailTrace_8165003
  have hstable : (prefixWord ++ tailWord_8165003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165003).length < 2 ^ (prefixWord ++ tailWord_8165003).sum := by decide
  have hdescent : baseEnd_8165003 < baseStart_8165003 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165016 : List Nat := [2, 1, 2, 4, 1, 4, 1, 1, 1, 2, 4]
def baseStart_8165016 : Nat := 118140960795 + 8165016 * 2 ^ 59
def prefixEnd_8165016 : Nat := 4983230072969 + 3 ^ 40 * 8165016 * 2
def baseEnd_8165016 : Nat := 4192577759651131571049781

theorem tailTrace_8165016 : CollatzResearch.WordTrace tailWord_8165016 prefixEnd_8165016 4192577759651131571049781 := by
  unfold tailWord_8165016
  simp only [CollatzResearch.WordTrace]
  refine ⟨148901299493774490279093451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198535065991699320372124601 148901299493774490279093451)
  ·
    refine ⟨223351949240661735418640177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148901299493774490279093451 223351949240661735418640177)
    ·
      refine ⟨167513961930496301563980133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223351949240661735418640177 167513961930496301563980133)
      ·
        refine ⟨31408867861968056543246275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167513961930496301563980133 31408867861968056543246275)
        ·
          refine ⟨47113301792952084814869413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31408867861968056543246275 47113301792952084814869413)
          ·
            refine ⟨8833744086178515902788015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47113301792952084814869413 8833744086178515902788015)
            ·
              refine ⟨13250616129267773854182023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8833744086178515902788015 13250616129267773854182023)
              ·
                refine ⟨19875924193901660781273035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13250616129267773854182023 19875924193901660781273035)
                ·
                  refine ⟨29813886290852491171909553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19875924193901660781273035 29813886290852491171909553)
                  ·
                    refine ⟨22360414718139368378932165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29813886290852491171909553 22360414718139368378932165)
                    ·
                      refine ⟨4192577759651131571049781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22360414718139368378932165 4192577759651131571049781)
                      ·
                        rfl

theorem cell23_8165016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_8165016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165016 prefixEnd_8165016 := by exact prefixLift 8165016
  have htrace : WordTrace (prefixWord ++ tailWord_8165016) baseStart_8165016 baseEnd_8165016 := by
    simpa [prefixWord, tailWord_8165016, baseEnd_8165016] using wordTrace_append hprefix tailTrace_8165016
  have hstable : (prefixWord ++ tailWord_8165016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165016).length < 2 ^ (prefixWord ++ tailWord_8165016).sum := by decide
  have hdescent : baseEnd_8165016 < baseStart_8165016 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165026 : List Nat := [3, 3, 1, 4, 1, 1, 1, 9]
def baseStart_8165026 : Nat := 118140960795 + 8165026 * 2 ^ 59
def prefixEnd_8165026 : Nat := 4983230072969 + 3 ^ 40 * 8165026 * 2
def baseEnd_8165026 : Nat := 155280847942876908589805

theorem tailTrace_8165026 : CollatzResearch.WordTrace tailWord_8165026 prefixEnd_8165026 155280847942876908589805 := by
  unfold tailWord_8165026
  simp only [CollatzResearch.WordTrace]
  refine ⟨74450740929378188066512733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198535309145008501510700621 74450740929378188066512733)
  ·
    refine ⟨27919027848516820524942275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74450740929378188066512733 27919027848516820524942275)
    ·
      refine ⟨41878541772775230787413413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27919027848516820524942275 41878541772775230787413413)
      ·
        refine ⟨7852226582395355772640015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41878541772775230787413413 7852226582395355772640015)
        ·
          refine ⟨11778339873593033658960023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7852226582395355772640015 11778339873593033658960023)
          ·
            refine ⟨17667509810389550488440035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11778339873593033658960023 17667509810389550488440035)
            ·
              refine ⟨26501264715584325732660053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17667509810389550488440035 26501264715584325732660053)
              ·
                refine ⟨155280847942876908589805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26501264715584325732660053 155280847942876908589805)
                ·
                  rfl

theorem cell23_8165026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 9].length) (baseStart_8165026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165026 prefixEnd_8165026 := by exact prefixLift 8165026
  have htrace : WordTrace (prefixWord ++ tailWord_8165026) baseStart_8165026 baseEnd_8165026 := by
    simpa [prefixWord, tailWord_8165026, baseEnd_8165026] using wordTrace_append hprefix tailTrace_8165026
  have hstable : (prefixWord ++ tailWord_8165026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165026).length < 2 ^ (prefixWord ++ tailWord_8165026).sum := by decide
  have hdescent : baseEnd_8165026 < baseStart_8165026 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165110 : List Nat := [5, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2]
def baseStart_8165110 : Nat := 118140960795 + 8165110 * 2 ^ 59
def prefixEnd_8165110 : Nat := 4983230072969 + 3 ^ 40 * 8165110 * 2
def baseEnd_8165110 : Nat := 4192626026832654203274349

theorem tailTrace_8165110 : CollatzResearch.WordTrace tailWord_8165110 prefixEnd_8165110 4192626026832654203274349 := by
  unfold tailWord_8165110
  simp only [CollatzResearch.WordTrace]
  refine ⟨18612876715575527163256799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198537351632805623074739189 18612876715575527163256799)
  ·
    refine ⟨27919315073363290744885199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18612876715575527163256799 27919315073363290744885199)
    ·
      refine ⟨41878972610044936117327799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27919315073363290744885199 41878972610044936117327799)
      ·
        refine ⟨62818458915067404175991699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41878972610044936117327799 62818458915067404175991699)
        ·
          refine ⟨94227688372601106263987549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62818458915067404175991699 94227688372601106263987549)
          ·
            refine ⟨35335383139725414848995331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94227688372601106263987549 35335383139725414848995331)
            ·
              refine ⟨53003074709588122273492997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35335383139725414848995331 53003074709588122273492997)
              ·
                refine ⟨9938076508047772926279937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53003074709588122273492997 9938076508047772926279937)
                ·
                  refine ⟨7453557381035829694709953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9938076508047772926279937 7453557381035829694709953)
                  ·
                    refine ⟨5590168035776872271032465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7453557381035829694709953 5590168035776872271032465)
                    ·
                      refine ⟨4192626026832654203274349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5590168035776872271032465 4192626026832654203274349)
                      ·
                        rfl

theorem cell23_8165110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_8165110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165110 prefixEnd_8165110 := by exact prefixLift 8165110
  have htrace : WordTrace (prefixWord ++ tailWord_8165110) baseStart_8165110 baseEnd_8165110 := by
    simpa [prefixWord, tailWord_8165110, baseEnd_8165110] using wordTrace_append hprefix tailTrace_8165110
  have hstable : (prefixWord ++ tailWord_8165110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165110).length < 2 ^ (prefixWord ++ tailWord_8165110).sum := by decide
  have hdescent : baseEnd_8165110 < baseStart_8165110 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165116 : List Nat := [2, 2, 2, 1, 3, 1, 3, 4, 5]
def baseStart_8165116 : Nat := 118140960795 + 8165116 * 2 ^ 59
def prefixEnd_8165116 : Nat := 4983230072969 + 3 ^ 40 * 8165116 * 2
def baseEnd_8165116 : Nat := 465847678635175686644369

theorem tailTrace_8165116 : CollatzResearch.WordTrace tailWord_8165116 prefixEnd_8165116 465847678635175686644369 := by
  unfold tailWord_8165116
  simp only [CollatzResearch.WordTrace]
  refine ⟨148903123143593348818413601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198537497524791131757884801 148903123143593348818413601)
  ·
    refine ⟨111677342357695011613810201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148903123143593348818413601 111677342357695011613810201)
    ·
      refine ⟨83758006768271258710357651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111677342357695011613810201 83758006768271258710357651)
      ·
        refine ⟨125637010152406888065536477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83758006768271258710357651 125637010152406888065536477)
        ·
          refine ⟨47113878807152583024576179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125637010152406888065536477 47113878807152583024576179)
          ·
            refine ⟨70670818210728874536864269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47113878807152583024576179 70670818210728874536864269)
            ·
              refine ⟨26501556829023327951324101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70670818210728874536864269 26501556829023327951324101)
              ·
                refine ⟨4969041905441873990873269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26501556829023327951324101 4969041905441873990873269)
                ·
                  refine ⟨465847678635175686644369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4969041905441873990873269 465847678635175686644369)
                  ·
                    rfl

theorem cell23_8165116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4, 5].length) (baseStart_8165116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165116 prefixEnd_8165116 := by exact prefixLift 8165116
  have htrace : WordTrace (prefixWord ++ tailWord_8165116) baseStart_8165116 baseEnd_8165116 := by
    simpa [prefixWord, tailWord_8165116, baseEnd_8165116] using wordTrace_append hprefix tailTrace_8165116
  have hstable : (prefixWord ++ tailWord_8165116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165116).length < 2 ^ (prefixWord ++ tailWord_8165116).sum := by decide
  have hdescent : baseEnd_8165116 < baseStart_8165116 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165146 : List Nat := [3, 1, 1, 3, 2, 2, 3, 1, 2, 5]
def baseStart_8165146 : Nat := 118140960795 + 8165146 * 2 ^ 59
def prefixEnd_8165146 : Nat := 4983230072969 + 3 ^ 40 * 8165146 * 2
def baseEnd_8165146 : Nat := 1397548170712072020808061

theorem tailTrace_8165146 : CollatzResearch.WordTrace tailWord_8165146 prefixEnd_8165146 1397548170712072020808061 := by
  unfold tailWord_8165146
  simp only [CollatzResearch.WordTrace]
  refine ⟨74451835119269503190104823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198538226984718675173612861 74451835119269503190104823)
  ·
    refine ⟨111677752678904254785157235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74451835119269503190104823 111677752678904254785157235)
    ·
      refine ⟨167516629018356382177735853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111677752678904254785157235 167516629018356382177735853)
      ·
        refine ⟨62818735881883643316650945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167516629018356382177735853 62818735881883643316650945)
        ·
          refine ⟨47114051911412732487488209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62818735881883643316650945 47114051911412732487488209)
          ·
            refine ⟨35335538933559549365616157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47114051911412732487488209 35335538933559549365616157)
            ·
              refine ⟨13250827100084831012106059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35335538933559549365616157 13250827100084831012106059)
              ·
                refine ⟨19876240650127246518159089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13250827100084831012106059 19876240650127246518159089)
                ·
                  refine ⟨14907180487595434888619317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19876240650127246518159089 14907180487595434888619317)
                  ·
                    refine ⟨1397548170712072020808061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14907180487595434888619317 1397548170712072020808061)
                    ·
                      rfl

theorem cell23_8165146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 2, 5].length) (baseStart_8165146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165146 prefixEnd_8165146 := by exact prefixLift 8165146
  have htrace : WordTrace (prefixWord ++ tailWord_8165146) baseStart_8165146 baseEnd_8165146 := by
    simpa [prefixWord, tailWord_8165146, baseEnd_8165146] using wordTrace_append hprefix tailTrace_8165146
  have hstable : (prefixWord ++ tailWord_8165146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165146).length < 2 ^ (prefixWord ++ tailWord_8165146).sum := by decide
  have hdescent : baseEnd_8165146 < baseStart_8165146 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165176 : List Nat := [2, 1, 2, 1, 3, 3, 1, 3, 3, 4]
def baseStart_8165176 : Nat := 118140960795 + 8165176 * 2 ^ 59
def prefixEnd_8165176 : Nat := 4983230072969 + 3 ^ 40 * 8165176 * 2
def baseEnd_8165176 : Nat := 1397553305518616981683015

theorem tailTrace_8165176 : CollatzResearch.WordTrace tailWord_8165176 prefixEnd_8165176 1397553305518616981683015 := by
  unfold tailWord_8165176
  simp only [CollatzResearch.WordTrace]
  refine ⟨148904217333484663942005691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198538956444646218589340921 148904217333484663942005691)
  ·
    refine ⟨223356326000226995913008537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148904217333484663942005691 223356326000226995913008537)
    ·
      refine ⟨167517244500170246934756403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223356326000226995913008537 167517244500170246934756403)
      ·
        refine ⟨251275866750255370402134605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167517244500170246934756403 251275866750255370402134605)
        ·
          refine ⟨94228450031345763900800477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251275866750255370402134605 94228450031345763900800477)
          ·
            refine ⟨35335668761754661462800179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94228450031345763900800477 35335668761754661462800179)
            ·
              refine ⟨53003503142631992194200269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35335668761754661462800179 53003503142631992194200269)
              ·
                refine ⟨19876313678486997072825101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53003503142631992194200269 19876313678486997072825101)
                ·
                  refine ⟨7453617629432623902309413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19876313678486997072825101 7453617629432623902309413)
                  ·
                    refine ⟨1397553305518616981683015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7453617629432623902309413 1397553305518616981683015)
                    ·
                      rfl

theorem cell23_8165176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 3, 4].length) (baseStart_8165176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165176 prefixEnd_8165176 := by exact prefixLift 8165176
  have htrace : WordTrace (prefixWord ++ tailWord_8165176) baseStart_8165176 baseEnd_8165176 := by
    simpa [prefixWord, tailWord_8165176, baseEnd_8165176] using wordTrace_append hprefix tailTrace_8165176
  have hstable : (prefixWord ++ tailWord_8165176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165176).length < 2 ^ (prefixWord ++ tailWord_8165176).sum := by decide
  have hdescent : baseEnd_8165176 < baseStart_8165176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165239 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 4]
def baseStart_8165239 : Nat := 118140960795 + 8165239 * 2 ^ 59
def prefixEnd_8165239 : Nat := 4983230072969 + 3 ^ 40 * 8165239 * 2
def baseEnd_8165239 : Nat := 4192692265837084198561255

theorem tailTrace_8165239 : CollatzResearch.WordTrace tailWord_8165239 prefixEnd_8165239 4192692265837084198561255 := by
  unfold tailWord_8165239
  simp only [CollatzResearch.WordTrace]
  refine ⟨297810732465741089643554771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198540488310494059762369847 297810732465741089643554771)
  ·
    refine ⟨446716098698611634465332157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297810732465741089643554771 446716098698611634465332157)
    ·
      refine ⟨167518537011979362924499559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446716098698611634465332157 167518537011979362924499559)
      ·
        refine ⟨251277805517969044386749339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167518537011979362924499559 251277805517969044386749339)
        ·
          refine ⟨376916708276953566580124009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251277805517969044386749339 376916708276953566580124009)
          ·
            refine ⟨282687531207715174935093007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376916708276953566580124009 282687531207715174935093007)
            ·
              refine ⟨424031296811572762402639511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282687531207715174935093007 424031296811572762402639511)
              ·
                refine ⟨636046945217359143603959267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424031296811572762402639511 636046945217359143603959267)
                ·
                  refine ⟨954070417826038715405938901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 636046945217359143603959267 954070417826038715405938901)
                  ·
                    refine ⟨22361025417797782392326693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 954070417826038715405938901 22361025417797782392326693)
                    ·
                      refine ⟨4192692265837084198561255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22361025417797782392326693 4192692265837084198561255)
                      ·
                        rfl

theorem cell23_8165239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_8165239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165239 prefixEnd_8165239 := by exact prefixLift 8165239
  have htrace : WordTrace (prefixWord ++ tailWord_8165239) baseStart_8165239 baseEnd_8165239 := by
    simpa [prefixWord, tailWord_8165239, baseEnd_8165239] using wordTrace_append hprefix tailTrace_8165239
  have hstable : (prefixWord ++ tailWord_8165239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165239).length < 2 ^ (prefixWord ++ tailWord_8165239).sum := by decide
  have hdescent : baseEnd_8165239 < baseStart_8165239 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165278 : List Nat := [4, 3, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_8165278 : Nat := 118140960795 + 8165278 * 2 ^ 59
def prefixEnd_8165278 : Nat := 4983230072969 + 3 ^ 40 * 8165278 * 2
def baseEnd_8165278 : Nat := 1397570763860869848657859

theorem tailTrace_8165278 : CollatzResearch.WordTrace tailWord_8165278 prefixEnd_8165278 1397570763860869848657859 := by
  unfold tailWord_8165278
  simp only [CollatzResearch.WordTrace]
  refine ⟨37226519364074974913028061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198541436608399866202816325 37226519364074974913028061)
  ·
    refine ⟨13959944761528115592385523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37226519364074974913028061 13959944761528115592385523)
    ·
      refine ⟨20939917142292173388578285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13959944761528115592385523 20939917142292173388578285)
      ·
        refine ⟨7852468928359565020716857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20939917142292173388578285 7852468928359565020716857)
        ·
          refine ⟨5889351696269673765537643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7852468928359565020716857 5889351696269673765537643)
          ·
            refine ⟨8834027544404510648306465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5889351696269673765537643 8834027544404510648306465)
            ·
              refine ⟨6625520658303382986229849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8834027544404510648306465 6625520658303382986229849)
              ·
                refine ⟨4969140493727537239672387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6625520658303382986229849 4969140493727537239672387)
                ·
                  refine ⟨7453710740591305859508581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4969140493727537239672387 7453710740591305859508581)
                  ·
                    refine ⟨1397570763860869848657859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7453710740591305859508581 1397570763860869848657859)
                    ·
                      rfl

theorem cell23_8165278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_8165278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165278 prefixEnd_8165278 := by exact prefixLift 8165278
  have htrace : WordTrace (prefixWord ++ tailWord_8165278) baseStart_8165278 baseEnd_8165278 := by
    simpa [prefixWord, tailWord_8165278, baseEnd_8165278] using wordTrace_append hprefix tailTrace_8165278
  have hstable : (prefixWord ++ tailWord_8165278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165278).length < 2 ^ (prefixWord ++ tailWord_8165278).sum := by decide
  have hdescent : baseEnd_8165278 < baseStart_8165278 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165279 : List Nat := [1, 1, 2, 5, 14]
def baseStart_8165279 : Nat := 118140960795 + 8165279 * 2 ^ 59
def prefixEnd_8165279 : Nat := 4983230072969 + 3 ^ 40 * 8165279 * 2
def baseEnd_8165279 : Nat := 5751320720251391004199

theorem tailTrace_8165279 : CollatzResearch.WordTrace tailWord_8165279 prefixEnd_8165279 5751320720251391004199 := by
  unfold tailWord_8165279
  simp only [CollatzResearch.WordTrace]
  refine ⟨297812191385596176475010891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198541460923730784316673927 297812191385596176475010891)
  ·
    refine ⟨446718287078394264712516337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297812191385596176475010891 446718287078394264712516337)
    ·
      refine ⟨335038715308795698534387253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446718287078394264712516337 335038715308795698534387253)
      ·
        refine ⟨31409879560199596737598805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 335038715308795698534387253 31409879560199596737598805)
        ·
          refine ⟨5751320720251391004199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 31409879560199596737598805 5751320720251391004199)
          ·
            rfl

theorem cell23_8165279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 14].length) (baseStart_8165279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165279 prefixEnd_8165279 := by exact prefixLift 8165279
  have htrace : WordTrace (prefixWord ++ tailWord_8165279) baseStart_8165279 baseEnd_8165279 := by
    simpa [prefixWord, tailWord_8165279, baseEnd_8165279] using wordTrace_append hprefix tailTrace_8165279
  have hstable : (prefixWord ++ tailWord_8165279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165279).length < 2 ^ (prefixWord ++ tailWord_8165279).sum := by decide
  have hdescent : baseEnd_8165279 < baseStart_8165279 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165284 : List Nat := [2, 3, 1, 2, 1, 5, 2, 2, 1, 1, 3]
def baseStart_8165284 : Nat := 118140960795 + 8165284 * 2 ^ 59
def prefixEnd_8165284 : Nat := 4983230072969 + 3 ^ 40 * 8165284 * 2
def baseEnd_8165284 : Nat := 4192715372466536522498549

theorem tailTrace_8165284 : CollatzResearch.WordTrace tailWord_8165284 prefixEnd_8165284 4192715372466536522498549 := by
  unfold tailWord_8165284
  simp only [CollatzResearch.WordTrace]
  refine ⟨148906186875289031164471453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198541582500385374885961937 148906186875289031164471453)
  ·
    refine ⟨55839820078233386686676795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148906186875289031164471453 55839820078233386686676795)
    ·
      refine ⟨83759730117350080030015193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55839820078233386686676795 83759730117350080030015193)
      ·
        refine ⟨62819797588012560022511395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83759730117350080030015193 62819797588012560022511395)
        ·
          refine ⟨94229696382018840033767093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62819797588012560022511395 94229696382018840033767093)
          ·
            refine ⟨8834034035814266253165665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94229696382018840033767093 8834034035814266253165665)
            ·
              refine ⟨6625525526860699689874249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8834034035814266253165665 6625525526860699689874249)
              ·
                refine ⟨4969144145145524767405687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6625525526860699689874249 4969144145145524767405687)
                ·
                  refine ⟨7453716217718287151108531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4969144145145524767405687 7453716217718287151108531)
                  ·
                    refine ⟨11180574326577430726662797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7453716217718287151108531 11180574326577430726662797)
                    ·
                      refine ⟨4192715372466536522498549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11180574326577430726662797 4192715372466536522498549)
                      ·
                        rfl

theorem cell23_8165284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_8165284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165284 prefixEnd_8165284 := by exact prefixLift 8165284
  have htrace : WordTrace (prefixWord ++ tailWord_8165284) baseStart_8165284 baseEnd_8165284 := by
    simpa [prefixWord, tailWord_8165284, baseEnd_8165284] using wordTrace_append hprefix tailTrace_8165284
  have hstable : (prefixWord ++ tailWord_8165284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165284).length < 2 ^ (prefixWord ++ tailWord_8165284).sum := by decide
  have hdescent : baseEnd_8165284 < baseStart_8165284 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165289 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 7]
def baseStart_8165289 : Nat := 118140960795 + 8165289 * 2 ^ 59
def prefixEnd_8165289 : Nat := 4983230072969 + 3 ^ 40 * 8165289 * 2
def baseEnd_8165289 : Nat := 4192717939869809002936025

theorem tailTrace_8165289 : CollatzResearch.WordTrace tailWord_8165289 prefixEnd_8165289 4192717939869809002936025 := by
  unfold tailWord_8165289
  simp only [CollatzResearch.WordTrace]
  refine ⟨297812556115559948182874921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198541704077039965455249947 297812556115559948182874921)
  ·
    refine ⟨223359417086669961137156191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297812556115559948182874921 223359417086669961137156191)
    ·
      refine ⟨335039125630004941705734287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223359417086669961137156191 335039125630004941705734287)
      ·
        refine ⟨502558688445007412558601431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335039125630004941705734287 502558688445007412558601431)
        ·
          refine ⟨753838032667511118837902147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502558688445007412558601431 753838032667511118837902147)
          ·
            refine ⟨1130757049001266678256853221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753838032667511118837902147 1130757049001266678256853221)
            ·
              refine ⟨212016946687737502173159979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1130757049001266678256853221 212016946687737502173159979)
              ·
                refine ⟨318025420031606253259739969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212016946687737502173159979 318025420031606253259739969)
                ·
                  refine ⟨238519065023704689944804977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 318025420031606253259739969 238519065023704689944804977)
                  ·
                    refine ⟨178889298767778517458603733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 238519065023704689944804977 178889298767778517458603733)
                    ·
                      refine ⟨4192717939869809002936025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 178889298767778517458603733 4192717939869809002936025)
                      ·
                        rfl

theorem cell23_8165289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_8165289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165289 prefixEnd_8165289 := by exact prefixLift 8165289
  have htrace : WordTrace (prefixWord ++ tailWord_8165289) baseStart_8165289 baseEnd_8165289 := by
    simpa [prefixWord, tailWord_8165289, baseEnd_8165289] using wordTrace_append hprefix tailTrace_8165289
  have hstable : (prefixWord ++ tailWord_8165289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165289).length < 2 ^ (prefixWord ++ tailWord_8165289).sum := by decide
  have hdescent : baseEnd_8165289 < baseStart_8165289 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165323 : List Nat := [1, 1, 1, 1, 3, 4, 2, 2, 4, 1, 3]
def baseStart_8165323 : Nat := 118140960795 + 8165323 * 2 ^ 59
def prefixEnd_8165323 : Nat := 4983230072969 + 3 ^ 40 * 8165323 * 2
def baseEnd_8165323 : Nat := 4192735398212061869910869

theorem tailTrace_8165323 : CollatzResearch.WordTrace tailWord_8165323 prefixEnd_8165323 4192735398212061869910869 := by
  unfold tailWord_8165323
  simp only [CollatzResearch.WordTrace]
  refine ⟨297813796197436771989612623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198542530798291181326408415 297813796197436771989612623)
  ·
    refine ⟨446720694296155157984418935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297813796197436771989612623 446720694296155157984418935)
    ·
      refine ⟨670081041444232736976628403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446720694296155157984418935 670081041444232736976628403)
      ·
        refine ⟨1005121562166349105464942605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670081041444232736976628403 1005121562166349105464942605)
        ·
          refine ⟨376920585812380914549353477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1005121562166349105464942605 376920585812380914549353477)
          ·
            refine ⟨70672609839821421478003777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 376920585812380914549353477 70672609839821421478003777)
            ·
              refine ⟨53004457379866066108502833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70672609839821421478003777 53004457379866066108502833)
              ·
                refine ⟨39753343034899549581377125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53004457379866066108502833 39753343034899549581377125)
                ·
                  refine ⟨7453751819043665546508211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39753343034899549581377125 7453751819043665546508211)
                  ·
                    refine ⟨11180627728565498319762317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7453751819043665546508211 11180627728565498319762317)
                    ·
                      refine ⟨4192735398212061869910869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11180627728565498319762317 4192735398212061869910869)
                      ·
                        rfl

theorem cell23_8165323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4, 1, 3].length) (baseStart_8165323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165323 prefixEnd_8165323 := by exact prefixLift 8165323
  have htrace : WordTrace (prefixWord ++ tailWord_8165323) baseStart_8165323 baseEnd_8165323 := by
    simpa [prefixWord, tailWord_8165323, baseEnd_8165323] using wordTrace_append hprefix tailTrace_8165323
  have hstable : (prefixWord ++ tailWord_8165323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165323).length < 2 ^ (prefixWord ++ tailWord_8165323).sum := by decide
  have hdescent : baseEnd_8165323 < baseStart_8165323 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165324 : List Nat := [2, 2, 1, 4, 1, 3, 2, 3, 1, 2, 2]
def baseStart_8165324 : Nat := 118140960795 + 8165324 * 2 ^ 59
def prefixEnd_8165324 : Nat := 4983230072969 + 3 ^ 40 * 8165324 * 2
def baseEnd_8165324 : Nat := 4192735911692716365998365

theorem tailTrace_8165324 : CollatzResearch.WordTrace tailWord_8165324 prefixEnd_8165324 4192735911692716365998365 := by
  unfold tailWord_8165324
  simp only [CollatzResearch.WordTrace]
  refine ⟨148906916335216574580199513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198542555113622099440266017 148906916335216574580199513)
  ·
    refine ⟨111680187251412430935149635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148906916335216574580199513 111680187251412430935149635)
    ·
      refine ⟨167520280877118646402724453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111680187251412430935149635 167520280877118646402724453)
      ·
        refine ⟨31410052664459746200510835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167520280877118646402724453 31410052664459746200510835)
        ·
          refine ⟨47115078996689619300766253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31410052664459746200510835 47115078996689619300766253)
          ·
            refine ⟨17668154623758607237787345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47115078996689619300766253 17668154623758607237787345)
            ·
              refine ⟨13251115967818955428340509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17668154623758607237787345 13251115967818955428340509)
              ·
                refine ⟨4969168487932108285627691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13251115967818955428340509 4969168487932108285627691)
                ·
                  refine ⟨7453752731898162428441537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4969168487932108285627691 7453752731898162428441537)
                  ·
                    refine ⟨5590314548923621821331153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7453752731898162428441537 5590314548923621821331153)
                    ·
                      refine ⟨4192735911692716365998365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5590314548923621821331153 4192735911692716365998365)
                      ·
                        rfl

theorem cell23_8165324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_8165324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165324 prefixEnd_8165324 := by exact prefixLift 8165324
  have htrace : WordTrace (prefixWord ++ tailWord_8165324) baseStart_8165324 baseEnd_8165324 := by
    simpa [prefixWord, tailWord_8165324, baseEnd_8165324] using wordTrace_append hprefix tailTrace_8165324
  have hstable : (prefixWord ++ tailWord_8165324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165324).length < 2 ^ (prefixWord ++ tailWord_8165324).sum := by decide
  have hdescent : baseEnd_8165324 < baseStart_8165324 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165334 : List Nat := [5, 2, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_8165334 : Nat := 118140960795 + 8165334 * 2 ^ 59
def prefixEnd_8165334 : Nat := 4983230072969 + 3 ^ 40 * 8165334 * 2
def baseEnd_8165334 : Nat := 1397580348833087108957773

theorem tailTrace_8165334 : CollatzResearch.WordTrace tailWord_8165334 prefixEnd_8165334 1397580348833087108957773 := by
  unfold tailWord_8165334
  simp only [CollatzResearch.WordTrace]
  refine ⟨18613387337524807554266441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198542798266931280578842037 18613387337524807554266441)
  ·
    refine ⟨13960040503143605665699831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18613387337524807554266441 13960040503143605665699831)
    ·
      refine ⟨20940060754715408498549747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13960040503143605665699831 20940060754715408498549747)
      ·
        refine ⟨31410091132073112747824621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20940060754715408498549747 31410091132073112747824621)
        ·
          refine ⟨11778784174527417280434233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31410091132073112747824621 11778784174527417280434233)
          ·
            refine ⟨8834088130895562960325675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11778784174527417280434233 8834088130895562960325675)
            ·
              refine ⟨13251132196343344440488513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8834088130895562960325675 13251132196343344440488513)
              ·
                refine ⟨9938349147257508330366385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13251132196343344440488513 9938349147257508330366385)
                ·
                  refine ⟨7453761860443131247774789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9938349147257508330366385 7453761860443131247774789)
                  ·
                    refine ⟨1397580348833087108957773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7453761860443131247774789 1397580348833087108957773)
                    ·
                      rfl

theorem cell23_8165334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_8165334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165334 prefixEnd_8165334 := by exact prefixLift 8165334
  have htrace : WordTrace (prefixWord ++ tailWord_8165334) baseStart_8165334 baseEnd_8165334 := by
    simpa [prefixWord, tailWord_8165334, baseEnd_8165334] using wordTrace_append hprefix tailTrace_8165334
  have hstable : (prefixWord ++ tailWord_8165334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165334).length < 2 ^ (prefixWord ++ tailWord_8165334).sum := by decide
  have hdescent : baseEnd_8165334 < baseStart_8165334 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165376 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 4]
def baseStart_8165376 : Nat := 118140960795 + 8165376 * 2 ^ 59
def prefixEnd_8165376 : Nat := 4983230072969 + 3 ^ 40 * 8165376 * 2
def baseEnd_8165376 : Nat := 4192762612686750162548125

theorem tailTrace_8165376 : CollatzResearch.WordTrace tailWord_8165376 prefixEnd_8165376 4192762612686750162548125 := by
  unfold tailWord_8165376
  simp only [CollatzResearch.WordTrace]
  refine ⟨148907864633122381020645991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198543819510829841360861321 148907864633122381020645991)
  ·
    refine ⟨223361796949683571530968987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148907864633122381020645991 223361796949683571530968987)
    ·
      refine ⟨335042695424525357296453481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223361796949683571530968987 335042695424525357296453481)
      ·
        refine ⟨251282021568394017972340111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335042695424525357296453481 251282021568394017972340111)
        ·
          refine ⟨376923032352591026958510167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251282021568394017972340111 376923032352591026958510167)
          ·
            refine ⟨565384548528886540437765251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376923032352591026958510167 565384548528886540437765251)
            ·
              refine ⟨848076822793329810656647877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565384548528886540437765251 848076822793329810656647877)
              ·
                refine ⟨159014404273749339498121477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 848076822793329810656647877 159014404273749339498121477)
                ·
                  refine ⟨29815200801328001155897777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159014404273749339498121477 29815200801328001155897777)
                  ·
                    refine ⟨22361400600996000866923333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29815200801328001155897777 22361400600996000866923333)
                    ·
                      refine ⟨4192762612686750162548125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22361400600996000866923333 4192762612686750162548125)
                      ·
                        rfl

theorem cell23_8165376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_8165376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165376 prefixEnd_8165376 := by exact prefixLift 8165376
  have htrace : WordTrace (prefixWord ++ tailWord_8165376) baseStart_8165376 baseEnd_8165376 := by
    simpa [prefixWord, tailWord_8165376, baseEnd_8165376] using wordTrace_append hprefix tailTrace_8165376
  have hstable : (prefixWord ++ tailWord_8165376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165376).length < 2 ^ (prefixWord ++ tailWord_8165376).sum := by decide
  have hdescent : baseEnd_8165376 < baseStart_8165376 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165383 : List Nat := [1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 5]
def baseStart_8165383 : Nat := 118140960795 + 8165383 * 2 ^ 59
def prefixEnd_8165383 : Nat := 4983230072969 + 3 ^ 40 * 8165383 * 2
def baseEnd_8165383 : Nat := 4192766207051331635160593

theorem tailTrace_8165383 : CollatzResearch.WordTrace tailWord_8165383 prefixEnd_8165383 4192766207051331635160593 := by
  unfold tailWord_8165383
  simp only [CollatzResearch.WordTrace]
  refine ⟨297815984577219402236796803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198543989718146268157864535 297815984577219402236796803)
  ·
    refine ⟨446723976865829103355195205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297815984577219402236796803 446723976865829103355195205)
    ·
      refine ⟨83760745662342956879099101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 446723976865829103355195205 83760745662342956879099101)
      ·
        refine ⟨31410279623378608829662163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83760745662342956879099101 31410279623378608829662163)
        ·
          refine ⟨47115419435067913244493245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31410279623378608829662163 47115419435067913244493245)
          ·
            refine ⟨17668282288150467466684967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47115419435067913244493245 17668282288150467466684967)
            ·
              refine ⟨26502423432225701200027451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17668282288150467466684967 26502423432225701200027451)
              ·
                refine ⟨39753635148338551800041177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26502423432225701200027451 39753635148338551800041177)
                ·
                  refine ⟨29815226361253913850030883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39753635148338551800041177 29815226361253913850030883)
                  ·
                    refine ⟨44722839541880870775046325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29815226361253913850030883 44722839541880870775046325)
                    ·
                      refine ⟨4192766207051331635160593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44722839541880870775046325 4192766207051331635160593)
                      ·
                        rfl

theorem cell23_8165383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_8165383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165383 prefixEnd_8165383 := by exact prefixLift 8165383
  have htrace : WordTrace (prefixWord ++ tailWord_8165383) baseStart_8165383 baseEnd_8165383 := by
    simpa [prefixWord, tailWord_8165383, baseEnd_8165383] using wordTrace_append hprefix tailTrace_8165383
  have hstable : (prefixWord ++ tailWord_8165383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165383).length < 2 ^ (prefixWord ++ tailWord_8165383).sum := by decide
  have hdescent : baseEnd_8165383 < baseStart_8165383 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165423 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 4, 5, 2]
def baseStart_8165423 : Nat := 118140960795 + 8165423 * 2 ^ 59
def prefixEnd_8165423 : Nat := 4983230072969 + 3 ^ 40 * 8165423 * 2
def baseEnd_8165423 : Nat := 4192786746277511478660409

theorem tailTrace_8165423 : CollatzResearch.WordTrace tailWord_8165423 prefixEnd_8165423 4192786746277511478660409 := by
  unfold tailWord_8165423
  simp only [CollatzResearch.WordTrace]
  refine ⟨297817443497074489068252923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198544962331382992712168615 297817443497074489068252923)
  ·
    refine ⟨446726165245611733602379385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297817443497074489068252923 446726165245611733602379385)
    ·
      refine ⟨335044623934208800201784539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446726165245611733602379385 335044623934208800201784539)
      ·
        refine ⟨502566935901313200302676809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335044623934208800201784539 502566935901313200302676809)
        ·
          refine ⟨376925201925984900227007607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502566935901313200302676809 376925201925984900227007607)
          ·
            refine ⟨565387802888977350340511411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376925201925984900227007607 565387802888977350340511411)
            ·
              refine ⟨848081704333466025510767117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565387802888977350340511411 848081704333466025510767117)
              ·
                refine ⟨318030639125049759566537669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 848081704333466025510767117 318030639125049759566537669)
                ·
                  refine ⟨59630744835946829918725813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 318030639125049759566537669 59630744835946829918725813)
                  ·
                    refine ⟨5590382328370015304880545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59630744835946829918725813 5590382328370015304880545)
                    ·
                      refine ⟨4192786746277511478660409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5590382328370015304880545 4192786746277511478660409)
                      ·
                        rfl

theorem cell23_8165423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 5, 2].length) (baseStart_8165423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165423 prefixEnd_8165423 := by exact prefixLift 8165423
  have htrace : WordTrace (prefixWord ++ tailWord_8165423) baseStart_8165423 baseEnd_8165423 := by
    simpa [prefixWord, tailWord_8165423, baseEnd_8165423] using wordTrace_append hprefix tailTrace_8165423
  have hstable : (prefixWord ++ tailWord_8165423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165423).length < 2 ^ (prefixWord ++ tailWord_8165423).sum := by decide
  have hdescent : baseEnd_8165423 < baseStart_8165423 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165473 : List Nat := [1, 2, 3, 1, 1, 2, 1, 4, 1, 4, 3]
def baseStart_8165473 : Nat := 118140960795 + 8165473 * 2 ^ 59
def prefixEnd_8165473 : Nat := 4983230072969 + 3 ^ 40 * 8165473 * 2
def baseEnd_8165473 : Nat := 4192812420310236283035179

theorem tailTrace_8165473 : CollatzResearch.WordTrace tailWord_8165473 prefixEnd_8165473 4192812420310236283035179 := by
  unfold tailWord_8165473
  simp only [CollatzResearch.WordTrace]
  refine ⟨297819267146893347607573073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198546178097928898405048715 297819267146893347607573073)
  ·
    refine ⟨223364450360170010705679805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297819267146893347607573073 223364450360170010705679805)
    ·
      refine ⟨83761668885063754014629927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223364450360170010705679805 83761668885063754014629927)
      ·
        refine ⟨125642503327595631021944891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83761668885063754014629927 125642503327595631021944891)
        ·
          refine ⟨188463754991393446532917337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125642503327595631021944891 188463754991393446532917337)
          ·
            refine ⟨141347816243545084899688003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188463754991393446532917337 141347816243545084899688003)
            ·
              refine ⟨212021724365317627349532005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141347816243545084899688003 212021724365317627349532005)
              ·
                refine ⟨39754073318497055128037251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212021724365317627349532005 39754073318497055128037251)
                ·
                  refine ⟨59631109977745582692055877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39754073318497055128037251 59631109977745582692055877)
                  ·
                    refine ⟨11180833120827296754760477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59631109977745582692055877 11180833120827296754760477)
                    ·
                      refine ⟨4192812420310236283035179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11180833120827296754760477 4192812420310236283035179)
                      ·
                        rfl

theorem cell23_8165473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_8165473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165473 prefixEnd_8165473 := by exact prefixLift 8165473
  have htrace : WordTrace (prefixWord ++ tailWord_8165473) baseStart_8165473 baseEnd_8165473 := by
    simpa [prefixWord, tailWord_8165473, baseEnd_8165473] using wordTrace_append hprefix tailTrace_8165473
  have hstable : (prefixWord ++ tailWord_8165473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165473).length < 2 ^ (prefixWord ++ tailWord_8165473).sum := by decide
  have hdescent : baseEnd_8165473 < baseStart_8165473 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165490 : List Nat := [3, 2, 1, 2, 2, 3, 1, 1, 1, 4, 3]
def baseStart_8165490 : Nat := 118140960795 + 8165490 * 2 ^ 59
def prefixEnd_8165490 : Nat := 4983230072969 + 3 ^ 40 * 8165490 * 2
def baseEnd_8165490 : Nat := 4192821149481362716522601

theorem tailTrace_8165490 : CollatzResearch.WordTrace tailWord_8165490 prefixEnd_8165490 4192821149481362716522601 := by
  unfold tailWord_8165490
  simp only [CollatzResearch.WordTrace]
  refine ⟨74454971796957939877735481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198546591458554506340627949 74454971796957939877735481)
  ·
    refine ⟨55841228847718454908301611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74454971796957939877735481 55841228847718454908301611)
    ·
      refine ⟨83761843271577682362452417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55841228847718454908301611 83761843271577682362452417)
      ·
        refine ⟨62821382453683261771839313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83761843271577682362452417 62821382453683261771839313)
        ·
          refine ⟨47116036840262446328879485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62821382453683261771839313 47116036840262446328879485)
          ·
            refine ⟨17668513815098417373329807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47116036840262446328879485 17668513815098417373329807)
            ·
              refine ⟨26502770722647626059994711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17668513815098417373329807 26502770722647626059994711)
              ·
                refine ⟨39754156083971439089992067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26502770722647626059994711 39754156083971439089992067)
                ·
                  refine ⟨59631234125957158634988101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39754156083971439089992067 59631234125957158634988101)
                  ·
                    refine ⟨11180856398616967244060269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59631234125957158634988101 11180856398616967244060269)
                    ·
                      refine ⟨4192821149481362716522601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11180856398616967244060269 4192821149481362716522601)
                      ·
                        rfl

theorem cell23_8165490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_8165490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165490 prefixEnd_8165490 := by exact prefixLift 8165490
  have htrace : WordTrace (prefixWord ++ tailWord_8165490) baseStart_8165490 baseEnd_8165490 := by
    simpa [prefixWord, tailWord_8165490, baseEnd_8165490] using wordTrace_append hprefix tailTrace_8165490
  have hstable : (prefixWord ++ tailWord_8165490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165490).length < 2 ^ (prefixWord ++ tailWord_8165490).sum := by decide
  have hdescent : baseEnd_8165490 < baseStart_8165490 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165497 : List Nat := [1, 2, 1, 3, 4, 1, 1, 5, 1, 4]
def baseStart_8165497 : Nat := 118140960795 + 8165497 * 2 ^ 59
def prefixEnd_8165497 : Nat := 4983230072969 + 3 ^ 40 * 8165497 * 2
def baseEnd_8165497 : Nat := 1397608247948648063045023

theorem tailTrace_8165497 : CollatzResearch.WordTrace tailWord_8165497 prefixEnd_8165497 1397608247948648063045023 := by
  unfold tailWord_8165497
  simp only [CollatzResearch.WordTrace]
  refine ⟨297820142498806399706446745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198546761665870933137631163 297820142498806399706446745)
  ·
    refine ⟨223365106874104799779835059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297820142498806399706446745 223365106874104799779835059)
    ·
      refine ⟨335047660311157199669752589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223365106874104799779835059 335047660311157199669752589)
      ·
        refine ⟨125642872616683949876157221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335047660311157199669752589 125642872616683949876157221)
        ·
          refine ⟨23558038615628240601779479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125642872616683949876157221 23558038615628240601779479)
          ·
            refine ⟨35337057923442360902669219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23558038615628240601779479 35337057923442360902669219)
            ·
              refine ⟨53005586885163541354003829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35337057923442360902669219 53005586885163541354003829)
              ·
                refine ⟨4969273770484082001937859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53005586885163541354003829 4969273770484082001937859)
                ·
                  refine ⟨7453910655726123002906789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4969273770484082001937859 7453910655726123002906789)
                  ·
                    refine ⟨1397608247948648063045023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7453910655726123002906789 1397608247948648063045023)
                    ·
                      rfl

theorem cell23_8165497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5, 1, 4].length) (baseStart_8165497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165497 prefixEnd_8165497 := by exact prefixLift 8165497
  have htrace : WordTrace (prefixWord ++ tailWord_8165497) baseStart_8165497 baseEnd_8165497 := by
    simpa [prefixWord, tailWord_8165497, baseEnd_8165497] using wordTrace_append hprefix tailTrace_8165497
  have hstable : (prefixWord ++ tailWord_8165497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165497).length < 2 ^ (prefixWord ++ tailWord_8165497).sum := by decide
  have hdescent : baseEnd_8165497 < baseStart_8165497 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165527 : List Nat := [1, 1, 3, 3, 4, 1, 3, 1, 6]
def baseStart_8165527 : Nat := 118140960795 + 8165527 * 2 ^ 59
def prefixEnd_8165527 : Nat := 4983230072969 + 3 ^ 40 * 8165527 * 2
def baseEnd_8165527 : Nat := 465871127585064341306659

theorem tailTrace_8165527 : CollatzResearch.WordTrace tailWord_8165527 prefixEnd_8165527 465871127585064341306659 := by
  unfold tailWord_8165527
  simp only [CollatzResearch.WordTrace]
  refine ⟨297821236688697714830038835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198547491125798476553359223 297821236688697714830038835)
  ·
    refine ⟨446731855033046572245058253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297821236688697714830038835 446731855033046572245058253)
    ·
      refine ⟨167524445637392464591896845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446731855033046572245058253 167524445637392464591896845)
      ·
        refine ⟨62821667114022174221961317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167524445637392464591896845 62821667114022174221961317)
        ·
          refine ⟨11779062583879157666617747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62821667114022174221961317 11779062583879157666617747)
          ·
            refine ⟨17668593875818736499926621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11779062583879157666617747 17668593875818736499926621)
            ·
              refine ⟨6625722703432026187472483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17668593875818736499926621 6625722703432026187472483)
              ·
                refine ⟨9938584055148039281208725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6625722703432026187472483 9938584055148039281208725)
                ·
                  refine ⟨465871127585064341306659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9938584055148039281208725 465871127585064341306659)
                  ·
                    rfl

theorem cell23_8165527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 6].length) (baseStart_8165527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165527 prefixEnd_8165527 := by exact prefixLift 8165527
  have htrace : WordTrace (prefixWord ++ tailWord_8165527) baseStart_8165527 baseEnd_8165527 := by
    simpa [prefixWord, tailWord_8165527, baseEnd_8165527] using wordTrace_append hprefix tailTrace_8165527
  have hstable : (prefixWord ++ tailWord_8165527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165527).length < 2 ^ (prefixWord ++ tailWord_8165527).sum := by decide
  have hdescent : baseEnd_8165527 < baseStart_8165527 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165537 : List Nat := [1, 2, 3, 3, 1, 2, 2, 2, 3, 1, 3]
def baseStart_8165537 : Nat := 118140960795 + 8165537 * 2 ^ 59
def prefixEnd_8165537 : Nat := 4983230072969 + 3 ^ 40 * 8165537 * 2
def baseEnd_8165537 : Nat := 4192845283072124032634885

theorem tailTrace_8165537 : CollatzResearch.WordTrace tailWord_8165537 prefixEnd_8165537 4192845283072124032634885 := by
  unfold tailWord_8165537
  simp only [CollatzResearch.WordTrace]
  refine ⟨297821601418661486537902865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198547734279107657691935243 297821601418661486537902865)
  ·
    refine ⟨223366201063996114903427149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297821601418661486537902865 223366201063996114903427149)
    ·
      refine ⟨83762325398998543088785181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223366201063996114903427149 83762325398998543088785181)
      ·
        refine ⟨31410872024624453658294443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83762325398998543088785181 31410872024624453658294443)
        ·
          refine ⟨47116308036936680487441665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31410872024624453658294443 47116308036936680487441665)
          ·
            refine ⟨35337231027702510365581249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47116308036936680487441665 35337231027702510365581249)
            ·
              refine ⟨26502923270776882774185937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35337231027702510365581249 26502923270776882774185937)
              ·
                refine ⟨19877192453082662080639453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26502923270776882774185937 19877192453082662080639453)
                ·
                  refine ⟨7453947169905998280239795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19877192453082662080639453 7453947169905998280239795)
                  ·
                    refine ⟨11180920754858997420359693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7453947169905998280239795 11180920754858997420359693)
                    ·
                      refine ⟨4192845283072124032634885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11180920754858997420359693 4192845283072124032634885)
                      ·
                        rfl

theorem cell23_8165537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_8165537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165537 prefixEnd_8165537 := by exact prefixLift 8165537
  have htrace : WordTrace (prefixWord ++ tailWord_8165537) baseStart_8165537 baseEnd_8165537 := by
    simpa [prefixWord, tailWord_8165537, baseEnd_8165537] using wordTrace_append hprefix tailTrace_8165537
  have hstable : (prefixWord ++ tailWord_8165537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165537).length < 2 ^ (prefixWord ++ tailWord_8165537).sum := by decide
  have hdescent : baseEnd_8165537 < baseStart_8165537 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165560 : List Nat := [2, 1, 2, 1, 2, 1, 3, 5, 1, 1, 4]
def baseStart_8165560 : Nat := 118140960795 + 8165560 * 2 ^ 59
def prefixEnd_8165560 : Nat := 4983230072969 + 3 ^ 40 * 8165560 * 2
def baseEnd_8165560 : Nat := 4192857093127177442647279

theorem tailTrace_8165560 : CollatzResearch.WordTrace tailWord_8165560 prefixEnd_8165560 4192857093127177442647279 := by
  unfold tailWord_8165560
  simp only [CollatzResearch.WordTrace]
  refine ⟨148911220148789080732995067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198548293531718774310660089 148911220148789080732995067)
  ·
    refine ⟨223366830223183621099492601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148911220148789080732995067 223366830223183621099492601)
    ·
      refine ⟨167525122667387715824619451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223366830223183621099492601 167525122667387715824619451)
      ·
        refine ⟨251287684001081573736929177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167525122667387715824619451 251287684001081573736929177)
        ·
          refine ⟨188465763000811180302696883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251287684001081573736929177 188465763000811180302696883)
          ·
            refine ⟨282698644501216770454045325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188465763000811180302696883 282698644501216770454045325)
            ·
              refine ⟨106011991687956288920266997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282698644501216770454045325 106011991687956288920266997)
              ·
                refine ⟨9938624220745902086275031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106011991687956288920266997 9938624220745902086275031)
                ·
                  refine ⟨14907936331118853129412547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9938624220745902086275031 14907936331118853129412547)
                  ·
                    refine ⟨22361904496678279694118821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14907936331118853129412547 22361904496678279694118821)
                    ·
                      refine ⟨4192857093127177442647279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22361904496678279694118821 4192857093127177442647279)
                      ·
                        rfl

theorem cell23_8165560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 1, 1, 4].length) (baseStart_8165560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165560 prefixEnd_8165560 := by exact prefixLift 8165560
  have htrace : WordTrace (prefixWord ++ tailWord_8165560) baseStart_8165560 baseEnd_8165560 := by
    simpa [prefixWord, tailWord_8165560, baseEnd_8165560] using wordTrace_append hprefix tailTrace_8165560
  have hstable : (prefixWord ++ tailWord_8165560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165560).length < 2 ^ (prefixWord ++ tailWord_8165560).sum := by decide
  have hdescent : baseEnd_8165560 < baseStart_8165560 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165564 : List Nat := [2, 2, 2, 3, 3, 1, 1, 2, 2, 3, 2]
def baseStart_8165564 : Nat := 118140960795 + 8165564 * 2 ^ 59
def prefixEnd_8165564 : Nat := 4983230072969 + 3 ^ 40 * 8165564 * 2
def baseEnd_8165564 : Nat := 4192859147049795426997261

theorem tailTrace_8165564 : CollatzResearch.WordTrace tailWord_8165564 prefixEnd_8165564 4192859147049795426997261 := by
  unfold tailWord_8165564
  simp only [CollatzResearch.WordTrace]
  refine ⟨148911293094781835074567873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198548390793042446766090497 148911293094781835074567873)
  ·
    refine ⟨111683469821086376305925905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148911293094781835074567873 111683469821086376305925905)
    ·
      refine ⟨83762602365814782229444429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111683469821086376305925905 83762602365814782229444429)
      ·
        refine ⟨31410975887180543336041661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83762602365814782229444429 31410975887180543336041661)
        ·
          refine ⟨11779115957692703751015623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31410975887180543336041661 11779115957692703751015623)
          ·
            refine ⟨17668673936539055626523435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11779115957692703751015623 17668673936539055626523435)
            ·
              refine ⟨26503010904808583439785153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17668673936539055626523435 26503010904808583439785153)
              ·
                refine ⟨19877258178606437579838865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26503010904808583439785153 19877258178606437579838865)
                ·
                  refine ⟨14907943633954828184879149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19877258178606437579838865 14907943633954828184879149)
                  ·
                    refine ⟨5590478862733060569329681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14907943633954828184879149 5590478862733060569329681)
                    ·
                      refine ⟨4192859147049795426997261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5590478862733060569329681 4192859147049795426997261)
                      ·
                        rfl

theorem cell23_8165564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_8165564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165564 prefixEnd_8165564 := by exact prefixLift 8165564
  have htrace : WordTrace (prefixWord ++ tailWord_8165564) baseStart_8165564 baseEnd_8165564 := by
    simpa [prefixWord, tailWord_8165564, baseEnd_8165564] using wordTrace_append hprefix tailTrace_8165564
  have hstable : (prefixWord ++ tailWord_8165564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165564).length < 2 ^ (prefixWord ++ tailWord_8165564).sum := by decide
  have hdescent : baseEnd_8165564 < baseStart_8165564 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165573 : List Nat := [1, 3, 1, 1, 1, 1, 5, 2, 1, 1, 6]
def baseStart_8165573 : Nat := 118140960795 + 8165573 * 2 ^ 59
def prefixEnd_8165573 : Nat := 4983230072969 + 3 ^ 40 * 8165573 * 2
def baseEnd_8165573 : Nat := 4192863768375685891784719

theorem tailTrace_8165573 : CollatzResearch.WordTrace tailWord_8165573 prefixEnd_8165573 4192863768375685891784719 := by
  unfold tailWord_8165573
  simp only [CollatzResearch.WordTrace]
  refine ⟨297822914446531064686213373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198548609631020709790808915 297822914446531064686213373)
  ·
    refine ⟨111683592917449149257330015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297822914446531064686213373 111683592917449149257330015)
    ·
      refine ⟨167525389376173723885995023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111683592917449149257330015 167525389376173723885995023)
      ·
        refine ⟨251288084064260585828992535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167525389376173723885995023 251288084064260585828992535)
        ·
          refine ⟨376932126096390878743488803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251288084064260585828992535 376932126096390878743488803)
          ·
            refine ⟨565398189144586318115233205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376932126096390878743488803 565398189144586318115233205)
            ·
              refine ⟨53006080232304967323303113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 565398189144586318115233205 53006080232304967323303113)
              ·
                refine ⟨39754560174228725492477335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53006080232304967323303113 39754560174228725492477335)
                ·
                  refine ⟨59631840261343088238716003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39754560174228725492477335 59631840261343088238716003)
                  ·
                    refine ⟨89447760392014632358074005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59631840261343088238716003 89447760392014632358074005)
                    ·
                      refine ⟨4192863768375685891784719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89447760392014632358074005 4192863768375685891784719)
                      ·
                        rfl

theorem cell23_8165573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_8165573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165573 prefixEnd_8165573 := by exact prefixLift 8165573
  have htrace : WordTrace (prefixWord ++ tailWord_8165573) baseStart_8165573 baseEnd_8165573 := by
    simpa [prefixWord, tailWord_8165573, baseEnd_8165573] using wordTrace_append hprefix tailTrace_8165573
  have hstable : (prefixWord ++ tailWord_8165573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165573).length < 2 ^ (prefixWord ++ tailWord_8165573).sum := by decide
  have hdescent : baseEnd_8165573 < baseStart_8165573 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165577 : List Nat := [1, 2, 1, 1, 2, 1, 1, 7, 3, 2, 2]
def baseStart_8165577 : Nat := 118140960795 + 8165577 * 2 ^ 59
def prefixEnd_8165577 : Nat := 4983230072969 + 3 ^ 40 * 8165577 * 2
def baseEnd_8165577 : Nat := 4192865822298303876134701

theorem tailTrace_8165577 : CollatzResearch.WordTrace tailWord_8165577 prefixEnd_8165577 4192865822298303876134701 := by
  unfold tailWord_8165577
  simp only [CollatzResearch.WordTrace]
  refine ⟨297823060338516573369358985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198548706892344382246239323 297823060338516573369358985)
  ·
    refine ⟨223367295253887430027019239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297823060338516573369358985 223367295253887430027019239)
    ·
      refine ⟨335050942880831145040528859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223367295253887430027019239 335050942880831145040528859)
      ·
        refine ⟨502576414321246717560793289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335050942880831145040528859 502576414321246717560793289)
        ·
          refine ⟨376932310740935038170594967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502576414321246717560793289 376932310740935038170594967)
          ·
            refine ⟨565398466111402557255892451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376932310740935038170594967 565398466111402557255892451)
            ·
              refine ⟨848097699167103835883838677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565398466111402557255892451 848097699167103835883838677)
              ·
                refine ⟨19877289824228996153527469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 848097699167103835883838677 19877289824228996153527469)
                ·
                  refine ⟨7453983684085873557572801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19877289824228996153527469 7453983684085873557572801)
                  ·
                    refine ⟨5590487763064405168179601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7453983684085873557572801 5590487763064405168179601)
                    ·
                      refine ⟨4192865822298303876134701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5590487763064405168179601 4192865822298303876134701)
                      ·
                        rfl

theorem cell23_8165577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3, 2, 2].length) (baseStart_8165577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165577 prefixEnd_8165577 := by exact prefixLift 8165577
  have htrace : WordTrace (prefixWord ++ tailWord_8165577) baseStart_8165577 baseEnd_8165577 := by
    simpa [prefixWord, tailWord_8165577, baseEnd_8165577] using wordTrace_append hprefix tailTrace_8165577
  have hstable : (prefixWord ++ tailWord_8165577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165577).length < 2 ^ (prefixWord ++ tailWord_8165577).sum := by decide
  have hdescent : baseEnd_8165577 < baseStart_8165577 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165583 : List Nat := [1, 1, 2, 1, 1, 3, 6, 8]
def baseStart_8165583 : Nat := 118140960795 + 8165583 * 2 ^ 59
def prefixEnd_8165583 : Nat := 4983230072969 + 3 ^ 40 * 8165583 * 2
def baseEnd_8165583 : Nat := 155291440858601142691099

theorem tailTrace_8165583 : CollatzResearch.WordTrace tailWord_8165583 prefixEnd_8165583 155291440858601142691099 := by
  unfold tailWord_8165583
  simp only [CollatzResearch.WordTrace]
  refine ⟨297823279176494836394077403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198548852784329890929384935 297823279176494836394077403)
  ·
    refine ⟨446734918764742254591116105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297823279176494836394077403 446734918764742254591116105)
    ·
      refine ⟨335051189073556690943337079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446734918764742254591116105 335051189073556690943337079)
      ·
        refine ⟨502576783610335036415005619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335051189073556690943337079 502576783610335036415005619)
        ·
          refine ⟨753865175415502554622508429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502576783610335036415005619 753865175415502554622508429)
          ·
            refine ⟨282699440780813457983440661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 753865175415502554622508429 282699440780813457983440661)
            ·
              refine ⟨13251536286600630842973781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 282699440780813457983440661 13251536286600630842973781)
              ·
                refine ⟨155291440858601142691099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13251536286600630842973781 155291440858601142691099)
                ·
                  rfl

theorem cell23_8165583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 8].length) (baseStart_8165583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165583 prefixEnd_8165583 := by exact prefixLift 8165583
  have htrace : WordTrace (prefixWord ++ tailWord_8165583) baseStart_8165583 baseEnd_8165583 := by
    simpa [prefixWord, tailWord_8165583, baseEnd_8165583] using wordTrace_append hprefix tailTrace_8165583
  have hstable : (prefixWord ++ tailWord_8165583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165583).length < 2 ^ (prefixWord ++ tailWord_8165583).sum := by decide
  have hdescent : baseEnd_8165583 < baseStart_8165583 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165607 : List Nat := [1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_8165607 : Nat := 118140960795 + 8165607 * 2 ^ 59
def prefixEnd_8165607 : Nat := 4983230072969 + 3 ^ 40 * 8165607 * 2
def baseEnd_8165607 : Nat := 4192881226717938758759563

theorem tailTrace_8165607 : CollatzResearch.WordTrace tailWord_8165607 prefixEnd_8165607 4192881226717938758759563 := by
  unfold tailWord_8165607
  simp only [CollatzResearch.WordTrace]
  refine ⟨297824154528407888492951075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198549436352271925661967383 297824154528407888492951075)
  ·
    refine ⟨446736231792611832739426613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297824154528407888492951075 446736231792611832739426613)
    ·
      refine ⟨41881521730557359319321245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 446736231792611832739426613 41881521730557359319321245)
      ·
        refine ⟨15705570648959009744745467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41881521730557359319321245 15705570648959009744745467)
        ·
          refine ⟨23558355973438514617118201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15705570648959009744745467 23558355973438514617118201)
          ·
            refine ⟨17668766980078885962838651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23558355973438514617118201 17668766980078885962838651)
            ·
              refine ⟨26503150470118328944257977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17668766980078885962838651 26503150470118328944257977)
              ·
                refine ⟨19877362852588746708193483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26503150470118328944257977 19877362852588746708193483)
                ·
                  refine ⟨29816044278883120062290225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19877362852588746708193483 29816044278883120062290225)
                  ·
                    refine ⟨22362033209162340046717669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29816044278883120062290225 22362033209162340046717669)
                    ·
                      refine ⟨4192881226717938758759563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22362033209162340046717669 4192881226717938758759563)
                      ·
                        rfl

theorem cell23_8165607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_8165607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165607 prefixEnd_8165607 := by exact prefixLift 8165607
  have htrace : WordTrace (prefixWord ++ tailWord_8165607) baseStart_8165607 baseEnd_8165607 := by
    simpa [prefixWord, tailWord_8165607, baseEnd_8165607] using wordTrace_append hprefix tailTrace_8165607
  have hstable : (prefixWord ++ tailWord_8165607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165607).length < 2 ^ (prefixWord ++ tailWord_8165607).sum := by decide
  have hdescent : baseEnd_8165607 < baseStart_8165607 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165628 : List Nat := [2, 2, 2, 1, 4, 1, 4, 2, 1, 2, 2]
def baseStart_8165628 : Nat := 118140960795 + 8165628 * 2 ^ 59
def prefixEnd_8165628 : Nat := 4983230072969 + 3 ^ 40 * 8165628 * 2
def baseEnd_8165628 : Nat := 4192892009811683176596967

theorem tailTrace_8165628 : CollatzResearch.WordTrace tailWord_8165628 prefixEnd_8165628 4192892009811683176596967 := by
  unfold tailWord_8165628
  simp only [CollatzResearch.WordTrace]
  refine ⟨148912460230665904539732769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198549946974221206052977025 148912460230665904539732769)
  ·
    refine ⟨111684345172999428404799577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148912460230665904539732769 111684345172999428404799577)
    ·
      refine ⟨83763258879749571303599683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111684345172999428404799577 83763258879749571303599683)
      ·
        refine ⟨125644888319624356955399525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83763258879749571303599683 125644888319624356955399525)
        ·
          refine ⟨23558416559929566929137411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125644888319624356955399525 23558416559929566929137411)
          ·
            refine ⟨35337624839894350393706117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23558416559929566929137411 35337624839894350393706117)
            ·
              refine ⟨6625804657480190698819897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35337624839894350393706117 6625804657480190698819897)
              ·
                refine ⟨4969353493110143024114923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6625804657480190698819897 4969353493110143024114923)
                ·
                  refine ⟨7454030239665214536172385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4969353493110143024114923 7454030239665214536172385)
                  ·
                    refine ⟨5590522679748910902129289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7454030239665214536172385 5590522679748910902129289)
                    ·
                      refine ⟨4192892009811683176596967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5590522679748910902129289 4192892009811683176596967)
                      ·
                        rfl

theorem cell23_8165628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2, 1, 2, 2].length) (baseStart_8165628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165628 prefixEnd_8165628 := by exact prefixLift 8165628
  have htrace : WordTrace (prefixWord ++ tailWord_8165628) baseStart_8165628 baseEnd_8165628 := by
    simpa [prefixWord, tailWord_8165628, baseEnd_8165628] using wordTrace_append hprefix tailTrace_8165628
  have hstable : (prefixWord ++ tailWord_8165628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165628).length < 2 ^ (prefixWord ++ tailWord_8165628).sum := by decide
  have hdescent : baseEnd_8165628 < baseStart_8165628 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165630 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 1, 9]
def baseStart_8165630 : Nat := 118140960795 + 8165630 * 2 ^ 59
def prefixEnd_8165630 : Nat := 4983230072969 + 3 ^ 40 * 8165630 * 2
def baseEnd_8165630 : Nat := 1397631012257664056257319

theorem tailTrace_8165630 : CollatzResearch.WordTrace tailWord_8165630 prefixEnd_8165630 1397631012257664056257319 := by
  unfold tailWord_8165630
  simp only [CollatzResearch.WordTrace]
  refine ⟨37228124175915570427629793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198549995604883042280692229 37228124175915570427629793)
  ·
    refine ⟨27921093131936677820722345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37228124175915570427629793 27921093131936677820722345)
    ·
      refine ⟨20940819848952508365541759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27921093131936677820722345 20940819848952508365541759)
      ·
        refine ⟨31411229773428762548312639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20940819848952508365541759 31411229773428762548312639)
        ·
          refine ⟨47116844660143143822468959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31411229773428762548312639 47116844660143143822468959)
          ·
            refine ⟨70675266990214715733703439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47116844660143143822468959 70675266990214715733703439)
            ·
              refine ⟨106012900485322073600555159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70675266990214715733703439 106012900485322073600555159)
              ·
                refine ⟨159019350727983110400832739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106012900485322073600555159 159019350727983110400832739)
                ·
                  refine ⟨238529026091974665601249109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159019350727983110400832739 238529026091974665601249109)
                  ·
                    refine ⟨1397631012257664056257319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 238529026091974665601249109 1397631012257664056257319)
                    ·
                      rfl

theorem cell23_8165630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_8165630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165630 prefixEnd_8165630 := by exact prefixLift 8165630
  have htrace : WordTrace (prefixWord ++ tailWord_8165630) baseStart_8165630 baseEnd_8165630 := by
    simpa [prefixWord, tailWord_8165630, baseEnd_8165630] using wordTrace_append hprefix tailTrace_8165630
  have hstable : (prefixWord ++ tailWord_8165630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165630).length < 2 ^ (prefixWord ++ tailWord_8165630).sum := by decide
  have hdescent : baseEnd_8165630 < baseStart_8165630 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165667 : List Nat := [1, 1, 1, 4, 2, 2, 1, 4, 1, 4, 2]
def baseStart_8165667 : Nat := 118140960795 + 8165667 * 2 ^ 59
def prefixEnd_8165667 : Nat := 4983230072969 + 3 ^ 40 * 8165667 * 2
def baseEnd_8165667 : Nat := 4192912035557208524009287

theorem tailTrace_8165667 : CollatzResearch.WordTrace tailWord_8165667 prefixEnd_8165667 4192912035557208524009287 := by
  unfold tailWord_8165667
  simp only [CollatzResearch.WordTrace]
  refine ⟨297826342908190518740135255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198550895272127012493423503 297826342908190518740135255)
  ·
    refine ⟨446739514362285778110202883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297826342908190518740135255 446739514362285778110202883)
    ·
      refine ⟨670109271543428667165304325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446739514362285778110202883 670109271543428667165304325)
      ·
        refine ⟨125645488414392875093494561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 670109271543428667165304325 125645488414392875093494561)
        ·
          refine ⟨94234116310794656320120921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125645488414392875093494561 94234116310794656320120921)
          ·
            refine ⟨70675587233095992240090691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94234116310794656320120921 70675587233095992240090691)
            ·
              refine ⟨106013380849643988360136037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70675587233095992240090691 106013380849643988360136037)
              ·
                refine ⟨19877508909308247817525507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106013380849643988360136037 19877508909308247817525507)
                ·
                  refine ⟨29816263363962371726288261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19877508909308247817525507 29816263363962371726288261)
                  ·
                    refine ⟨5590549380742944698679049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29816263363962371726288261 5590549380742944698679049)
                    ·
                      refine ⟨4192912035557208524009287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5590549380742944698679049 4192912035557208524009287)
                      ·
                        rfl

theorem cell23_8165667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 4, 2].length) (baseStart_8165667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165667 prefixEnd_8165667 := by exact prefixLift 8165667
  have htrace : WordTrace (prefixWord ++ tailWord_8165667) baseStart_8165667 baseEnd_8165667 := by
    simpa [prefixWord, tailWord_8165667, baseEnd_8165667] using wordTrace_append hprefix tailTrace_8165667
  have hstable : (prefixWord ++ tailWord_8165667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165667).length < 2 ^ (prefixWord ++ tailWord_8165667).sum := by decide
  have hdescent : baseEnd_8165667 < baseStart_8165667 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165690 : List Nat := [3, 1, 1, 1, 4, 2, 1, 3, 7]
def baseStart_8165690 : Nat := 118140960795 + 8165690 * 2 ^ 59
def prefixEnd_8165690 : Nat := 4983230072969 + 3 ^ 40 * 8165690 * 2
def baseEnd_8165690 : Nat := 465880427290251326002409

theorem tailTrace_8165690 : CollatzResearch.WordTrace tailWord_8165690 prefixEnd_8165690 465880427290251326002409 := by
  unfold tailWord_8165690
  simp only [CollatzResearch.WordTrace]
  refine ⟨74456795446776798417055631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198551454524738129112148349 74456795446776798417055631)
  ·
    refine ⟨111685193170165197625583447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74456795446776798417055631 111685193170165197625583447)
    ·
      refine ⟨167527789755247796438375171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111685193170165197625583447 167527789755247796438375171)
      ·
        refine ⟨251291684632871694657562757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167527789755247796438375171 251291684632871694657562757)
        ·
          refine ⟨47117190868663442748293017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251291684632871694657562757 47117190868663442748293017)
          ·
            refine ⟨35337893151497582061219763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47117190868663442748293017 35337893151497582061219763)
            ·
              refine ⟨53006839727246373091829645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35337893151497582061219763 53006839727246373091829645)
              ·
                refine ⟨19877564897717389909436117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53006839727246373091829645 19877564897717389909436117)
                ·
                  refine ⟨465880427290251326002409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19877564897717389909436117 465880427290251326002409)
                  ·
                    rfl

theorem cell23_8165690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 7].length) (baseStart_8165690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165690 prefixEnd_8165690 := by exact prefixLift 8165690
  have htrace : WordTrace (prefixWord ++ tailWord_8165690) baseStart_8165690 baseEnd_8165690 := by
    simpa [prefixWord, tailWord_8165690, baseEnd_8165690] using wordTrace_append hprefix tailTrace_8165690
  have hstable : (prefixWord ++ tailWord_8165690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165690).length < 2 ^ (prefixWord ++ tailWord_8165690).sum := by decide
  have hdescent : baseEnd_8165690 < baseStart_8165690 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165767 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 5, 4]
def baseStart_8165767 : Nat := 118140960795 + 8165767 * 2 ^ 59
def prefixEnd_8165767 : Nat := 4983230072969 + 3 ^ 40 * 8165767 * 2
def baseEnd_8165767 : Nat := 1397654461207552710919609

theorem tailTrace_8165767 : CollatzResearch.WordTrace tailWord_8165767 prefixEnd_8165767 1397654461207552710919609 := by
  unfold tailWord_8165767
  simp only [CollatzResearch.WordTrace]
  refine ⟨297829990207828235818775555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198553326805218823879183703 297829990207828235818775555)
  ·
    refine ⟨446744985311742353728163333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297829990207828235818775555 446744985311742353728163333)
    ·
      refine ⟨83764684745951691324030625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 446744985311742353728163333 83764684745951691324030625)
      ·
        refine ⟨62823513559463768493022969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83764684745951691324030625 62823513559463768493022969)
        ·
          refine ⟨47117635169597826369767227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62823513559463768493022969 47117635169597826369767227)
          ·
            refine ⟨70676452754396739554650841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47117635169597826369767227 70676452754396739554650841)
            ·
              refine ⟨53007339565797554665988131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70676452754396739554650841 53007339565797554665988131)
              ·
                refine ⟨79511009348696331998982197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53007339565797554665988131 79511009348696331998982197)
                ·
                  refine ⟨7454157126440281124904581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79511009348696331998982197 7454157126440281124904581)
                  ·
                    refine ⟨1397654461207552710919609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7454157126440281124904581 1397654461207552710919609)
                    ·
                      rfl

theorem cell23_8165767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_8165767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165767 prefixEnd_8165767 := by exact prefixLift 8165767
  have htrace : WordTrace (prefixWord ++ tailWord_8165767) baseStart_8165767 baseEnd_8165767 := by
    simpa [prefixWord, tailWord_8165767, baseEnd_8165767] using wordTrace_append hprefix tailTrace_8165767
  have hstable : (prefixWord ++ tailWord_8165767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165767).length < 2 ^ (prefixWord ++ tailWord_8165767).sum := by decide
  have hdescent : baseEnd_8165767 < baseStart_8165767 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165774 : List Nat := [4, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4]
def baseStart_8165774 : Nat := 118140960795 + 8165774 * 2 ^ 59
def prefixEnd_8165774 : Nat := 4983230072969 + 3 ^ 40 * 8165774 * 2
def baseEnd_8165774 : Nat := 4192966977987239605371295

theorem tailTrace_8165774 : CollatzResearch.WordTrace tailWord_8165774 prefixEnd_8165774 4192966977987239605371295 := by
  unfold tailWord_8165774
  simp only [CollatzResearch.WordTrace]
  refine ⟨37228780689850359501785047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198553497012535250676186917 37228780689850359501785047)
  ·
    refine ⟨55843171034775539252677571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37228780689850359501785047 55843171034775539252677571)
    ·
      refine ⟨83764756552163308879016357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55843171034775539252677571 83764756552163308879016357)
      ·
        refine ⟨15705891853530620414815567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83764756552163308879016357 15705891853530620414815567)
        ·
          refine ⟨23558837780295930622223351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15705891853530620414815567 23558837780295930622223351)
          ·
            refine ⟨35338256670443895933335027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23558837780295930622223351 35338256670443895933335027)
            ·
              refine ⟨53007385005665843900002541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35338256670443895933335027 53007385005665843900002541)
              ·
                refine ⟨19877769377124691462500953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53007385005665843900002541 19877769377124691462500953)
                ·
                  refine ⟨14908327032843518596875715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19877769377124691462500953 14908327032843518596875715)
                  ·
                    refine ⟨22362490549265277895313573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14908327032843518596875715 22362490549265277895313573)
                    ·
                      refine ⟨4192966977987239605371295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22362490549265277895313573 4192966977987239605371295)
                      ·
                        rfl

theorem cell23_8165774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_8165774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165774 prefixEnd_8165774 := by exact prefixLift 8165774
  have htrace : WordTrace (prefixWord ++ tailWord_8165774) baseStart_8165774 baseEnd_8165774 := by
    simpa [prefixWord, tailWord_8165774, baseEnd_8165774] using wordTrace_append hprefix tailTrace_8165774
  have hstable : (prefixWord ++ tailWord_8165774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165774).length < 2 ^ (prefixWord ++ tailWord_8165774).sum := by decide
  have hdescent : baseEnd_8165774 < baseStart_8165774 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165794 : List Nat := [3, 3, 1, 2, 1, 1, 1, 4, 2, 2, 3]
def baseStart_8165794 : Nat := 118140960795 + 8165794 * 2 ^ 59
def prefixEnd_8165794 : Nat := 4983230072969 + 3 ^ 40 * 8165794 * 2
def baseEnd_8165794 : Nat := 4192977247600329527121203

theorem tailTrace_8165794 : CollatzResearch.WordTrace tailWord_8165794 prefixEnd_8165794 4192977247600329527121203 := by
  unfold tailWord_8165794
  simp only [CollatzResearch.WordTrace]
  refine ⟨74457743744682604857502109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198553983319153612953338957 74457743744682604857502109)
  ·
    refine ⟨27921653904255976821563291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74457743744682604857502109 27921653904255976821563291)
    ·
      refine ⟨41882480856383965232344937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27921653904255976821563291 41882480856383965232344937)
      ·
        refine ⟨31411860642287973924258703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41882480856383965232344937 31411860642287973924258703)
        ·
          refine ⟨47117790963431960886388055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31411860642287973924258703 47117790963431960886388055)
          ·
            refine ⟨70676686445147941329582083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47117790963431960886388055 70676686445147941329582083)
            ·
              refine ⟨106015029667721911994373125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70676686445147941329582083 106015029667721911994373125)
              ·
                refine ⟨19877818062697858498944961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106015029667721911994373125 19877818062697858498944961)
                ·
                  refine ⟨14908363547023393874208721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19877818062697858498944961 14908363547023393874208721)
                  ·
                    refine ⟨11181272660267545405656541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14908363547023393874208721 11181272660267545405656541)
                    ·
                      refine ⟨4192977247600329527121203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11181272660267545405656541 4192977247600329527121203)
                      ·
                        rfl

theorem cell23_8165794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_8165794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165794 prefixEnd_8165794 := by exact prefixLift 8165794
  have htrace : WordTrace (prefixWord ++ tailWord_8165794) baseStart_8165794 baseEnd_8165794 := by
    simpa [prefixWord, tailWord_8165794, baseEnd_8165794] using wordTrace_append hprefix tailTrace_8165794
  have hstable : (prefixWord ++ tailWord_8165794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165794).length < 2 ^ (prefixWord ++ tailWord_8165794).sum := by decide
  have hdescent : baseEnd_8165794 < baseStart_8165794 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165797 : List Nat := [1, 3, 1, 2, 1, 1, 6, 2, 6]
def baseStart_8165797 : Nat := 118140960795 + 8165797 * 2 ^ 59
def prefixEnd_8165797 : Nat := 4983230072969 + 3 ^ 40 * 8165797 * 2
def baseEnd_8165797 : Nat := 465886532004699223931521

theorem tailTrace_8165797 : CollatzResearch.WordTrace tailWord_8165797 prefixEnd_8165797 465886532004699223931521 := by
  unfold tailWord_8165797
  simp only [CollatzResearch.WordTrace]
  refine ⟨297831084397719550942367645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198554056265146367294911763 297831084397719550942367645)
  ·
    refine ⟨111686656649144831603387867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297831084397719550942367645 111686656649144831603387867)
    ·
      refine ⟨167529984973717247405081801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111686656649144831603387867 167529984973717247405081801)
      ·
        refine ⟨125647488730287935553811351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167529984973717247405081801 125647488730287935553811351)
        ·
          refine ⟨188471233095431903330717027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125647488730287935553811351 188471233095431903330717027)
          ·
            refine ⟨282706849643147854996075541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188471233095431903330717027 282706849643147854996075541)
            ·
              refine ⟨13251883577022555702941041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 282706849643147854996075541 13251883577022555702941041)
              ·
                refine ⟨9938912682766916777205781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13251883577022555702941041 9938912682766916777205781)
                ·
                  refine ⟨465886532004699223931521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9938912682766916777205781 465886532004699223931521)
                  ·
                    rfl

theorem cell23_8165797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 6].length) (baseStart_8165797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165797 prefixEnd_8165797 := by exact prefixLift 8165797
  have htrace : WordTrace (prefixWord ++ tailWord_8165797) baseStart_8165797 baseEnd_8165797 := by
    simpa [prefixWord, tailWord_8165797, baseEnd_8165797] using wordTrace_append hprefix tailTrace_8165797
  have hstable : (prefixWord ++ tailWord_8165797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165797).length < 2 ^ (prefixWord ++ tailWord_8165797).sum := by decide
  have hdescent : baseEnd_8165797 < baseStart_8165797 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165825 : List Nat := [1, 2, 7, 1, 1, 2, 1, 1, 2, 1, 4]
def baseStart_8165825 : Nat := 118140960795 + 8165825 * 2 ^ 59
def prefixEnd_8165825 : Nat := 4983230072969 + 3 ^ 40 * 8165825 * 2
def baseEnd_8165825 : Nat := 4192993165500618905833561

theorem tailTrace_8165825 : CollatzResearch.WordTrace tailWord_8165825 prefixEnd_8165825 4192993165500618905833561 := by
  unfold tailWord_8165825
  simp only [CollatzResearch.WordTrace]
  refine ⟨297832105641618111724386929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198554737094412074482924619 297832105641618111724386929)
  ·
    refine ⟨223374079231213583793290197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297832105641618111724386929 223374079231213583793290197)
    ·
      refine ⟨5235329981981568370155239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 223374079231213583793290197 5235329981981568370155239)
      ·
        refine ⟨7852994972972352555232859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5235329981981568370155239 7852994972972352555232859)
        ·
          refine ⟨11779492459458528832849289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7852994972972352555232859 11779492459458528832849289)
          ·
            refine ⟨8834619344593896624636967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11779492459458528832849289 8834619344593896624636967)
            ·
              refine ⟨13251929016890844936955451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8834619344593896624636967 13251929016890844936955451)
              ·
                refine ⟨19877893525336267405433177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13251929016890844936955451 19877893525336267405433177)
                ·
                  refine ⟨14908420144002200554074883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19877893525336267405433177 14908420144002200554074883)
                  ·
                    refine ⟨22362630216003300831112325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14908420144002200554074883 22362630216003300831112325)
                    ·
                      refine ⟨4192993165500618905833561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22362630216003300831112325 4192993165500618905833561)
                      ·
                        rfl

theorem cell23_8165825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_8165825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165825 prefixEnd_8165825 := by exact prefixLift 8165825
  have htrace : WordTrace (prefixWord ++ tailWord_8165825) baseStart_8165825 baseEnd_8165825 := by
    simpa [prefixWord, tailWord_8165825, baseEnd_8165825] using wordTrace_append hprefix tailTrace_8165825
  have hstable : (prefixWord ++ tailWord_8165825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165825).length < 2 ^ (prefixWord ++ tailWord_8165825).sum := by decide
  have hdescent : baseEnd_8165825 < baseStart_8165825 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165827 : List Nat := [1, 1, 1, 3, 1, 1, 3, 6, 1, 5]
def baseStart_8165827 : Nat := 118140960795 + 8165827 * 2 ^ 59
def prefixEnd_8165827 : Nat := 4983230072969 + 3 ^ 40 * 8165827 * 2
def baseEnd_8165827 : Nat := 1397664730820642632669517

theorem tailTrace_8165827 : CollatzResearch.WordTrace tailWord_8165827 prefixEnd_8165827 1397664730820642632669517 := by
  unfold tailWord_8165827
  simp only [CollatzResearch.WordTrace]
  refine ⟨297832178587610866065959735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198554785725073910710639823 297832178587610866065959735)
  ·
    refine ⟨446748267881416299098939603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297832178587610866065959735 446748267881416299098939603)
    ·
      refine ⟨670122401822124448648409405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446748267881416299098939603 670122401822124448648409405)
      ·
        refine ⟨251295900683296668243153527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 670122401822124448648409405 251295900683296668243153527)
        ·
          refine ⟨376943851024945002364730291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251295900683296668243153527 376943851024945002364730291)
          ·
            refine ⟨565415776537417503547095437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376943851024945002364730291 565415776537417503547095437)
            ·
              refine ⟨212030916201531563830160789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 565415776537417503547095437 212030916201531563830160789)
              ·
                refine ⟨9938949196946792054538787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 212030916201531563830160789 9938949196946792054538787)
                ·
                  refine ⟨14908423795420188081808181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9938949196946792054538787 14908423795420188081808181)
                  ·
                    refine ⟨1397664730820642632669517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14908423795420188081808181 1397664730820642632669517)
                    ·
                      rfl

theorem cell23_8165827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 5].length) (baseStart_8165827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165827 prefixEnd_8165827 := by exact prefixLift 8165827
  have htrace : WordTrace (prefixWord ++ tailWord_8165827) baseStart_8165827 baseEnd_8165827 := by
    simpa [prefixWord, tailWord_8165827, baseEnd_8165827] using wordTrace_append hprefix tailTrace_8165827
  have hstable : (prefixWord ++ tailWord_8165827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165827).length < 2 ^ (prefixWord ++ tailWord_8165827).sum := by decide
  have hdescent : baseEnd_8165827 < baseStart_8165827 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165828 : List Nat := [2, 3, 3, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_8165828 : Nat := 118140960795 + 8165828 * 2 ^ 59
def prefixEnd_8165828 : Nat := 4983230072969 + 3 ^ 40 * 8165828 * 2
def baseEnd_8165828 : Nat := 4192994705942582394096047

theorem tailTrace_8165828 : CollatzResearch.WordTrace tailWord_8165828 prefixEnd_8165828 4192994705942582394096047 := by
  unfold tailWord_8165828
  simp only [CollatzResearch.WordTrace]
  refine ⟨148916107530303621618373069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198554810040404828824497425 148916107530303621618373069)
  ·
    refine ⟨55843540323863858106889901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148916107530303621618373069 55843540323863858106889901)
    ·
      refine ⟨20941327621448946790083713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55843540323863858106889901 20941327621448946790083713)
      ·
        refine ⟨15705995716086710092562785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20941327621448946790083713 15705995716086710092562785)
        ·
          refine ⟨11779496787065032569422089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15705995716086710092562785 11779496787065032569422089)
          ·
            refine ⟨8834622590298774427066567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11779496787065032569422089 8834622590298774427066567)
            ·
              refine ⟨13251933885448161640599851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8834622590298774427066567 13251933885448161640599851)
              ·
                refine ⟨19877900828172242460899777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13251933885448161640599851 19877900828172242460899777)
                ·
                  refine ⟨14908425621129181845674833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19877900828172242460899777 14908425621129181845674833)
                  ·
                    refine ⟨11181319215846886384256125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14908425621129181845674833 11181319215846886384256125)
                    ·
                      refine ⟨4192994705942582394096047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11181319215846886384256125 4192994705942582394096047)
                      ·
                        rfl

theorem cell23_8165828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_8165828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165828 prefixEnd_8165828 := by exact prefixLift 8165828
  have htrace : WordTrace (prefixWord ++ tailWord_8165828) baseStart_8165828 baseEnd_8165828 := by
    simpa [prefixWord, tailWord_8165828, baseEnd_8165828] using wordTrace_append hprefix tailTrace_8165828
  have hstable : (prefixWord ++ tailWord_8165828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165828).length < 2 ^ (prefixWord ++ tailWord_8165828).sum := by decide
  have hdescent : baseEnd_8165828 < baseStart_8165828 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165834 : List Nat := [3, 1, 2, 1, 2, 2, 3, 1, 1, 5, 2]
def baseStart_8165834 : Nat := 118140960795 + 8165834 * 2 ^ 59
def prefixEnd_8165834 : Nat := 4983230072969 + 3 ^ 40 * 8165834 * 2
def baseEnd_8165834 : Nat := 4192997786826509370621019

theorem tailTrace_8165834 : CollatzResearch.WordTrace tailWord_8165834 prefixEnd_8165834 4192997786826509370621019 := by
  unfold tailWord_8165834
  simp only [CollatzResearch.WordTrace]
  refine ⟨74458108474646376565366139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198554955932390337507643037 74458108474646376565366139)
  ·
    refine ⟨111687162711969564848049209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74458108474646376565366139 111687162711969564848049209)
    ·
      refine ⟨83765372033977173636036907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111687162711969564848049209 83765372033977173636036907)
      ·
        refine ⟨125648058050965760454055361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83765372033977173636036907 125648058050965760454055361)
        ·
          refine ⟨94236043538224320340541521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125648058050965760454055361 94236043538224320340541521)
          ·
            refine ⟨70677032653668240255406141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94236043538224320340541521 70677032653668240255406141)
            ·
              refine ⟨26503887245125590095777303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70677032653668240255406141 26503887245125590095777303)
              ·
                refine ⟨39755830867688385143665955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26503887245125590095777303 39755830867688385143665955)
                ·
                  refine ⟨59633746301532577715498933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39755830867688385143665955 59633746301532577715498933)
                  ·
                    refine ⟨5590663715768679160828025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59633746301532577715498933 5590663715768679160828025)
                    ·
                      refine ⟨4192997786826509370621019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5590663715768679160828025 4192997786826509370621019)
                      ·
                        rfl

theorem cell23_8165834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 1, 5, 2].length) (baseStart_8165834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165834 prefixEnd_8165834 := by exact prefixLift 8165834
  have htrace : WordTrace (prefixWord ++ tailWord_8165834) baseStart_8165834 baseEnd_8165834 := by
    simpa [prefixWord, tailWord_8165834, baseEnd_8165834] using wordTrace_append hprefix tailTrace_8165834
  have hstable : (prefixWord ++ tailWord_8165834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165834).length < 2 ^ (prefixWord ++ tailWord_8165834).sum := by decide
  have hdescent : baseEnd_8165834 < baseStart_8165834 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165867 : List Nat := [1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 5]
def baseStart_8165867 : Nat := 118140960795 + 8165867 * 2 ^ 59
def prefixEnd_8165867 : Nat := 4983230072969 + 3 ^ 40 * 8165867 * 2
def baseEnd_8165867 : Nat := 4193014731688107741508367

theorem tailTrace_8165867 : CollatzResearch.WordTrace tailWord_8165867 prefixEnd_8165867 4193014731688107741508367 := by
  unfold tailWord_8165867
  simp only [CollatzResearch.WordTrace]
  refine ⟨297833637507465952897415855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198555758338310635264943903 297833637507465952897415855)
  ·
    refine ⟨446750456261198929346123783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297833637507465952897415855 446750456261198929346123783)
    ·
      refine ⟨670125684391798394019185675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446750456261198929346123783 670125684391798394019185675)
      ·
        refine ⟨1005188526587697591028778513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670125684391798394019185675 1005188526587697591028778513)
        ·
          refine ⟨753891394940773193271583885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1005188526587697591028778513 753891394940773193271583885)
          ·
            refine ⟨282709273102789947476843957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 753891394940773193271583885 282709273102789947476843957)
            ·
              refine ⟨26503994353386557575954121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 282709273102789947476843957 26503994353386557575954121)
              ·
                refine ⟨19877995765039918181965591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26503994353386557575954121 19877995765039918181965591)
                ·
                  refine ⟨29816993647559877272948387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19877995765039918181965591 29816993647559877272948387)
                  ·
                    refine ⟨44725490471339815909422581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29816993647559877272948387 44725490471339815909422581)
                    ·
                      refine ⟨4193014731688107741508367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44725490471339815909422581 4193014731688107741508367)
                      ·
                        rfl

theorem cell23_8165867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 5].length) (baseStart_8165867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165867 prefixEnd_8165867 := by exact prefixLift 8165867
  have htrace : WordTrace (prefixWord ++ tailWord_8165867) baseStart_8165867 baseEnd_8165867 := by
    simpa [prefixWord, tailWord_8165867, baseEnd_8165867] using wordTrace_append hprefix tailTrace_8165867
  have hstable : (prefixWord ++ tailWord_8165867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165867).length < 2 ^ (prefixWord ++ tailWord_8165867).sum := by decide
  have hdescent : baseEnd_8165867 < baseStart_8165867 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165881 : List Nat := [1, 2, 1, 3, 1, 2, 4, 2, 3, 2, 2]
def baseStart_8165881 : Nat := 118140960795 + 8165881 * 2 ^ 59
def prefixEnd_8165881 : Nat := 4983230072969 + 3 ^ 40 * 8165881 * 2
def baseEnd_8165881 : Nat := 4193021920417270686733303

theorem tailTrace_8165881 : CollatzResearch.WordTrace tailWord_8165881 prefixEnd_8165881 4193021920417270686733303 := by
  unfold tailWord_8165881
  simp only [CollatzResearch.WordTrace]
  refine ⟨297834148129415233288425497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198556098752943488858950331 297834148129415233288425497)
  ·
    refine ⟨223375611097061424966319123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297834148129415233288425497 223375611097061424966319123)
    ·
      refine ⟨335063416645592137449478685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223375611097061424966319123 335063416645592137449478685)
      ·
        refine ⟨125648781242097051543554507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335063416645592137449478685 125648781242097051543554507)
        ·
          refine ⟨188473171863145577315331761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125648781242097051543554507 188473171863145577315331761)
          ·
            refine ⟨141354878897359182986498821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188473171863145577315331761 141354878897359182986498821)
            ·
              refine ⟨26504039793254846809968529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141354878897359182986498821 26504039793254846809968529)
              ·
                refine ⟨19878029844941135107476397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26504039793254846809968529 19878029844941135107476397)
                ·
                  refine ⟨7454261191852925665303649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19878029844941135107476397 7454261191852925665303649)
                  ·
                    refine ⟨5590695893889694248977737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7454261191852925665303649 5590695893889694248977737)
                    ·
                      refine ⟨4193021920417270686733303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5590695893889694248977737 4193021920417270686733303)
                      ·
                        rfl

theorem cell23_8165881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3, 2, 2].length) (baseStart_8165881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165881 prefixEnd_8165881 := by exact prefixLift 8165881
  have htrace : WordTrace (prefixWord ++ tailWord_8165881) baseStart_8165881 baseEnd_8165881 := by
    simpa [prefixWord, tailWord_8165881, baseEnd_8165881] using wordTrace_append hprefix tailTrace_8165881
  have hstable : (prefixWord ++ tailWord_8165881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165881).length < 2 ^ (prefixWord ++ tailWord_8165881).sum := by decide
  have hdescent : baseEnd_8165881 < baseStart_8165881 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165941 : List Nat := [1, 3, 3, 1, 1, 2, 3, 1, 3, 3, 2]
def baseStart_8165941 : Nat := 118140960795 + 8165941 * 2 ^ 59
def prefixEnd_8165941 : Nat := 4983230072969 + 3 ^ 40 * 8165941 * 2
def baseEnd_8165941 : Nat := 4193052729256540451983027

theorem tailTrace_8165941 : CollatzResearch.WordTrace tailWord_8165941 prefixEnd_8165941 4193052729256540451983027 := by
  unfold tailWord_8165941
  simp only [CollatzResearch.WordTrace]
  refine ⟨297836336509197863535609677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198557557672798575690406451 297836336509197863535609677)
  ·
    refine ⟨111688626190949198825853629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297836336509197863535609677 111688626190949198825853629)
    ·
      refine ⟨41883234821605949559695111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111688626190949198825853629 41883234821605949559695111)
      ·
        refine ⟨62824852232408924339542667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41883234821605949559695111 62824852232408924339542667)
        ·
          refine ⟨94237278348613386509314001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62824852232408924339542667 94237278348613386509314001)
          ·
            refine ⟨70677958761460039881985501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94237278348613386509314001 70677958761460039881985501)
            ·
              refine ⟨26504234535547514955744563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70677958761460039881985501 26504234535547514955744563)
              ·
                refine ⟨39756351803321272433616845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26504234535547514955744563 39756351803321272433616845)
                ·
                  refine ⟨14908631926245477162606317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39756351803321272433616845 14908631926245477162606317)
                  ·
                    refine ⟨5590736972342053935977369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14908631926245477162606317 5590736972342053935977369)
                    ·
                      refine ⟨4193052729256540451983027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5590736972342053935977369 4193052729256540451983027)
                      ·
                        rfl

theorem cell23_8165941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_8165941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165941 prefixEnd_8165941 := by exact prefixLift 8165941
  have htrace : WordTrace (prefixWord ++ tailWord_8165941) baseStart_8165941 baseEnd_8165941 := by
    simpa [prefixWord, tailWord_8165941, baseEnd_8165941] using wordTrace_append hprefix tailTrace_8165941
  have hstable : (prefixWord ++ tailWord_8165941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165941).length < 2 ^ (prefixWord ++ tailWord_8165941).sum := by decide
  have hdescent : baseEnd_8165941 < baseStart_8165941 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165965 : List Nat := [1, 6, 1, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_8165965 : Nat := 118140960795 + 8165965 * 2 ^ 59
def prefixEnd_8165965 : Nat := 4983230072969 + 3 ^ 40 * 8165965 * 2
def baseEnd_8165965 : Nat := 4193065052792248358082917

theorem tailTrace_8165965 : CollatzResearch.WordTrace tailWord_8165965 prefixEnd_8165965 4193065052792248358082917 := by
  unfold tailWord_8165965
  simp only [CollatzResearch.WordTrace]
  refine ⟨297837211861110915634483349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198558141240740610422988899 297837211861110915634483349)
  ·
    refine ⟨13961119305989574170366407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 297837211861110915634483349 13961119305989574170366407)
    ·
      refine ⟨20941678958984361255549611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13961119305989574170366407 20941678958984361255549611)
      ·
        refine ⟨31412518438476541883324417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20941678958984361255549611 31412518438476541883324417)
        ·
          refine ⟨23559388828857406412493313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31412518438476541883324417 23559388828857406412493313)
          ·
            refine ⟨17669541621643054809369985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23559388828857406412493313 17669541621643054809369985)
            ·
              refine ⟨13252156216232291107027489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17669541621643054809369985 13252156216232291107027489)
              ·
                refine ⟨9939117162174218330270617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13252156216232291107027489 9939117162174218330270617)
                ·
                  refine ⟨7454337871630663747702963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9939117162174218330270617 7454337871630663747702963)
                  ·
                    refine ⟨11181506807445995621554445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7454337871630663747702963 11181506807445995621554445)
                    ·
                      refine ⟨4193065052792248358082917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11181506807445995621554445 4193065052792248358082917)
                      ·
                        rfl

theorem cell23_8165965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_8165965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165965 prefixEnd_8165965 := by exact prefixLift 8165965
  have htrace : WordTrace (prefixWord ++ tailWord_8165965) baseStart_8165965 baseEnd_8165965 := by
    simpa [prefixWord, tailWord_8165965, baseEnd_8165965] using wordTrace_append hprefix tailTrace_8165965
  have hstable : (prefixWord ++ tailWord_8165965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165965).length < 2 ^ (prefixWord ++ tailWord_8165965).sum := by decide
  have hdescent : baseEnd_8165965 < baseStart_8165965 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165982 : List Nat := [4, 4, 1, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_8165982 : Nat := 118140960795 + 8165982 * 2 ^ 59
def prefixEnd_8165982 : Nat := 4983230072969 + 3 ^ 40 * 8165982 * 2
def baseEnd_8165982 : Nat := 4193073781963374791570339

theorem tailTrace_8165982 : CollatzResearch.WordTrace tailWord_8165982 prefixEnd_8165982 4193073781963374791570339 := by
  unfold tailWord_8165982
  simp only [CollatzResearch.WordTrace]
  refine ⟨37229728987756165942231525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198558554601366218358568133 37229728987756165942231525)
  ·
    refine ⟨6980574185204281114168411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37229728987756165942231525 6980574185204281114168411)
    ·
      refine ⟨10470861277806421671252617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6980574185204281114168411 10470861277806421671252617)
      ·
        refine ⟨7853145958354816253439463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10470861277806421671252617 7853145958354816253439463)
        ·
          refine ⟨11779718937532224380159195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7853145958354816253439463 11779718937532224380159195)
          ·
            refine ⟨17669578406298336570238793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11779718937532224380159195 17669578406298336570238793)
            ·
              refine ⟨13252183804723752427679095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17669578406298336570238793 13252183804723752427679095)
              ·
                refine ⟨19878275707085628641518643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13252183804723752427679095 19878275707085628641518643)
                ·
                  refine ⟨29817413560628442962277965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19878275707085628641518643 29817413560628442962277965)
                  ·
                    refine ⟨11181530085235666110854237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29817413560628442962277965 11181530085235666110854237)
                    ·
                      refine ⟨4193073781963374791570339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11181530085235666110854237 4193073781963374791570339)
                      ·
                        rfl

theorem cell23_8165982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_8165982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165982 prefixEnd_8165982 := by exact prefixLift 8165982
  have htrace : WordTrace (prefixWord ++ tailWord_8165982) baseStart_8165982 baseEnd_8165982 := by
    simpa [prefixWord, tailWord_8165982, baseEnd_8165982] using wordTrace_append hprefix tailTrace_8165982
  have hstable : (prefixWord ++ tailWord_8165982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165982).length < 2 ^ (prefixWord ++ tailWord_8165982).sum := by decide
  have hdescent : baseEnd_8165982 < baseStart_8165982 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165988 : List Nat := [2, 3, 1, 1, 2, 2, 1, 5, 2, 2, 2]
def baseStart_8165988 : Nat := 118140960795 + 8165988 * 2 ^ 59
def prefixEnd_8165988 : Nat := 4983230072969 + 3 ^ 40 * 8165988 * 2
def baseEnd_8165988 : Nat := 4193076862847301768095311

theorem tailTrace_8165988 : CollatzResearch.WordTrace tailWord_8165988 prefixEnd_8165988 4193076862847301768095311 := by
  unfold tailWord_8165988
  simp only [CollatzResearch.WordTrace]
  refine ⟨148919025370013795281285309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198558700493351727041713745 148919025370013795281285309)
  ·
    refine ⟨55844634513755173230481991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148919025370013795281285309 55844634513755173230481991)
    ·
      refine ⟨83766951770632759845722987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55844634513755173230481991 83766951770632759845722987)
      ·
        refine ⟨125650427655949139768584481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83766951770632759845722987 125650427655949139768584481)
        ·
          refine ⟨94237820741961854826438361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125650427655949139768584481 94237820741961854826438361)
          ·
            refine ⟨70678365556471391119828771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94237820741961854826438361 70678365556471391119828771)
            ·
              refine ⟨106017548334707086679743157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70678365556471391119828771 106017548334707086679743157)
              ·
                refine ⟨9939145156378789376225921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106017548334707086679743157 9939145156378789376225921)
                ·
                  refine ⟨7454358867284092032169441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9939145156378789376225921 7454358867284092032169441)
                  ·
                    refine ⟨5590769150463069024127081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7454358867284092032169441 5590769150463069024127081)
                    ·
                      refine ⟨4193076862847301768095311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5590769150463069024127081 4193076862847301768095311)
                      ·
                        rfl

theorem cell23_8165988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 2, 2, 2].length) (baseStart_8165988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165988 prefixEnd_8165988 := by exact prefixLift 8165988
  have htrace : WordTrace (prefixWord ++ tailWord_8165988) baseStart_8165988 baseEnd_8165988 := by
    simpa [prefixWord, tailWord_8165988, baseEnd_8165988] using wordTrace_append hprefix tailTrace_8165988
  have hstable : (prefixWord ++ tailWord_8165988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165988).length < 2 ^ (prefixWord ++ tailWord_8165988).sum := by decide
  have hdescent : baseEnd_8165988 < baseStart_8165988 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8165994 : List Nat := [3, 1, 3, 2, 1, 1, 3, 2, 7]
def baseStart_8165994 : Nat := 118140960795 + 8165994 * 2 ^ 59
def prefixEnd_8165994 : Nat := 4983230072969 + 3 ^ 40 * 8165994 * 2
def baseEnd_8165994 : Nat := 465897771525692082735587

theorem tailTrace_8165994 : CollatzResearch.WordTrace tailWord_8165994 prefixEnd_8165994 465897771525692082735587 := by
  unfold tailWord_8165994
  simp only [CollatzResearch.WordTrace]
  refine ⟨74459567394501463396822259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198558846385337235724859357 74459567394501463396822259)
  ·
    refine ⟨111689351091752195095233389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74459567394501463396822259 111689351091752195095233389)
    ·
      refine ⟨41883506659407073160712521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111689351091752195095233389 41883506659407073160712521)
      ·
        refine ⟨31412629994555304870534391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41883506659407073160712521 31412629994555304870534391)
        ·
          refine ⟨47118944991832957305801587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31412629994555304870534391 47118944991832957305801587)
          ·
            refine ⟨70678417487749435958702381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47118944991832957305801587 70678417487749435958702381)
            ·
              refine ⟨26504406557906038484513393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70678417487749435958702381 26504406557906038484513393)
              ·
                refine ⟨19878304918429528863385045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26504406557906038484513393 19878304918429528863385045)
                ·
                  refine ⟨465897771525692082735587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19878304918429528863385045 465897771525692082735587)
                  ·
                    rfl

theorem cell23_8165994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 7].length) (baseStart_8165994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8165994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8165994 prefixEnd_8165994 := by exact prefixLift 8165994
  have htrace : WordTrace (prefixWord ++ tailWord_8165994) baseStart_8165994 baseEnd_8165994 := by
    simpa [prefixWord, tailWord_8165994, baseEnd_8165994] using wordTrace_append hprefix tailTrace_8165994
  have hstable : (prefixWord ++ tailWord_8165994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8165994).length < 2 ^ (prefixWord ++ tailWord_8165994).sum := by decide
  have hdescent : baseEnd_8165994 < baseStart_8165994 := by decide
  rcases family_descends (prefixWord ++ tailWord_8165994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166061 : List Nat := [1, 5, 2, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_8166061 : Nat := 118140960795 + 8166061 * 2 ^ 59
def prefixEnd_8166061 : Nat := 4983230072969 + 3 ^ 40 * 8166061 * 2
def baseEnd_8166061 : Nat := 4193114346935079982482475

theorem tailTrace_8166061 : CollatzResearch.WordTrace tailWord_8166061 prefixEnd_8166061 4193114346935079982482475 := by
  unfold tailWord_8166061
  simp only [CollatzResearch.WordTrace]
  refine ⟨297840713268763124029978037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198560475512508749353318691 297840713268763124029978037)
  ·
    refine ⟨27922566868946542877810441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 297840713268763124029978037 27922566868946542877810441)
    ·
      refine ⟨20941925151709907158357831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27922566868946542877810441 20941925151709907158357831)
      ·
        refine ⟨31412887727564860737536747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20941925151709907158357831 31412887727564860737536747)
        ·
          refine ⟨47119331591347291106305121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31412887727564860737536747 47119331591347291106305121)
          ·
            refine ⟨35339498693510468329728841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47119331591347291106305121 35339498693510468329728841)
            ·
              refine ⟨26504624020132851247296631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35339498693510468329728841 26504624020132851247296631)
              ·
                refine ⟨39756936030199276870944947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26504624020132851247296631 39756936030199276870944947)
                ·
                  refine ⟨59635404045298915306417421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39756936030199276870944947 59635404045298915306417421)
                  ·
                    refine ⟨22363276516987093239906533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59635404045298915306417421 22363276516987093239906533)
                    ·
                      refine ⟨4193114346935079982482475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22363276516987093239906533 4193114346935079982482475)
                      ·
                        rfl

theorem cell23_8166061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_8166061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166061 prefixEnd_8166061 := by exact prefixLift 8166061
  have htrace : WordTrace (prefixWord ++ tailWord_8166061) baseStart_8166061 baseEnd_8166061 := by
    simpa [prefixWord, tailWord_8166061, baseEnd_8166061] using wordTrace_append hprefix tailTrace_8166061
  have hstable : (prefixWord ++ tailWord_8166061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166061).length < 2 ^ (prefixWord ++ tailWord_8166061).sum := by decide
  have hdescent : baseEnd_8166061 < baseStart_8166061 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166088 : List Nat := [2, 1, 3, 1, 2, 5, 1, 1, 3, 4]
def baseStart_8166088 : Nat := 118140960795 + 8166088 * 2 ^ 59
def prefixEnd_8166088 : Nat := 4983230072969 + 3 ^ 40 * 8166088 * 2
def baseEnd_8166088 : Nat := 1397709403637583792281617

theorem tailTrace_8166088 : CollatzResearch.WordTrace tailWord_8166088 prefixEnd_8166088 1397709403637583792281617 := by
  unfold tailWord_8166088
  simp only [CollatzResearch.WordTrace]
  refine ⟨148920849019832653820605459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198561132026443538427473945 148920849019832653820605459)
  ·
    refine ⟨223381273529748980730908189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148920849019832653820605459 223381273529748980730908189)
    ·
      refine ⟨83767977573655867774090571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223381273529748980730908189 83767977573655867774090571)
      ·
        refine ⟨125651966360483801661135857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83767977573655867774090571 125651966360483801661135857)
        ·
          refine ⟨94238974770362851245851893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125651966360483801661135857 94238974770362851245851893)
          ·
            refine ⟨8834903884721517304298615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94238974770362851245851893 8834903884721517304298615)
            ·
              refine ⟨13252355827082275956447923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8834903884721517304298615 13252355827082275956447923)
              ·
                refine ⟨19878533740623413934671885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13252355827082275956447923 19878533740623413934671885)
                ·
                  refine ⟨7454450152733780225501957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19878533740623413934671885 7454450152733780225501957)
                  ·
                    refine ⟨1397709403637583792281617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7454450152733780225501957 1397709403637583792281617)
                    ·
                      rfl

theorem cell23_8166088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_8166088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166088 prefixEnd_8166088 := by exact prefixLift 8166088
  have htrace : WordTrace (prefixWord ++ tailWord_8166088) baseStart_8166088 baseEnd_8166088 := by
    simpa [prefixWord, tailWord_8166088, baseEnd_8166088] using wordTrace_append hprefix tailTrace_8166088
  have hstable : (prefixWord ++ tailWord_8166088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166088).length < 2 ^ (prefixWord ++ tailWord_8166088).sum := by decide
  have hdescent : baseEnd_8166088 < baseStart_8166088 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166121 : List Nat := [1, 2, 1, 1, 1, 2, 4, 3, 1, 5, 2]
def baseStart_8166121 : Nat := 118140960795 + 8166121 * 2 ^ 59
def prefixEnd_8166121 : Nat := 4983230072969 + 3 ^ 40 * 8166121 * 2
def baseEnd_8166121 : Nat := 4193145155774349747732199

theorem tailTrace_8166121 : CollatzResearch.WordTrace tailWord_8166121 prefixEnd_8166121 4193145155774349747732199 := by
  unfold tailWord_8166121
  simp only [CollatzResearch.WordTrace]
  refine ⟨297842901648545754277162217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198561934432363836184774811 297842901648545754277162217)
  ·
    refine ⟨223382176236409315707871663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297842901648545754277162217 223382176236409315707871663)
    ·
      refine ⟨335073264354613973561807495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223382176236409315707871663 335073264354613973561807495)
      ·
        refine ⟨502609896531920960342711243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335073264354613973561807495 502609896531920960342711243)
        ·
          refine ⟨753914844797881440514066865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502609896531920960342711243 753914844797881440514066865)
          ·
            refine ⟨565436133598411080385550149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 753914844797881440514066865 565436133598411080385550149)
            ·
              refine ⟨106019275049702077572290653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 565436133598411080385550149 106019275049702077572290653)
              ·
                refine ⟨39757228143638279089608995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106019275049702077572290653 39757228143638279089608995)
                ·
                  refine ⟨59635842215457418634413493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39757228143638279089608995 59635842215457418634413493)
                  ·
                    refine ⟨5590860207699132996976265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59635842215457418634413493 5590860207699132996976265)
                    ·
                      refine ⟨4193145155774349747732199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5590860207699132996976265 4193145155774349747732199)
                      ·
                        rfl

theorem cell23_8166121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 5, 2].length) (baseStart_8166121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166121 prefixEnd_8166121 := by exact prefixLift 8166121
  have htrace : WordTrace (prefixWord ++ tailWord_8166121) baseStart_8166121 baseEnd_8166121 := by
    simpa [prefixWord, tailWord_8166121, baseEnd_8166121] using wordTrace_append hprefix tailTrace_8166121
  have hstable : (prefixWord ++ tailWord_8166121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166121).length < 2 ^ (prefixWord ++ tailWord_8166121).sum := by decide
  have hdescent : baseEnd_8166121 < baseStart_8166121 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166138 : List Nat := [3, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2]
def baseStart_8166138 : Nat := 118140960795 + 8166138 * 2 ^ 59
def prefixEnd_8166138 : Nat := 4983230072969 + 3 ^ 40 * 8166138 * 2
def baseEnd_8166138 : Nat := 4193153884945476181219621

theorem tailTrace_8166138 : CollatzResearch.WordTrace tailWord_8166138 prefixEnd_8166138 4193153884945476181219621 := by
  unfold tailWord_8166138
  simp only [CollatzResearch.WordTrace]
  refine ⟨74460880422371041545132767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198562347792989444120354045 74460880422371041545132767)
  ·
    refine ⟨111691320633556562317699151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74460880422371041545132767 111691320633556562317699151)
    ·
      refine ⟨167536980950334843476548727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111691320633556562317699151 167536980950334843476548727)
      ·
        refine ⟨251305471425502265214823091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167536980950334843476548727 251305471425502265214823091)
        ·
          refine ⟨376958207138253397822234637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251305471425502265214823091 376958207138253397822234637)
          ·
            refine ⟨141359327676845024183337989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 376958207138253397822234637 141359327676845024183337989)
            ·
              refine ⟨26504873939408442034375873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141359327676845024183337989 26504873939408442034375873)
              ·
                refine ⟨19878655454556331525781905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26504873939408442034375873 19878655454556331525781905)
                ·
                  refine ⟨14908991590917248644336429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19878655454556331525781905 14908991590917248644336429)
                  ·
                    refine ⟨5590871846593968241626161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14908991590917248644336429 5590871846593968241626161)
                    ·
                      refine ⟨4193153884945476181219621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5590871846593968241626161 4193153884945476181219621)
                      ·
                        rfl

theorem cell23_8166138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2].length) (baseStart_8166138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166138 prefixEnd_8166138 := by exact prefixLift 8166138
  have htrace : WordTrace (prefixWord ++ tailWord_8166138) baseStart_8166138 baseEnd_8166138 := by
    simpa [prefixWord, tailWord_8166138, baseEnd_8166138] using wordTrace_append hprefix tailTrace_8166138
  have hstable : (prefixWord ++ tailWord_8166138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166138).length < 2 ^ (prefixWord ++ tailWord_8166138).sum := by decide
  have hdescent : baseEnd_8166138 < baseStart_8166138 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166162 : List Nat := [3, 2, 4, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_8166162 : Nat := 118140960795 + 8166162 * 2 ^ 59
def prefixEnd_8166162 : Nat := 4983230072969 + 3 ^ 40 * 8166162 * 2
def baseEnd_8166162 : Nat := 4193166208481184087319511

theorem tailTrace_8166162 : CollatzResearch.WordTrace tailWord_8166162 prefixEnd_8166162 4193166208481184087319511 := by
  unfold tailWord_8166162
  simp only [CollatzResearch.WordTrace]
  refine ⟨74461099260349304569851185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198562931360931478852936493 74461099260349304569851185)
  ·
    refine ⟨55845824445261978427388389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74461099260349304569851185 55845824445261978427388389)
    ·
      refine ⟨10471092083486620955135323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55845824445261978427388389 10471092083486620955135323)
      ·
        refine ⟨15706638125229931432702985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10471092083486620955135323 15706638125229931432702985)
        ·
          refine ⟨11779978593922448574527239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15706638125229931432702985 11779978593922448574527239)
          ·
            refine ⟨17669967890883672861790859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11779978593922448574527239 17669967890883672861790859)
            ·
              refine ⟨26504951836325509292686289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17669967890883672861790859 26504951836325509292686289)
              ·
                refine ⟨19878713877244131969514717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26504951836325509292686289 19878713877244131969514717)
                ·
                  refine ⟨7454517703966549488568019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19878713877244131969514717 7454517703966549488568019)
                  ·
                    refine ⟨11181776555949824232852029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7454517703966549488568019 11181776555949824232852029)
                    ·
                      refine ⟨4193166208481184087319511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11181776555949824232852029 4193166208481184087319511)
                      ·
                        rfl

theorem cell23_8166162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_8166162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166162 prefixEnd_8166162 := by exact prefixLift 8166162
  have htrace : WordTrace (prefixWord ++ tailWord_8166162) baseStart_8166162 baseEnd_8166162 := by
    simpa [prefixWord, tailWord_8166162, baseEnd_8166162] using wordTrace_append hprefix tailTrace_8166162
  have hstable : (prefixWord ++ tailWord_8166162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166162).length < 2 ^ (prefixWord ++ tailWord_8166162).sum := by decide
  have hdescent : baseEnd_8166162 < baseStart_8166162 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166181 : List Nat := [1, 3, 1, 2, 3, 1, 1, 4, 1, 2, 4]
def baseStart_8166181 : Nat := 118140960795 + 8166181 * 2 ^ 59
def prefixEnd_8166181 : Nat := 4983230072969 + 3 ^ 40 * 8166181 * 2
def baseEnd_8166181 : Nat := 4193175964613619512981923

theorem tailTrace_8166181 : CollatzResearch.WordTrace tailWord_8166181 prefixEnd_8166181 4193175964613619512981923 := by
  unfold tailWord_8166181
  simp only [CollatzResearch.WordTrace]
  refine ⟨297845090028328384524346397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198563393352218923016230931 297845090028328384524346397)
  ·
    refine ⟨111691908760623144196629899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297845090028328384524346397 111691908760623144196629899)
    ·
      refine ⟨167537863140934716294944849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111691908760623144196629899 167537863140934716294944849)
      ·
        refine ⟨125653397355701037221208637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167537863140934716294944849 125653397355701037221208637)
        ·
          refine ⟨47120024008387888957953239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125653397355701037221208637 47120024008387888957953239)
          ·
            refine ⟨70680036012581833436929859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47120024008387888957953239 70680036012581833436929859)
            ·
              refine ⟨106020054018872750155394789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70680036012581833436929859 106020054018872750155394789)
              ·
                refine ⟨19878760128538640654136523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106020054018872750155394789 19878760128538640654136523)
                ·
                  refine ⟨29818140192807960981204785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19878760128538640654136523 29818140192807960981204785)
                  ·
                    refine ⟨22363605144605970735903589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29818140192807960981204785 22363605144605970735903589)
                    ·
                      refine ⟨4193175964613619512981923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22363605144605970735903589 4193175964613619512981923)
                      ·
                        rfl

theorem cell23_8166181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_8166181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166181 prefixEnd_8166181 := by exact prefixLift 8166181
  have htrace : WordTrace (prefixWord ++ tailWord_8166181) baseStart_8166181 baseEnd_8166181 := by
    simpa [prefixWord, tailWord_8166181, baseEnd_8166181] using wordTrace_append hprefix tailTrace_8166181
  have hstable : (prefixWord ++ tailWord_8166181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166181).length < 2 ^ (prefixWord ++ tailWord_8166181).sum := by decide
  have hdescent : baseEnd_8166181 < baseStart_8166181 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166188 : List Nat := [2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 3]
def baseStart_8166188 : Nat := 118140960795 + 8166188 * 2 ^ 59
def prefixEnd_8166188 : Nat := 4983230072969 + 3 ^ 40 * 8166188 * 2
def baseEnd_8166188 : Nat := 4193179558978200985594391

theorem tailTrace_8166188 : CollatzResearch.WordTrace tailWord_8166188 prefixEnd_8166188 4193179558978200985594391 := by
  unfold tailWord_8166188
  simp only [CollatzResearch.WordTrace]
  refine ⟨148922672669651512359925609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198563563559535349813234145 148922672669651512359925609)
  ·
    refine ⟨111692004502238634269944207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148922672669651512359925609 111692004502238634269944207)
    ·
      refine ⟨167538006753357951404916311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111692004502238634269944207 167538006753357951404916311)
      ·
        refine ⟨251307010130036927107374467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167538006753357951404916311 251307010130036927107374467)
        ·
          refine ⟨376960515195055390661061701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251307010130036927107374467 376960515195055390661061701)
          ·
            refine ⟨70680096599072885748949069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 376960515195055390661061701 70680096599072885748949069)
            ·
              refine ⟨26505036224652332155855901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70680096599072885748949069 26505036224652332155855901)
              ·
                refine ⟨9939388584244624558445963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26505036224652332155855901 9939388584244624558445963)
                ·
                  refine ⟨14909082876366936837668945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9939388584244624558445963 14909082876366936837668945)
                  ·
                    refine ⟨11181812157275202628251709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14909082876366936837668945 11181812157275202628251709)
                    ·
                      refine ⟨4193179558978200985594391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11181812157275202628251709 4193179558978200985594391)
                      ·
                        rfl

theorem cell23_8166188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 3].length) (baseStart_8166188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166188 prefixEnd_8166188 := by exact prefixLift 8166188
  have htrace : WordTrace (prefixWord ++ tailWord_8166188) baseStart_8166188 baseEnd_8166188 := by
    simpa [prefixWord, tailWord_8166188, baseEnd_8166188] using wordTrace_append hprefix tailTrace_8166188
  have hstable : (prefixWord ++ tailWord_8166188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166188).length < 2 ^ (prefixWord ++ tailWord_8166188).sum := by decide
  have hdescent : baseEnd_8166188 < baseStart_8166188 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166195 : List Nat := [1, 1, 1, 2, 6, 3, 1, 2, 2, 4]
def baseStart_8166195 : Nat := 118140960795 + 8166195 * 2 ^ 59
def prefixEnd_8166195 : Nat := 4983230072969 + 3 ^ 40 * 8166195 * 2
def baseEnd_8166195 : Nat := 1397727717780927486068953

theorem tailTrace_8166195 : CollatzResearch.WordTrace tailWord_8166195 prefixEnd_8166195 1397727717780927486068953 := by
  unfold tailWord_8166195
  simp only [CollatzResearch.WordTrace]
  refine ⟨297845600650277664915356039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198563733766851776610237359 297845600650277664915356039)
  ·
    refine ⟨446768400975416497373034059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297845600650277664915356039 446768400975416497373034059)
    ·
      refine ⟨670152601463124746059551089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446768400975416497373034059 670152601463124746059551089)
      ·
        refine ⟨502614451097343559544663317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 670152601463124746059551089 502614451097343559544663317)
        ·
          refine ⟨23560052395187979353656093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 502614451097343559544663317 23560052395187979353656093)
          ·
            refine ⟨8835019648195492257621035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23560052395187979353656093 8835019648195492257621035)
            ·
              refine ⟨13252529472293238386431553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8835019648195492257621035 13252529472293238386431553)
              ·
                refine ⟨9939397104219928789823665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13252529472293238386431553 9939397104219928789823665)
                ·
                  refine ⟨7454547828164946592367749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9939397104219928789823665 7454547828164946592367749)
                  ·
                    refine ⟨1397727717780927486068953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7454547828164946592367749 1397727717780927486068953)
                    ·
                      rfl

theorem cell23_8166195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2, 4].length) (baseStart_8166195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166195 prefixEnd_8166195 := by exact prefixLift 8166195
  have htrace : WordTrace (prefixWord ++ tailWord_8166195) baseStart_8166195 baseEnd_8166195 := by
    simpa [prefixWord, tailWord_8166195, baseEnd_8166195] using wordTrace_append hprefix tailTrace_8166195
  have hstable : (prefixWord ++ tailWord_8166195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166195).length < 2 ^ (prefixWord ++ tailWord_8166195).sum := by decide
  have hdescent : baseEnd_8166195 < baseStart_8166195 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166202 : List Nat := [3, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2]
def baseStart_8166202 : Nat := 118140960795 + 8166202 * 2 ^ 59
def prefixEnd_8166202 : Nat := 4983230072969 + 3 ^ 40 * 8166202 * 2
def baseEnd_8166202 : Nat := 4193186747707363930819327

theorem tailTrace_8166202 : CollatzResearch.WordTrace tailWord_8166202 prefixEnd_8166202 4193186747707363930819327 := by
  unfold tailWord_8166202
  simp only [CollatzResearch.WordTrace]
  refine ⟨74461463990313076277715215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198563903974168203407240573 74461463990313076277715215)
  ·
    refine ⟨111692195985469614416572823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74461463990313076277715215 111692195985469614416572823)
    ·
      refine ⟨167538293978204421624859235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111692195985469614416572823 167538293978204421624859235)
      ·
        refine ⟨251307440967306632437288853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167538293978204421624859235 251307440967306632437288853)
        ·
          refine ⟨11780036295342498395497915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 251307440967306632437288853 11780036295342498395497915)
          ·
            refine ⟨17670054443013747593246873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11780036295342498395497915 17670054443013747593246873)
            ·
              refine ⟨13252540832260310694935155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17670054443013747593246873 13252540832260310694935155)
              ·
                refine ⟨19878811248390466042402733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13252540832260310694935155 19878811248390466042402733)
                ·
                  refine ⟨7454554218146424765901025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19878811248390466042402733 7454554218146424765901025)
                  ·
                    refine ⟨5590915663609818574425769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7454554218146424765901025 5590915663609818574425769)
                    ·
                      refine ⟨4193186747707363930819327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5590915663609818574425769 4193186747707363930819327)
                      ·
                        rfl

theorem cell23_8166202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2].length) (baseStart_8166202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166202 prefixEnd_8166202 := by exact prefixLift 8166202
  have htrace : WordTrace (prefixWord ++ tailWord_8166202) baseStart_8166202 baseEnd_8166202 := by
    simpa [prefixWord, tailWord_8166202, baseEnd_8166202] using wordTrace_append hprefix tailTrace_8166202
  have hstable : (prefixWord ++ tailWord_8166202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166202).length < 2 ^ (prefixWord ++ tailWord_8166202).sum := by decide
  have hdescent : baseEnd_8166202 < baseStart_8166202 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166212 : List Nat := [2, 3, 4, 2, 1, 2, 1, 1, 1, 6]
def baseStart_8166212 : Nat := 118140960795 + 8166212 * 2 ^ 59
def prefixEnd_8166212 : Nat := 4983230072969 + 3 ^ 40 * 8166212 * 2
def baseEnd_8166212 : Nat := 1397730627504636297231427

theorem tailTrace_8166212 : CollatzResearch.WordTrace tailWord_8166212 prefixEnd_8166212 1397730627504636297231427 := by
  unfold tailWord_8166212
  simp only [CollatzResearch.WordTrace]
  refine ⟨148923110345608038409362445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198564147127477384545816593 148923110345608038409362445)
  ·
    refine ⟨55846166379603014403510917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148923110345608038409362445 55846166379603014403510917)
    ·
      refine ⟨10471156196175565200658297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55846166379603014403510917 10471156196175565200658297)
      ·
        refine ⟨7853367147131673900493723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10471156196175565200658297 7853367147131673900493723)
        ·
          refine ⟨11780050720697510850740585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7853367147131673900493723 11780050720697510850740585)
          ·
            refine ⟨8835038040523133138055439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11780050720697510850740585 8835038040523133138055439)
            ·
              refine ⟨13252557060784699707083159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8835038040523133138055439 13252557060784699707083159)
              ·
                refine ⟨19878835591177049560624739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13252557060784699707083159 19878835591177049560624739)
                ·
                  refine ⟨29818253386765574340937109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19878835591177049560624739 29818253386765574340937109)
                  ·
                    refine ⟨1397730627504636297231427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29818253386765574340937109 1397730627504636297231427)
                    ·
                      rfl

theorem cell23_8166212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_8166212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166212 prefixEnd_8166212 := by exact prefixLift 8166212
  have htrace : WordTrace (prefixWord ++ tailWord_8166212) baseStart_8166212 baseEnd_8166212 := by
    simpa [prefixWord, tailWord_8166212, baseEnd_8166212] using wordTrace_append hprefix tailTrace_8166212
  have hstable : (prefixWord ++ tailWord_8166212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166212).length < 2 ^ (prefixWord ++ tailWord_8166212).sum := by decide
  have hdescent : baseEnd_8166212 < baseStart_8166212 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166225 : List Nat := [1, 2, 2, 1, 7, 1, 2, 7]
def baseStart_8166225 : Nat := 118140960795 + 8166225 * 2 ^ 59
def prefixEnd_8166225 : Nat := 4983230072969 + 3 ^ 40 * 8166225 * 2
def baseEnd_8166225 : Nat := 155303650287496938549323

theorem tailTrace_8166225 : CollatzResearch.WordTrace tailWord_8166225 prefixEnd_8166225 155303650287496938549323 := by
  unfold tailWord_8166225
  simp only [CollatzResearch.WordTrace]
  refine ⟨297846694840168980038948129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198564463226779320025965419 297846694840168980038948129)
  ·
    refine ⟨223385021130126735029211097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297846694840168980038948129 223385021130126735029211097)
    ·
      refine ⟨167538765847595051271908323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223385021130126735029211097 167538765847595051271908323)
      ·
        refine ⟨251308148771392576907862485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167538765847595051271908323 251308148771392576907862485)
        ·
          refine ⟨5890034736829513521278027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 251308148771392576907862485 5890034736829513521278027)
          ·
            refine ⟨8835052105244270281917041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5890034736829513521278027 8835052105244270281917041)
            ·
              refine ⟨6626289078933202711437781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8835052105244270281917041 6626289078933202711437781)
              ·
                refine ⟨155303650287496938549323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6626289078933202711437781 155303650287496938549323)
                ·
                  rfl

theorem cell23_8166225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 7].length) (baseStart_8166225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166225 prefixEnd_8166225 := by exact prefixLift 8166225
  have htrace : WordTrace (prefixWord ++ tailWord_8166225) baseStart_8166225 baseEnd_8166225 := by
    simpa [prefixWord, tailWord_8166225, baseEnd_8166225] using wordTrace_append hprefix tailTrace_8166225
  have hstable : (prefixWord ++ tailWord_8166225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166225).length < 2 ^ (prefixWord ++ tailWord_8166225).sum := by decide
  have hdescent : baseEnd_8166225 < baseStart_8166225 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166231 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 5]
def baseStart_8166231 : Nat := 118140960795 + 8166231 * 2 ^ 59
def prefixEnd_8166231 : Nat := 4983230072969 + 3 ^ 40 * 8166231 * 2
def baseEnd_8166231 : Nat := 4193201638646344317356693

theorem tailTrace_8166231 : CollatzResearch.WordTrace tailWord_8166231 prefixEnd_8166231 4193201638646344317356693 := by
  unfold tailWord_8166231
  simp only [CollatzResearch.WordTrace]
  refine ⟨297846913678147243063666547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198564609118764828709111031 297846913678147243063666547)
  ·
    refine ⟨446770370517220864595499821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297846913678147243063666547 446770370517220864595499821)
    ·
      refine ⟨167538888943957824223312433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446770370517220864595499821 167538888943957824223312433)
      ·
        refine ⟨125654166707968368167484325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167538888943957824223312433 125654166707968368167484325)
        ·
          refine ⟨23560156257744069031403311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125654166707968368167484325 23560156257744069031403311)
          ·
            refine ⟨35340234386616103547104967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23560156257744069031403311 35340234386616103547104967)
            ·
              refine ⟨53010351579924155320657451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35340234386616103547104967 53010351579924155320657451)
              ·
                refine ⟨79515527369886232980986177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53010351579924155320657451 79515527369886232980986177)
                ·
                  refine ⟨59636645527414674735739633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79515527369886232980986177 59636645527414674735739633)
                  ·
                    refine ⟨44727484145561006051804725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59636645527414674735739633 44727484145561006051804725)
                    ·
                      refine ⟨4193201638646344317356693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44727484145561006051804725 4193201638646344317356693)
                      ·
                        rfl

theorem cell23_8166231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_8166231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166231 prefixEnd_8166231 := by exact prefixLift 8166231
  have htrace : WordTrace (prefixWord ++ tailWord_8166231) baseStart_8166231 baseEnd_8166231 := by
    simpa [prefixWord, tailWord_8166231, baseEnd_8166231] using wordTrace_append hprefix tailTrace_8166231
  have hstable : (prefixWord ++ tailWord_8166231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166231).length < 2 ^ (prefixWord ++ tailWord_8166231).sum := by decide
  have hdescent : baseEnd_8166231 < baseStart_8166231 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166236 : List Nat := [2, 2, 4, 2, 1, 3, 1, 3, 1, 2, 2]
def baseStart_8166236 : Nat := 118140960795 + 8166236 * 2 ^ 59
def prefixEnd_8166236 : Nat := 4983230072969 + 3 ^ 40 * 8166236 * 2
def baseEnd_8166236 : Nat := 4193204206049616797794171

theorem tailTrace_8166236 : CollatzResearch.WordTrace tailWord_8166236 prefixEnd_8166236 4193204206049616797794171 := by
  unfold tailWord_8166236
  simp only [CollatzResearch.WordTrace]
  refine ⟨148923548021564564458799281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198564730695419419278399041 148923548021564564458799281)
  ·
    refine ⟨111692661016173423344099461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148923548021564564458799281 111692661016173423344099461)
    ·
      refine ⟨20942373940532516877018649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111692661016173423344099461 20942373940532516877018649)
      ·
        refine ⟨15706780455399387657763987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20942373940532516877018649 15706780455399387657763987)
        ·
          refine ⟨23560170683099081486645981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15706780455399387657763987 23560170683099081486645981)
          ·
            refine ⟨8835064006162155557492243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23560170683099081486645981 8835064006162155557492243)
            ·
              refine ⟨13252596009243233336238365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8835064006162155557492243 13252596009243233336238365)
              ·
                refine ⟨4969723503466212501089387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13252596009243233336238365 4969723503466212501089387)
                ·
                  refine ⟨7454585255199318751634081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4969723503466212501089387 7454585255199318751634081)
                  ·
                    refine ⟨5590938941399489063725561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7454585255199318751634081 5590938941399489063725561)
                    ·
                      refine ⟨4193204206049616797794171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5590938941399489063725561 4193204206049616797794171)
                      ·
                        rfl

theorem cell23_8166236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_8166236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166236 prefixEnd_8166236 := by exact prefixLift 8166236
  have htrace : WordTrace (prefixWord ++ tailWord_8166236) baseStart_8166236 baseEnd_8166236 := by
    simpa [prefixWord, tailWord_8166236, baseEnd_8166236] using wordTrace_append hprefix tailTrace_8166236
  have hstable : (prefixWord ++ tailWord_8166236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166236).length < 2 ^ (prefixWord ++ tailWord_8166236).sum := by decide
  have hdescent : baseEnd_8166236 < baseStart_8166236 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166245 : List Nat := [1, 3, 1, 3, 1, 1, 4, 3, 1, 3, 2]
def baseStart_8166245 : Nat := 118140960795 + 8166245 * 2 ^ 59
def prefixEnd_8166245 : Nat := 4983230072969 + 3 ^ 40 * 8166245 * 2
def baseEnd_8166245 : Nat := 4193208827375507262581629

theorem tailTrace_8166245 : CollatzResearch.WordTrace tailWord_8166245 prefixEnd_8166245 4193208827375507262581629 := by
  unfold tailWord_8166245
  simp only [CollatzResearch.WordTrace]
  refine ⟨297847424300096523454676189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198564949533397682303117459 297847424300096523454676189)
  ·
    refine ⟨111692784112536196295503571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297847424300096523454676189 111692784112536196295503571)
    ·
      refine ⟨167539176168804294443255357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111692784112536196295503571 167539176168804294443255357)
      ·
        refine ⟨62827191063301610416220759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167539176168804294443255357 62827191063301610416220759)
        ·
          refine ⟨94240786594952415624331139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62827191063301610416220759 94240786594952415624331139)
          ·
            refine ⟨141361179892428623436496709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94240786594952415624331139 141361179892428623436496709)
            ·
              refine ⟨26505221229830366894343133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141361179892428623436496709 26505221229830366894343133)
              ·
                refine ⟨9939457961186387585378675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26505221229830366894343133 9939457961186387585378675)
                ·
                  refine ⟨14909186941779581378068013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9939457961186387585378675 14909186941779581378068013)
                  ·
                    refine ⟨5590945103167343016775505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14909186941779581378068013 5590945103167343016775505)
                    ·
                      refine ⟨4193208827375507262581629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5590945103167343016775505 4193208827375507262581629)
                      ·
                        rfl

theorem cell23_8166245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_8166245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166245 prefixEnd_8166245 := by exact prefixLift 8166245
  have htrace : WordTrace (prefixWord ++ tailWord_8166245) baseStart_8166245 baseEnd_8166245 := by
    simpa [prefixWord, tailWord_8166245, baseEnd_8166245] using wordTrace_append hprefix tailTrace_8166245
  have hstable : (prefixWord ++ tailWord_8166245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166245).length < 2 ^ (prefixWord ++ tailWord_8166245).sum := by decide
  have hdescent : baseEnd_8166245 < baseStart_8166245 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166271 : List Nat := [1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 4]
def baseStart_8166271 : Nat := 118140960795 + 8166271 * 2 ^ 59
def prefixEnd_8166271 : Nat := 4983230072969 + 3 ^ 40 * 8166271 * 2
def baseEnd_8166271 : Nat := 4193222177872524160856509

theorem tailTrace_8166271 : CollatzResearch.WordTrace tailWord_8166271 prefixEnd_8166271 4193222177872524160856509 := by
  unfold tailWord_8166271
  simp only [CollatzResearch.WordTrace]
  refine ⟨297848372598002329895122667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198565581732001553263415111 297848372598002329895122667)
  ·
    refine ⟨446772558897003494842684001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297848372598002329895122667 446772558897003494842684001)
    ·
      refine ⟨335079419172752621132013001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446772558897003494842684001 335079419172752621132013001)
      ·
        refine ⟨251309564379564465849009751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335079419172752621132013001 251309564379564465849009751)
        ·
          refine ⟨376964346569346698773514627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251309564379564465849009751 376964346569346698773514627)
          ·
            refine ⟨565446519854020048160271941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376964346569346698773514627 565446519854020048160271941)
            ·
              refine ⟨106021222472628759030050989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 565446519854020048160271941 106021222472628759030050989)
              ·
                refine ⟨39757958427235784636269121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106021222472628759030050989 39757958427235784636269121)
                ·
                  refine ⟨29818468820426838477201841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39757958427235784636269121 29818468820426838477201841)
                  ·
                    refine ⟨22363851615320128857901381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29818468820426838477201841 22363851615320128857901381)
                    ·
                      refine ⟨4193222177872524160856509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22363851615320128857901381 4193222177872524160856509)
                      ·
                        rfl

theorem cell23_8166271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_8166271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166271 prefixEnd_8166271 := by exact prefixLift 8166271
  have htrace : WordTrace (prefixWord ++ tailWord_8166271) baseStart_8166271 baseEnd_8166271 := by
    simpa [prefixWord, tailWord_8166271, baseEnd_8166271] using wordTrace_append hprefix tailTrace_8166271
  have hstable : (prefixWord ++ tailWord_8166271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166271).length < 2 ^ (prefixWord ++ tailWord_8166271).sum := by decide
  have hdescent : baseEnd_8166271 < baseStart_8166271 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166291 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 3, 5, 3]
def baseStart_8166291 : Nat := 118140960795 + 8166291 * 2 ^ 59
def prefixEnd_8166291 : Nat := 4983230072969 + 3 ^ 40 * 8166291 * 2
def baseEnd_8166291 : Nat := 4193232447485614082606417

theorem tailTrace_8166291 : CollatzResearch.WordTrace tailWord_8166291 prefixEnd_8166291 4193232447485614082606417 := by
  unfold tailWord_8166291
  simp only [CollatzResearch.WordTrace]
  refine ⟨297849102057929873310850727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198566068038619915540567151 297849102057929873310850727)
  ·
    refine ⟨446773653086894809966276091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297849102057929873310850727 446773653086894809966276091)
    ·
      refine ⟨670160479630342214949414137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446773653086894809966276091 670160479630342214949414137)
      ·
        refine ⟨502620359722756661212060603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 670160479630342214949414137 502620359722756661212060603)
        ·
          refine ⟨753930539584134991818090905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502620359722756661212060603 753930539584134991818090905)
          ·
            refine ⟨565447904688101243863568179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 753930539584134991818090905 565447904688101243863568179)
            ·
              refine ⟨848171857032151865795352269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565447904688101243863568179 848171857032151865795352269)
              ·
                refine ⟨318064446387056949673257101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 848171857032151865795352269 318064446387056949673257101)
                ·
                  refine ⟨119274167395146356127471413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 318064446387056949673257101 119274167395146356127471413)
                  ·
                    refine ⟨11181953193294970886950445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 119274167395146356127471413 11181953193294970886950445)
                    ·
                      refine ⟨4193232447485614082606417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11181953193294970886950445 4193232447485614082606417)
                      ·
                        rfl

theorem cell23_8166291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5, 3].length) (baseStart_8166291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166291 prefixEnd_8166291 := by exact prefixLift 8166291
  have htrace : WordTrace (prefixWord ++ tailWord_8166291) baseStart_8166291 baseEnd_8166291 := by
    simpa [prefixWord, tailWord_8166291, baseEnd_8166291] using wordTrace_append hprefix tailTrace_8166291
  have hstable : (prefixWord ++ tailWord_8166291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166291).length < 2 ^ (prefixWord ++ tailWord_8166291).sum := by decide
  have hdescent : baseEnd_8166291 < baseStart_8166291 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166308 : List Nat := [2, 3, 1, 2, 1, 2, 2, 2, 2, 3, 3]
def baseStart_8166308 : Nat := 118140960795 + 8166308 * 2 ^ 59
def prefixEnd_8166308 : Nat := 4983230072969 + 3 ^ 40 * 8166308 * 2
def baseEnd_8166308 : Nat := 4193241176656740516093839

theorem tailTrace_8166308 : CollatzResearch.WordTrace tailWord_8166308 prefixEnd_8166308 4193241176656740516093839 := by
  unfold tailWord_8166308
  simp only [CollatzResearch.WordTrace]
  refine ⟨148924861049434142607109789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198566481399245523476146385 148924861049434142607109789)
  ·
    refine ⟨55846822893537803477666171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148924861049434142607109789 55846822893537803477666171)
    ·
      refine ⟨83770234340306705216499257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55846822893537803477666171 83770234340306705216499257)
      ·
        refine ⟨62827675755230028912374443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83770234340306705216499257 62827675755230028912374443)
        ·
          refine ⟨94241513632845043368561665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62827675755230028912374443 94241513632845043368561665)
          ·
            refine ⟨70681135224633782526421249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94241513632845043368561665 70681135224633782526421249)
            ·
              refine ⟨53010851418475336894815937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70681135224633782526421249 53010851418475336894815937)
              ·
                refine ⟨39758138563856502671111953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53010851418475336894815937 39758138563856502671111953)
                ·
                  refine ⟨29818603922892377003333965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39758138563856502671111953 29818603922892377003333965)
                  ·
                    refine ⟨11181976471084641376250237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29818603922892377003333965 11181976471084641376250237)
                    ·
                      refine ⟨4193241176656740516093839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11181976471084641376250237 4193241176656740516093839)
                      ·
                        rfl

theorem cell23_8166308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_8166308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166308 prefixEnd_8166308 := by exact prefixLift 8166308
  have htrace : WordTrace (prefixWord ++ tailWord_8166308) baseStart_8166308 baseEnd_8166308 := by
    simpa [prefixWord, tailWord_8166308, baseEnd_8166308] using wordTrace_append hprefix tailTrace_8166308
  have hstable : (prefixWord ++ tailWord_8166308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166308).length < 2 ^ (prefixWord ++ tailWord_8166308).sum := by decide
  have hdescent : baseEnd_8166308 < baseStart_8166308 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166348 : List Nat := [2, 2, 1, 4, 1, 1, 3, 1, 1, 3, 4]
def baseStart_8166348 : Nat := 118140960795 + 8166348 * 2 ^ 59
def prefixEnd_8166348 : Nat := 4983230072969 + 3 ^ 40 * 8166348 * 2
def baseEnd_8166348 : Nat := 4193261715882920359593655

theorem tailTrace_8166348 : CollatzResearch.WordTrace tailWord_8166348 prefixEnd_8166348 4193261715882920359593655 := by
  unfold tailWord_8166348
  simp only [CollatzResearch.WordTrace]
  refine ⟨148925590509361686022837849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198567454012482248030450465 148925590509361686022837849)
  ·
    refine ⟨111694192882021264517128387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148925590509361686022837849 111694192882021264517128387)
    ·
      refine ⟨167541289323031896775692581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111694192882021264517128387 167541289323031896775692581)
      ·
        refine ⟨31413991748068480645442359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167541289323031896775692581 31413991748068480645442359)
        ·
          refine ⟨47120987622102720968163539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31413991748068480645442359 47120987622102720968163539)
          ·
            refine ⟨70681481433154081452245309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47120987622102720968163539 70681481433154081452245309)
            ·
              refine ⟨26505555537432780544591991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70681481433154081452245309 26505555537432780544591991)
              ·
                refine ⟨39758333306149170816887987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26505555537432780544591991 39758333306149170816887987)
                ·
                  refine ⟨59637499959223756225331981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39758333306149170816887987 59637499959223756225331981)
                  ·
                    refine ⟨22364062484708908584499493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59637499959223756225331981 22364062484708908584499493)
                    ·
                      refine ⟨4193261715882920359593655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22364062484708908584499493 4193261715882920359593655)
                      ·
                        rfl

theorem cell23_8166348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_8166348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166348 prefixEnd_8166348 := by exact prefixLift 8166348
  have htrace : WordTrace (prefixWord ++ tailWord_8166348) baseStart_8166348 baseEnd_8166348 := by
    simpa [prefixWord, tailWord_8166348, baseEnd_8166348] using wordTrace_append hprefix tailTrace_8166348
  have hstable : (prefixWord ++ tailWord_8166348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166348).length < 2 ^ (prefixWord ++ tailWord_8166348).sum := by decide
  have hdescent : baseEnd_8166348 < baseStart_8166348 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166375 : List Nat := [1, 1, 5, 2, 2, 1, 1, 3, 3, 4]
def baseStart_8166375 : Nat := 118140960795 + 8166375 * 2 ^ 59
def prefixEnd_8166375 : Nat := 4983230072969 + 3 ^ 40 * 8166375 * 2
def baseEnd_8166375 : Nat := 1397758526620197251318677

theorem tailTrace_8166375 : CollatzResearch.WordTrace tailWord_8166375 prefixEnd_8166375 1397758526620197251318677 := by
  unfold tailWord_8166375
  simp only [CollatzResearch.WordTrace]
  refine ⟨297852165789625555656908579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198568110526417037104605719 297852165789625555656908579)
  ·
    refine ⟨446778248684438333485362869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297852165789625555656908579 446778248684438333485362869)
    ·
      refine ⟨41885460814166093764252769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 446778248684438333485362869 41885460814166093764252769)
      ·
        refine ⟨31414095610624570323189577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41885460814166093764252769 31414095610624570323189577)
        ·
          refine ⟨23560571707968427742392183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31414095610624570323189577 23560571707968427742392183)
          ·
            refine ⟨35340857561952641613588275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23560571707968427742392183 35340857561952641613588275)
            ·
              refine ⟨53011286342928962420382413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35340857561952641613588275 53011286342928962420382413)
              ·
                refine ⟨19879232378598360907643405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53011286342928962420382413 19879232378598360907643405)
                ·
                  refine ⟨7454712141974385340366277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19879232378598360907643405 7454712141974385340366277)
                  ·
                    refine ⟨1397758526620197251318677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7454712141974385340366277 1397758526620197251318677)
                    ·
                      rfl

theorem cell23_8166375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_8166375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166375 prefixEnd_8166375 := by exact prefixLift 8166375
  have htrace : WordTrace (prefixWord ++ tailWord_8166375) baseStart_8166375 baseEnd_8166375 := by
    simpa [prefixWord, tailWord_8166375, baseEnd_8166375] using wordTrace_append hprefix tailTrace_8166375
  have hstable : (prefixWord ++ tailWord_8166375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166375).length < 2 ^ (prefixWord ++ tailWord_8166375).sum := by decide
  have hdescent : baseEnd_8166375 < baseStart_8166375 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166425 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 4, 3, 2]
def baseStart_8166425 : Nat := 118140960795 + 8166425 * 2 ^ 59
def prefixEnd_8166425 : Nat := 4983230072969 + 3 ^ 40 * 8166425 * 2
def baseEnd_8166425 : Nat := 4193301253893316558330801

theorem tailTrace_8166425 : CollatzResearch.WordTrace tailWord_8166425 prefixEnd_8166425 4193301253893316558330801 := by
  unfold tailWord_8166425
  simp only [CollatzResearch.WordTrace]
  refine ⟨297853989439444414196228729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198569326292962942797485819 297853989439444414196228729)
  ·
    refine ⟨223390492079583310647171547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297853989439444414196228729 223390492079583310647171547)
    ·
      refine ⟨335085738119374965970757321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223390492079583310647171547 335085738119374965970757321)
      ·
        refine ⟨251314303589531224478067991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335085738119374965970757321 251314303589531224478067991)
        ·
          refine ⟨376971455384296836717101987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251314303589531224478067991 376971455384296836717101987)
          ·
            refine ⟨565457183076445255075652981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376971455384296836717101987 565457183076445255075652981)
            ·
              refine ⟨53011610913416742663342467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 565457183076445255075652981 53011610913416742663342467)
              ·
                refine ⟨79517416370125113995013701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53011610913416742663342467 79517416370125113995013701)
                ·
                  refine ⟨14909515569398458874065069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79517416370125113995013701 14909515569398458874065069)
                  ·
                    refine ⟨5591068338524422077774401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14909515569398458874065069 5591068338524422077774401)
                    ·
                      refine ⟨4193301253893316558330801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5591068338524422077774401 4193301253893316558330801)
                      ·
                        rfl

theorem cell23_8166425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 3, 2].length) (baseStart_8166425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166425 prefixEnd_8166425 := by exact prefixLift 8166425
  have htrace : WordTrace (prefixWord ++ tailWord_8166425) baseStart_8166425 baseEnd_8166425 := by
    simpa [prefixWord, tailWord_8166425, baseEnd_8166425] using wordTrace_append hprefix tailTrace_8166425
  have hstable : (prefixWord ++ tailWord_8166425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166425).length < 2 ^ (prefixWord ++ tailWord_8166425).sum := by decide
  have hdescent : baseEnd_8166425 < baseStart_8166425 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166439 : List Nat := [1, 1, 7, 1, 1, 3, 2, 1, 6]
def baseStart_8166439 : Nat := 118140960795 + 8166439 * 2 ^ 59
def prefixEnd_8166439 : Nat := 4983230072969 + 3 ^ 40 * 8166439 * 2
def baseEnd_8166439 : Nat := 465923160291386611506193

theorem tailTrace_8166439 : CollatzResearch.WordTrace tailWord_8166439 prefixEnd_8166439 465923160291386611506193 := by
  unfold tailWord_8166439
  simp only [CollatzResearch.WordTrace]
  refine ⟨297854500061393694587238371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198569666707595796391492247 297854500061393694587238371)
  ·
    refine ⟨446781750092090541880857557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297854500061393694587238371 446781750092090541880857557)
    ·
      refine ⟨10471447267783372075332599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 446781750092090541880857557 10471447267783372075332599)
      ·
        refine ⟨15707170901675058112998899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10471447267783372075332599 15707170901675058112998899)
        ·
          refine ⟨23560756352512587169498349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15707170901675058112998899 23560756352512587169498349)
          ·
            refine ⟨8835283632192220188561881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23560756352512587169498349 8835283632192220188561881)
            ·
              refine ⟨6626462724144165141421411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8835283632192220188561881 6626462724144165141421411)
              ·
                refine ⟨9939694086216247712132117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6626462724144165141421411 9939694086216247712132117)
                ·
                  refine ⟨465923160291386611506193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9939694086216247712132117 465923160291386611506193)
                  ·
                    rfl

theorem cell23_8166439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 6].length) (baseStart_8166439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166439 prefixEnd_8166439 := by exact prefixLift 8166439
  have htrace : WordTrace (prefixWord ++ tailWord_8166439) baseStart_8166439 baseEnd_8166439 := by
    simpa [prefixWord, tailWord_8166439, baseEnd_8166439] using wordTrace_append hprefix tailTrace_8166439
  have hstable : (prefixWord ++ tailWord_8166439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166439).length < 2 ^ (prefixWord ++ tailWord_8166439).sum := by decide
  have hdescent : baseEnd_8166439 < baseStart_8166439 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166448 : List Nat := [2, 1, 1, 1, 2, 4, 2, 3, 1, 6]
def baseStart_8166448 : Nat := 118140960795 + 8166448 * 2 ^ 59
def prefixEnd_8166448 : Nat := 4983230072969 + 3 ^ 40 * 8166448 * 2
def baseEnd_8166448 : Nat := 1397771021316123322781065

theorem tailTrace_8166448 : CollatzResearch.WordTrace tailWord_8166448 prefixEnd_8166448 1397771021316123322781065 := by
  unfold tailWord_8166448
  simp only [CollatzResearch.WordTrace]
  refine ⟨148927414159180544562157999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198569885545574059416210665 148927414159180544562157999)
  ·
    refine ⟨223391121238770816843236999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148927414159180544562157999 223391121238770816843236999)
    ·
      refine ⟨335086681858156225264855499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223391121238770816843236999 335086681858156225264855499)
      ·
        refine ⟨502630022787234337897283249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335086681858156225264855499 502630022787234337897283249)
        ·
          refine ⟨376972517090425753422962437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502630022787234337897283249 376972517090425753422962437)
          ·
            refine ⟨70682346954454828766805457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 376972517090425753422962437 70682346954454828766805457)
            ·
              refine ⟨53011760215841121575104093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70682346954454828766805457 53011760215841121575104093)
              ·
                refine ⟨19879410080940420590664035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53011760215841121575104093 19879410080940420590664035)
                ·
                  refine ⟨29819115121410630885996053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19879410080940420590664035 29819115121410630885996053)
                  ·
                    refine ⟨1397771021316123322781065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29819115121410630885996053 1397771021316123322781065)
                    ·
                      rfl

theorem cell23_8166448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 1, 6].length) (baseStart_8166448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166448 prefixEnd_8166448 := by exact prefixLift 8166448
  have htrace : WordTrace (prefixWord ++ tailWord_8166448) baseStart_8166448 baseEnd_8166448 := by
    simpa [prefixWord, tailWord_8166448, baseEnd_8166448] using wordTrace_append hprefix tailTrace_8166448
  have hstable : (prefixWord ++ tailWord_8166448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166448).length < 2 ^ (prefixWord ++ tailWord_8166448).sum := by decide
  have hdescent : baseEnd_8166448 < baseStart_8166448 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166452 : List Nat := [2, 5, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_8166452 : Nat := 118140960795 + 8166452 * 2 ^ 59
def prefixEnd_8166452 : Nat := 4983230072969 + 3 ^ 40 * 8166452 * 2
def baseEnd_8166452 : Nat := 1397771705956995984231059

theorem tailTrace_8166452 : CollatzResearch.WordTrace tailWord_8166452 prefixEnd_8166452 1397771705956995984231059 := by
  unfold tailWord_8166452
  simp only [CollatzResearch.WordTrace]
  refine ⟨148927487105173298903730805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198569982806897731871641073 148927487105173298903730805)
  ·
    refine ⟨13961951916109996772224763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148927487105173298903730805 13961951916109996772224763)
    ·
      refine ⟨20942927874164995158337145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13961951916109996772224763 20942927874164995158337145)
      ·
        refine ⟨15707195905623746368752859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20942927874164995158337145 15707195905623746368752859)
        ·
          refine ⟨23560793858435619553129289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15707195905623746368752859 23560793858435619553129289)
          ·
            refine ⟨17670595393826714664846967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23560793858435619553129289 17670595393826714664846967)
            ·
              refine ⟨26505893090740071997270451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17670595393826714664846967 26505893090740071997270451)
              ·
                refine ⟨39758839636110107995905677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26505893090740071997270451 39758839636110107995905677)
                ·
                  refine ⟨14909564863541290498464629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39758839636110107995905677 14909564863541290498464629)
                  ·
                    refine ⟨1397771705956995984231059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14909564863541290498464629 1397771705956995984231059)
                    ·
                      rfl

theorem cell23_8166452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_8166452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166452 prefixEnd_8166452 := by exact prefixLift 8166452
  have htrace : WordTrace (prefixWord ++ tailWord_8166452) baseStart_8166452 baseEnd_8166452 := by
    simpa [prefixWord, tailWord_8166452, baseEnd_8166452] using wordTrace_append hprefix tailTrace_8166452
  have hstable : (prefixWord ++ tailWord_8166452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166452).length < 2 ^ (prefixWord ++ tailWord_8166452).sum := by decide
  have hdescent : baseEnd_8166452 < baseStart_8166452 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166458 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5]
def baseStart_8166458 : Nat := 118140960795 + 8166458 * 2 ^ 59
def prefixEnd_8166458 : Nat := 4983230072969 + 3 ^ 40 * 8166458 * 2
def baseEnd_8166458 : Nat := 4193318198754914929218149

theorem tailTrace_8166458 : CollatzResearch.WordTrace tailWord_8166458 prefixEnd_8166458 4193318198754914929218149 := by
  unfold tailWord_8166458
  simp only [CollatzResearch.WordTrace]
  refine ⟨74463798262081215208045007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198570128698883240554786685 74463798262081215208045007)
  ·
    refine ⟨111695697393121822812067511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74463798262081215208045007 111695697393121822812067511)
    ·
      refine ⟨167543546089682734218101267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111695697393121822812067511 167543546089682734218101267)
      ·
        refine ⟨251315319134524101327151901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167543546089682734218101267 251315319134524101327151901)
        ·
          refine ⟨94243244675446537997681963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251315319134524101327151901 94243244675446537997681963)
          ·
            refine ⟨141364867013169806996522945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94243244675446537997681963 141364867013169806996522945)
            ·
              refine ⟨106023650259877355247392209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141364867013169806996522945 106023650259877355247392209)
              ·
                refine ⟨79517737694908016435544157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106023650259877355247392209 79517737694908016435544157)
                ·
                  refine ⟨29819151635590506163329059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79517737694908016435544157 29819151635590506163329059)
                  ·
                    refine ⟨44728727453385759244993589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29819151635590506163329059 44728727453385759244993589)
                    ·
                      refine ⟨4193318198754914929218149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44728727453385759244993589 4193318198754914929218149)
                      ·
                        rfl

theorem cell23_8166458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_8166458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166458 prefixEnd_8166458 := by exact prefixLift 8166458
  have htrace : WordTrace (prefixWord ++ tailWord_8166458) baseStart_8166458 baseEnd_8166458 := by
    simpa [prefixWord, tailWord_8166458, baseEnd_8166458] using wordTrace_append hprefix tailTrace_8166458
  have hstable : (prefixWord ++ tailWord_8166458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166458).length < 2 ^ (prefixWord ++ tailWord_8166458).sum := by decide
  have hdescent : baseEnd_8166458 < baseStart_8166458 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166472 : List Nat := [2, 1, 3, 1, 1, 1, 7, 1, 1, 1, 4]
def baseStart_8166472 : Nat := 118140960795 + 8166472 * 2 ^ 59
def prefixEnd_8166472 : Nat := 4983230072969 + 3 ^ 40 * 8166472 * 2
def baseEnd_8166472 : Nat := 4193325387484077874443085

theorem tailTrace_8166472 : CollatzResearch.WordTrace tailWord_8166472 prefixEnd_8166472 4193325387484077874443085 := by
  unfold tailWord_8166472
  simp only [CollatzResearch.WordTrace]
  refine ⟨148927851835137070611594835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198570469113516094148793113 148927851835137070611594835)
  ·
    refine ⟨223391777752705605917392253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148927851835137070611594835 223391777752705605917392253)
    ·
      refine ⟨83771916657264602219022095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223391777752705605917392253 83771916657264602219022095)
      ·
        refine ⟨125657874985896903328533143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83771916657264602219022095 125657874985896903328533143)
        ·
          refine ⟨188486812478845354992799715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125657874985896903328533143 188486812478845354992799715)
          ·
            refine ⟨282730218718268032489199573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188486812478845354992799715 282730218718268032489199573)
            ·
              refine ⟨6626489501209407011465615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 282730218718268032489199573 6626489501209407011465615)
              ·
                refine ⟨9939734251814110517198423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6626489501209407011465615 9939734251814110517198423)
                ·
                  refine ⟨14909601377721165775797635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9939734251814110517198423 14909601377721165775797635)
                  ·
                    refine ⟨22364402066581748663696453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14909601377721165775797635 22364402066581748663696453)
                    ·
                      refine ⟨4193325387484077874443085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22364402066581748663696453 4193325387484077874443085)
                      ·
                        rfl

theorem cell23_8166472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 1, 1, 4].length) (baseStart_8166472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166472 prefixEnd_8166472 := by exact prefixLift 8166472
  have htrace : WordTrace (prefixWord ++ tailWord_8166472) baseStart_8166472 baseEnd_8166472 := by
    simpa [prefixWord, tailWord_8166472, baseEnd_8166472] using wordTrace_append hprefix tailTrace_8166472
  have hstable : (prefixWord ++ tailWord_8166472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166472).length < 2 ^ (prefixWord ++ tailWord_8166472).sum := by decide
  have hdescent : baseEnd_8166472 < baseStart_8166472 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166482 : List Nat := [3, 2, 2, 1, 3, 1, 1, 4, 2, 4]
def baseStart_8166482 : Nat := 118140960795 + 8166482 * 2 ^ 59
def prefixEnd_8166482 : Nat := 4983230072969 + 3 ^ 40 * 8166482 * 2
def baseEnd_8166482 : Nat := 1397776840763540945106013

theorem tailTrace_8166482 : CollatzResearch.WordTrace tailWord_8166482 prefixEnd_8166482 1397776840763540945106013 := by
  unfold tailWord_8166482
  simp only [CollatzResearch.WordTrace]
  refine ⟨74464017100059478232763425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198570712266825275287369133 74464017100059478232763425)
  ·
    refine ⟨55848012825044608674572569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74464017100059478232763425 55848012825044608674572569)
    ·
      refine ⟨41886009618783456505929427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55848012825044608674572569 41886009618783456505929427)
      ·
        refine ⟨62829014428175184758894141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41886009618783456505929427 62829014428175184758894141)
        ·
          refine ⟨23560880410565694284585303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62829014428175184758894141 23560880410565694284585303)
          ·
            refine ⟨35341320615848541426877955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23560880410565694284585303 35341320615848541426877955)
            ·
              refine ⟨53011980923772812140316933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35341320615848541426877955 53011980923772812140316933)
              ·
                refine ⟨9939746423207402276309425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53011980923772812140316933 9939746423207402276309425)
                ·
                  refine ⟨7454809817405551707232069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9939746423207402276309425 7454809817405551707232069)
                  ·
                    refine ⟨1397776840763540945106013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7454809817405551707232069 1397776840763540945106013)
                    ·
                      rfl

theorem cell23_8166482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_8166482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166482 prefixEnd_8166482 := by exact prefixLift 8166482
  have htrace : WordTrace (prefixWord ++ tailWord_8166482) baseStart_8166482 baseEnd_8166482 := by
    simpa [prefixWord, tailWord_8166482, baseEnd_8166482] using wordTrace_append hprefix tailTrace_8166482
  have hstable : (prefixWord ++ tailWord_8166482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166482).length < 2 ^ (prefixWord ++ tailWord_8166482).sum := by decide
  have hdescent : baseEnd_8166482 < baseStart_8166482 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166505 : List Nat := [1, 2, 1, 1, 1, 6, 1, 3, 1, 3, 3]
def baseStart_8166505 : Nat := 118140960795 + 8166505 * 2 ^ 59
def prefixEnd_8166505 : Nat := 4983230072969 + 3 ^ 40 * 8166505 * 2
def baseEnd_8166505 : Nat := 4193342332345676245330433

theorem tailTrace_8166505 : CollatzResearch.WordTrace tailWord_8166505 prefixEnd_8166505 4193342332345676245330433 := by
  unfold tailWord_8166505
  simp only [CollatzResearch.WordTrace]
  refine ⟨297856907279154587859140969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198571271519436391906093979 297856907279154587859140969)
  ·
    refine ⟨223392680459365940894355727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297856907279154587859140969 223392680459365940894355727)
    ·
      refine ⟨335089020689048911341533591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223392680459365940894355727 335089020689048911341533591)
      ·
        refine ⟨502633531033573367012300387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335089020689048911341533591 502633531033573367012300387)
        ·
          refine ⟨753950296550360050518450581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502633531033573367012300387 753950296550360050518450581)
          ·
            refine ⟨35341420150798127368052371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 753950296550360050518450581 35341420150798127368052371)
            ·
              refine ⟨53012130226197191052078557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35341420150798127368052371 53012130226197191052078557)
              ·
                refine ⟨19879548834823946644529459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53012130226197191052078557 19879548834823946644529459)
                ·
                  refine ⟨29819323252235919966794189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19879548834823946644529459 29819323252235919966794189)
                  ·
                    refine ⟨11182246219588469987547821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29819323252235919966794189 11182246219588469987547821)
                    ·
                      refine ⟨4193342332345676245330433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11182246219588469987547821 4193342332345676245330433)
                      ·
                        rfl

theorem cell23_8166505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 3, 3].length) (baseStart_8166505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166505 prefixEnd_8166505 := by exact prefixLift 8166505
  have htrace : WordTrace (prefixWord ++ tailWord_8166505) baseStart_8166505 baseEnd_8166505 := by
    simpa [prefixWord, tailWord_8166505, baseEnd_8166505] using wordTrace_append hprefix tailTrace_8166505
  have hstable : (prefixWord ++ tailWord_8166505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166505).length < 2 ^ (prefixWord ++ tailWord_8166505).sum := by decide
  have hdescent : baseEnd_8166505 < baseStart_8166505 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166508 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 2, 7]
def baseStart_8166508 : Nat := 118140960795 + 8166508 * 2 ^ 59
def prefixEnd_8166508 : Nat := 4983230072969 + 3 ^ 40 * 8166508 * 2
def baseEnd_8166508 : Nat := 1397781290929213244530973

theorem tailTrace_8166508 : CollatzResearch.WordTrace tailWord_8166508 prefixEnd_8166508 1397781290929213244530973 := by
  unfold tailWord_8166508
  simp only [CollatzResearch.WordTrace]
  refine ⟨148928508349071859685750089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198571344465429146247666785 148928508349071859685750089)
  ·
    refine ⟨111696381261803894764312567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148928508349071859685750089 111696381261803894764312567)
    ·
      refine ⟨167544571892705842146468851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111696381261803894764312567 167544571892705842146468851)
      ·
        refine ⟨251316857839058763219703277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167544571892705842146468851 251316857839058763219703277)
        ·
          refine ⟨94243821689647036207388729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251316857839058763219703277 94243821689647036207388729)
          ·
            refine ⟨70682866267235277155541547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94243821689647036207388729 70682866267235277155541547)
            ·
              refine ⟨106024299400852915733312321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70682866267235277155541547 106024299400852915733312321)
              ·
                refine ⟨79518224550639686799984241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106024299400852915733312321 79518224550639686799984241)
                ·
                  refine ⟨59638668412979765099988181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79518224550639686799984241 59638668412979765099988181)
                  ·
                    refine ⟨1397781290929213244530973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59638668412979765099988181 1397781290929213244530973)
                    ·
                      rfl

theorem cell23_8166508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_8166508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166508 prefixEnd_8166508 := by exact prefixLift 8166508
  have htrace : WordTrace (prefixWord ++ tailWord_8166508) baseStart_8166508 baseEnd_8166508 := by
    simpa [prefixWord, tailWord_8166508, baseEnd_8166508] using wordTrace_append hprefix tailTrace_8166508
  have hstable : (prefixWord ++ tailWord_8166508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166508).length < 2 ^ (prefixWord ++ tailWord_8166508).sum := by decide
  have hdescent : baseEnd_8166508 < baseStart_8166508 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166545 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 1, 10, 2]
def baseStart_8166545 : Nat := 118140960795 + 8166545 * 2 ^ 59
def prefixEnd_8166545 : Nat := 4983230072969 + 3 ^ 40 * 8166545 * 2
def baseEnd_8166545 : Nat := 4193362871571856088830249

theorem tailTrace_8166545 : CollatzResearch.WordTrace tailWord_8166545 prefixEnd_8166545 4193362871571856088830249 := by
  unfold tailWord_8166545
  simp only [CollatzResearch.WordTrace]
  refine ⟨297858366199009674690597089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198572244132673116460398059 297858366199009674690597089)
  ·
    refine ⟨223393774649257256017947817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297858366199009674690597089 223393774649257256017947817)
    ·
      refine ⟨167545330986942942013460863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223393774649257256017947817 167545330986942942013460863)
      ·
        refine ⟨251317996480414413020191295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167545330986942942013460863 251317996480414413020191295)
        ·
          refine ⟨376976994720621619530286943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251317996480414413020191295 376976994720621619530286943)
          ·
            refine ⟨565465492080932429295430415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376976994720621619530286943 565465492080932429295430415)
            ·
              refine ⟨848198238121398643943145623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565465492080932429295430415 848198238121398643943145623)
              ·
                refine ⟨1272297357182097965914718435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 848198238121398643943145623 1272297357182097965914718435)
                ·
                  refine ⟨1908446035773146948872077653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1272297357182097965914718435 1908446035773146948872077653)
                  ·
                    refine ⟨5591150495429141451773665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1908446035773146948872077653 5591150495429141451773665)
                    ·
                      refine ⟨4193362871571856088830249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5591150495429141451773665 4193362871571856088830249)
                      ·
                        rfl

theorem cell23_8166545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 10, 2].length) (baseStart_8166545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166545 prefixEnd_8166545 := by exact prefixLift 8166545
  have htrace : WordTrace (prefixWord ++ tailWord_8166545) baseStart_8166545 baseEnd_8166545 := by
    simpa [prefixWord, tailWord_8166545, baseEnd_8166545] using wordTrace_append hprefix tailTrace_8166545
  have hstable : (prefixWord ++ tailWord_8166545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166545).length < 2 ^ (prefixWord ++ tailWord_8166545).sum := by decide
  have hdescent : baseEnd_8166545 < baseStart_8166545 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166556 : List Nat := [2, 2, 3, 2, 1, 3, 3, 1, 2, 1, 3]
def baseStart_8166556 : Nat := 118140960795 + 8166556 * 2 ^ 59
def prefixEnd_8166556 : Nat := 4983230072969 + 3 ^ 40 * 8166556 * 2
def baseEnd_8166556 : Nat := 4193368519859055545792699

theorem tailTrace_8166556 : CollatzResearch.WordTrace tailWord_8166556 prefixEnd_8166556 4193368519859055545792699 := by
  unfold tailWord_8166556
  simp only [CollatzResearch.WordTrace]
  refine ⟨148929383700984911784623761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198572511601313215712831681 148929383700984911784623761)
  ·
    refine ⟨111697037775738683838467821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148929383700984911784623761 111697037775738683838467821)
    ·
      refine ⟨41886389165902006439425433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111697037775738683838467821 41886389165902006439425433)
      ·
        refine ⟨31414791874426504829569075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41886389165902006439425433 31414791874426504829569075)
        ·
          refine ⟨47122187811639757244353613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31414791874426504829569075 47122187811639757244353613)
          ·
            refine ⟨17670820429364908966632605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47122187811639757244353613 17670820429364908966632605)
            ·
              refine ⟨6626557661011840862487227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17670820429364908966632605 6626557661011840862487227)
              ·
                refine ⟨9939836491517761293730841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6626557661011840862487227 9939836491517761293730841)
                ·
                  refine ⟨7454877368638320970298131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9939836491517761293730841 7454877368638320970298131)
                  ·
                    refine ⟨11182316052957481455447197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7454877368638320970298131 11182316052957481455447197)
                    ·
                      refine ⟨4193368519859055545792699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11182316052957481455447197 4193368519859055545792699)
                      ·
                        rfl

theorem cell23_8166556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_8166556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166556 prefixEnd_8166556 := by exact prefixLift 8166556
  have htrace : WordTrace (prefixWord ++ tailWord_8166556) baseStart_8166556 baseEnd_8166556 := by
    simpa [prefixWord, tailWord_8166556, baseEnd_8166556] using wordTrace_append hprefix tailTrace_8166556
  have hstable : (prefixWord ++ tailWord_8166556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166556).length < 2 ^ (prefixWord ++ tailWord_8166556).sum := by decide
  have hdescent : baseEnd_8166556 < baseStart_8166556 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166595 : List Nat := [1, 1, 1, 3, 1, 1, 1, 6, 2, 3, 3]
def baseStart_8166595 : Nat := 118140960795 + 8166595 * 2 ^ 59
def prefixEnd_8166595 : Nat := 4983230072969 + 3 ^ 40 * 8166595 * 2
def baseEnd_8166595 : Nat := 4193388545604580893205019

theorem tailTrace_8166595 : CollatzResearch.WordTrace tailWord_8166595 prefixEnd_8166595 4193388545604580893205019 := by
  unfold tailWord_8166595
  simp only [CollatzResearch.WordTrace]
  refine ⟨297860189848828533229917239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198573459899219022153278159 297860189848828533229917239)
  ·
    refine ⟨446790284773242799844875859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297860189848828533229917239 446790284773242799844875859)
    ·
      refine ⟨670185427159864199767313789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446790284773242799844875859 670185427159864199767313789)
      ·
        refine ⟨251319535184949074912742671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 670185427159864199767313789 251319535184949074912742671)
        ·
          refine ⟨376979302777423612369114007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251319535184949074912742671 376979302777423612369114007)
          ·
            refine ⟨565468954166135418553671011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376979302777423612369114007 565468954166135418553671011)
            ·
              refine ⟨848203431249203127830506517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565468954166135418553671011 848203431249203127830506517)
              ·
                refine ⟨39759535839806396617054993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 848203431249203127830506517 39759535839806396617054993)
                ·
                  refine ⟨29819651879854797462791245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39759535839806396617054993 29819651879854797462791245)
                  ·
                    refine ⟨11182369454945549048546717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29819651879854797462791245 11182369454945549048546717)
                    ·
                      refine ⟨4193388545604580893205019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11182369454945549048546717 4193388545604580893205019)
                      ·
                        rfl

theorem cell23_8166595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3, 3].length) (baseStart_8166595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166595 prefixEnd_8166595 := by exact prefixLift 8166595
  have htrace : WordTrace (prefixWord ++ tailWord_8166595) baseStart_8166595 baseEnd_8166595 := by
    simpa [prefixWord, tailWord_8166595, baseEnd_8166595] using wordTrace_append hprefix tailTrace_8166595
  have hstable : (prefixWord ++ tailWord_8166595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166595).length < 2 ^ (prefixWord ++ tailWord_8166595).sum := by decide
  have hdescent : baseEnd_8166595 < baseStart_8166595 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166602 : List Nat := [3, 1, 2, 1, 3, 4, 1, 1, 7]
def baseStart_8166602 : Nat := 118140960795 + 8166602 * 2 ^ 59
def prefixEnd_8166602 : Nat := 4983230072969 + 3 ^ 40 * 8166602 * 2
def baseEnd_8166602 : Nat := 465932459996573596201943

theorem tailTrace_8166602 : CollatzResearch.WordTrace tailWord_8166602 prefixEnd_8166602 465932459996573596201943 := by
  unfold tailWord_8166602
  simp only [CollatzResearch.WordTrace]
  refine ⟨74465111289950793356355515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198573630106535448950281373 74465111289950793356355515)
  ·
    refine ⟨111697666934926190034533273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74465111289950793356355515 111697666934926190034533273)
    ·
      refine ⟨83773250201194642525899955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111697666934926190034533273 83773250201194642525899955)
      ·
        refine ⟨125659875301791963788849933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83773250201194642525899955 125659875301791963788849933)
        ·
          refine ⟨47122453238171986420818725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125659875301791963788849933 47122453238171986420818725)
          ·
            refine ⟨8835459982157247453903511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47122453238171986420818725 8835459982157247453903511)
            ·
              refine ⟨13253189973235871180855267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8835459982157247453903511 13253189973235871180855267)
              ·
                refine ⟨19879784959853806771282901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13253189973235871180855267 19879784959853806771282901)
                ·
                  refine ⟨465932459996573596201943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19879784959853806771282901 465932459996573596201943)
                  ·
                    rfl

theorem cell23_8166602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 7].length) (baseStart_8166602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166602 prefixEnd_8166602 := by exact prefixLift 8166602
  have htrace : WordTrace (prefixWord ++ tailWord_8166602) baseStart_8166602 baseEnd_8166602 := by
    simpa [prefixWord, tailWord_8166602, baseEnd_8166602] using wordTrace_append hprefix tailTrace_8166602
  have hstable : (prefixWord ++ tailWord_8166602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166602).length < 2 ^ (prefixWord ++ tailWord_8166602).sum := by decide
  have hdescent : baseEnd_8166602 < baseStart_8166602 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166613 : List Nat := [1, 3, 2, 4, 1, 1, 4, 1, 2, 2, 2]
def baseStart_8166613 : Nat := 118140960795 + 8166613 * 2 ^ 59
def prefixEnd_8166613 : Nat := 4983230072969 + 3 ^ 40 * 8166613 * 2
def baseEnd_8166613 : Nat := 4193397788256361822779937

theorem tailTrace_8166613 : CollatzResearch.WordTrace tailWord_8166613 prefixEnd_8166613 4193397788256361822779937 := by
  unfold tailWord_8166613
  simp only [CollatzResearch.WordTrace]
  refine ⟨297860846362763322304072493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198573897575175548202714995 297860846362763322304072493)
  ·
    refine ⟨111697817386036245864027185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297860846362763322304072493 111697817386036245864027185)
    ·
      refine ⟨83773363039527184398020389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111697817386036245864027185 83773363039527184398020389)
      ·
        refine ⟨15707505569911347074628823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83773363039527184398020389 15707505569911347074628823)
        ·
          refine ⟨23561258354867020611943235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15707505569911347074628823 23561258354867020611943235)
          ·
            refine ⟨35341887532300530917914853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23561258354867020611943235 35341887532300530917914853)
            ·
              refine ⟨6626603912306349547109035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35341887532300530917914853 6626603912306349547109035)
              ·
                refine ⟨9939905868459524320663553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6626603912306349547109035 9939905868459524320663553)
                ·
                  refine ⟨7454929401344643240497665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9939905868459524320663553 7454929401344643240497665)
                  ·
                    refine ⟨5591197051008482430373249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7454929401344643240497665 5591197051008482430373249)
                    ·
                      refine ⟨4193397788256361822779937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5591197051008482430373249 4193397788256361822779937)
                      ·
                        rfl

theorem cell23_8166613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_8166613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166613 prefixEnd_8166613 := by exact prefixLift 8166613
  have htrace : WordTrace (prefixWord ++ tailWord_8166613) baseStart_8166613 baseEnd_8166613 := by
    simpa [prefixWord, tailWord_8166613, baseEnd_8166613] using wordTrace_append hprefix tailTrace_8166613
  have hstable : (prefixWord ++ tailWord_8166613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166613).length < 2 ^ (prefixWord ++ tailWord_8166613).sum := by decide
  have hdescent : baseEnd_8166613 < baseStart_8166613 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166632 : List Nat := [2, 1, 4, 1, 2, 1, 4, 1, 2, 5]
def baseStart_8166632 : Nat := 118140960795 + 8166632 * 2 ^ 59
def prefixEnd_8166632 : Nat := 4983230072969 + 3 ^ 40 * 8166632 * 2
def baseEnd_8166632 : Nat := 1397802514796265749480783

theorem tailTrace_8166632 : CollatzResearch.WordTrace tailWord_8166632 prefixEnd_8166632 1397802514796265749480783 := by
  unfold tailWord_8166632
  simp only [CollatzResearch.WordTrace]
  refine ⟨148930769674847244274507075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198574359566462992366009433 148930769674847244274507075)
  ·
    refine ⟨223396154512270866411760613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148930769674847244274507075 223396154512270866411760613)
    ·
      refine ⟨41886778971050787452205115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223396154512270866411760613 41886778971050787452205115)
      ·
        refine ⟨62830168456576181178307673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41886778971050787452205115 62830168456576181178307673)
        ·
          refine ⟨47122626342432135883730755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62830168456576181178307673 47122626342432135883730755)
          ·
            refine ⟨70683939513648203825596133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47122626342432135883730755 70683939513648203825596133)
            ·
              refine ⟨13253238658809038217299275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70683939513648203825596133 13253238658809038217299275)
              ·
                refine ⟨19879857988213557325948913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13253238658809038217299275 19879857988213557325948913)
                ·
                  refine ⟨14909893491160167994461685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19879857988213557325948913 14909893491160167994461685)
                  ·
                    refine ⟨1397802514796265749480783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14909893491160167994461685 1397802514796265749480783)
                    ·
                      rfl

theorem cell23_8166632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_8166632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166632 prefixEnd_8166632 := by exact prefixLift 8166632
  have htrace : WordTrace (prefixWord ++ tailWord_8166632) baseStart_8166632 baseEnd_8166632 := by
    simpa [prefixWord, tailWord_8166632, baseEnd_8166632] using wordTrace_append hprefix tailTrace_8166632
  have hstable : (prefixWord ++ tailWord_8166632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166632).length < 2 ^ (prefixWord ++ tailWord_8166632).sum := by decide
  have hdescent : baseEnd_8166632 < baseStart_8166632 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166686 : List Nat := [4, 3, 2, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_8166686 : Nat := 118140960795 + 8166686 * 2 ^ 59
def prefixEnd_8166686 : Nat := 4983230072969 + 3 ^ 40 * 8166686 * 2
def baseEnd_8166686 : Nat := 4193435272344140037167101

theorem tailTrace_8166686 : CollatzResearch.WordTrace tailWord_8166686 prefixEnd_8166686 4193435272344140037167101 := by
  unfold tailWord_8166686
  simp only [CollatzResearch.WordTrace]
  refine ⟨37232938611437356971434989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198575672594332570514319941 37232938611437356971434989)
  ·
    refine ⟨13962351979289008864288121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37232938611437356971434989 13962351979289008864288121)
    ·
      refine ⟨10471763984466756648216091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13962351979289008864288121 10471763984466756648216091)
      ·
        refine ⟨15707645976700134972324137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10471763984466756648216091 15707645976700134972324137)
        ·
          refine ⟨11780734482525101229243103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15707645976700134972324137 11780734482525101229243103)
          ·
            refine ⟨17671101723787651843864655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11780734482525101229243103 17671101723787651843864655)
            ·
              refine ⟨26506652585681477765796983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17671101723787651843864655 26506652585681477765796983)
              ·
                refine ⟨39759978878522216648695475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26506652585681477765796983 39759978878522216648695475)
                ·
                  refine ⟨59639968317783324973043213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39759978878522216648695475 59639968317783324973043213)
                  ·
                    refine ⟨22364988119168746864891205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59639968317783324973043213 22364988119168746864891205)
                    ·
                      refine ⟨4193435272344140037167101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22364988119168746864891205 4193435272344140037167101)
                      ·
                        rfl

theorem cell23_8166686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_8166686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166686 prefixEnd_8166686 := by exact prefixLift 8166686
  have htrace : WordTrace (prefixWord ++ tailWord_8166686) baseStart_8166686 baseEnd_8166686 := by
    simpa [prefixWord, tailWord_8166686, baseEnd_8166686] using wordTrace_append hprefix tailTrace_8166686
  have hstable : (prefixWord ++ tailWord_8166686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166686).length < 2 ^ (prefixWord ++ tailWord_8166686).sum := by decide
  have hdescent : baseEnd_8166686 < baseStart_8166686 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166696 : List Nat := [2, 1, 5, 1, 2, 1, 1, 5, 1, 4]
def baseStart_8166696 : Nat := 118140960795 + 8166696 * 2 ^ 59
def prefixEnd_8166696 : Nat := 4983230072969 + 3 ^ 40 * 8166696 * 2
def baseEnd_8166696 : Nat := 1397813469050228332680685

theorem tailTrace_8166696 : CollatzResearch.WordTrace tailWord_8166696 prefixEnd_8166696 1397813469050228332680685 := by
  unfold tailWord_8166696
  simp only [CollatzResearch.WordTrace]
  refine ⟨148931936810731313739671971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198575915747641751652895961 148931936810731313739671971)
  ·
    refine ⟨223397905216096970609507957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148931936810731313739671971 223397905216096970609507957)
    ·
      refine ⟨20943553614009090994641371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223397905216096970609507957 20943553614009090994641371)
      ·
        refine ⟨31415330421013636491962057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20943553614009090994641371 31415330421013636491962057)
        ·
          refine ⟨23561497815760227368971543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31415330421013636491962057 23561497815760227368971543)
          ·
            refine ⟨35342246723640341053457315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23561497815760227368971543 35342246723640341053457315)
            ·
              refine ⟨53013370085460511580185973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35342246723640341053457315 53013370085460511580185973)
              ·
                refine ⟨4970003445511922960642435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53013370085460511580185973 4970003445511922960642435)
                ·
                  refine ⟨7455005168267884440963653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4970003445511922960642435 7455005168267884440963653)
                  ·
                    refine ⟨1397813469050228332680685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7455005168267884440963653 1397813469050228332680685)
                    ·
                      rfl

theorem cell23_8166696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_8166696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166696 prefixEnd_8166696 := by exact prefixLift 8166696
  have htrace : WordTrace (prefixWord ++ tailWord_8166696) baseStart_8166696 baseEnd_8166696 := by
    simpa [prefixWord, tailWord_8166696, baseEnd_8166696] using wordTrace_append hprefix tailTrace_8166696
  have hstable : (prefixWord ++ tailWord_8166696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166696).length < 2 ^ (prefixWord ++ tailWord_8166696).sum := by decide
  have hdescent : baseEnd_8166696 < baseStart_8166696 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166709 : List Nat := [1, 3, 3, 1, 2, 4, 1, 2, 6]
def baseStart_8166709 : Nat := 118140960795 + 8166709 * 2 ^ 59
def prefixEnd_8166709 : Nat := 4983230072969 + 3 ^ 40 * 8166709 * 2
def baseEnd_8166709 : Nat := 465938564711021494131055

theorem tailTrace_8166709 : CollatzResearch.WordTrace tailWord_8166709 prefixEnd_8166709 465938564711021494131055 := by
  unfold tailWord_8166709
  simp only [CollatzResearch.WordTrace]
  refine ⟨297864347770415530699567181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198576231846943687133044787 297864347770415530699567181)
  ·
    refine ⟨111699130413905824012337693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297864347770415530699567181 111699130413905824012337693)
    ·
      refine ⟨41887173905214684004626635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111699130413905824012337693 41887173905214684004626635)
      ·
        refine ⟨62830760857822026006939953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41887173905214684004626635 62830760857822026006939953)
        ·
          refine ⟨47123070643366519505204965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62830760857822026006939953 47123070643366519505204965)
          ·
            refine ⟨8835575745631222407225931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47123070643366519505204965 8835575745631222407225931)
            ·
              refine ⟨13253363618446833610838897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8835575745631222407225931 13253363618446833610838897)
              ·
                refine ⟨9940022713835125208129173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13253363618446833610838897 9940022713835125208129173)
                ·
                  refine ⟨465938564711021494131055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9940022713835125208129173 465938564711021494131055)
                  ·
                    rfl

theorem cell23_8166709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 6].length) (baseStart_8166709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166709 prefixEnd_8166709 := by exact prefixLift 8166709
  have htrace : WordTrace (prefixWord ++ tailWord_8166709) baseStart_8166709 baseEnd_8166709 := by
    simpa [prefixWord, tailWord_8166709, baseEnd_8166709] using wordTrace_append hprefix tailTrace_8166709
  have hstable : (prefixWord ++ tailWord_8166709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166709).length < 2 ^ (prefixWord ++ tailWord_8166709).sum := by decide
  have hdescent : baseEnd_8166709 < baseStart_8166709 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166719 : List Nat := [1, 1, 2, 2, 4, 2, 1, 3, 3, 1, 3]
def baseStart_8166719 : Nat := 118140960795 + 8166719 * 2 ^ 59
def prefixEnd_8166719 : Nat := 4983230072969 + 3 ^ 40 * 8166719 * 2
def baseEnd_8166719 : Nat := 4193452217205738408054449

theorem tailTrace_8166719 : CollatzResearch.WordTrace tailWord_8166719 prefixEnd_8166719 4193452217205738408054449 := by
  unfold tailWord_8166719
  simp only [CollatzResearch.WordTrace]
  refine ⟨297864712500379302407431211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198576475000252868271620807 297864712500379302407431211)
  ·
    refine ⟨446797068750568953611146817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297864712500379302407431211 446797068750568953611146817)
    ·
      refine ⟨335097801562926715208360113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446797068750568953611146817 335097801562926715208360113)
      ·
        refine ⟨251323351172195036406270085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335097801562926715208360113 251323351172195036406270085)
        ·
          refine ⟨47123128344786569326175641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251323351172195036406270085 47123128344786569326175641)
          ·
            refine ⟨35342346258589926994631731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47123128344786569326175641 35342346258589926994631731)
            ·
              refine ⟨53013519387884890491947597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35342346258589926994631731 53013519387884890491947597)
              ·
                refine ⟨19880069770456833934480349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53013519387884890491947597 19880069770456833934480349)
                ·
                  refine ⟨7455026163921312725430131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19880069770456833934480349 7455026163921312725430131)
                  ·
                    refine ⟨11182539245881969088145197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7455026163921312725430131 11182539245881969088145197)
                    ·
                      refine ⟨4193452217205738408054449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11182539245881969088145197 4193452217205738408054449)
                      ·
                        rfl

theorem cell23_8166719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3, 1, 3].length) (baseStart_8166719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166719 prefixEnd_8166719 := by exact prefixLift 8166719
  have htrace : WordTrace (prefixWord ++ tailWord_8166719) baseStart_8166719 baseEnd_8166719 := by
    simpa [prefixWord, tailWord_8166719, baseEnd_8166719] using wordTrace_append hprefix tailTrace_8166719
  have hstable : (prefixWord ++ tailWord_8166719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166719).length < 2 ^ (prefixWord ++ tailWord_8166719).sum := by decide
  have hdescent : baseEnd_8166719 < baseStart_8166719 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166793 : List Nat := [1, 2, 1, 1, 8, 1, 1, 2, 1, 1, 4]
def baseStart_8166793 : Nat := 118140960795 + 8166793 * 2 ^ 59
def prefixEnd_8166793 : Nat := 4983230072969 + 3 ^ 40 * 8166793 * 2
def baseEnd_8166793 : Nat := 4193490214774171118529109

theorem tailTrace_8166793 : CollatzResearch.WordTrace tailWord_8166793 prefixEnd_8166793 4193490214774171118529109 := by
  unfold tailWord_8166793
  simp only [CollatzResearch.WordTrace]
  refine ⟨297867411502111213045625033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198578274334740808697083355 297867411502111213045625033)
  ·
    refine ⟨223400558626583409784218775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297867411502111213045625033 223400558626583409784218775)
    ·
      refine ⟨335100837939875114676328163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223400558626583409784218775 335100837939875114676328163)
      ·
        refine ⟨502651256909812672014492245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335100837939875114676328163 502651256909812672014492245)
        ·
          refine ⟨5890444416911867250169831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 502651256909812672014492245 5890444416911867250169831)
          ·
            refine ⟨8835666625367800875254747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5890444416911867250169831 8835666625367800875254747)
            ·
              refine ⟨13253499938051701312882121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8835666625367800875254747 13253499938051701312882121)
              ·
                refine ⟨9940124953538775984661591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13253499938051701312882121 9940124953538775984661591)
                ·
                  refine ⟨14910187430308163976992387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9940124953538775984661591 14910187430308163976992387)
                  ·
                    refine ⟨22365281145462245965488581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14910187430308163976992387 22365281145462245965488581)
                    ·
                      refine ⟨4193490214774171118529109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22365281145462245965488581 4193490214774171118529109)
                      ·
                        rfl

theorem cell23_8166793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 1, 1, 4].length) (baseStart_8166793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166793 prefixEnd_8166793 := by exact prefixLift 8166793
  have htrace : WordTrace (prefixWord ++ tailWord_8166793) baseStart_8166793 baseEnd_8166793 := by
    simpa [prefixWord, tailWord_8166793, baseEnd_8166793] using wordTrace_append hprefix tailTrace_8166793
  have hstable : (prefixWord ++ tailWord_8166793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166793).length < 2 ^ (prefixWord ++ tailWord_8166793).sum := by decide
  have hdescent : baseEnd_8166793 < baseStart_8166793 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166809 : List Nat := [1, 2, 1, 2, 1, 6, 1, 2, 1, 3, 3]
def baseStart_8166809 : Nat := 118140960795 + 8166809 * 2 ^ 59
def prefixEnd_8166809 : Nat := 4983230072969 + 3 ^ 40 * 8166809 * 2
def baseEnd_8166809 : Nat := 4193498430464643055929035

theorem tailTrace_8166809 : CollatzResearch.WordTrace tailWord_8166809 prefixEnd_8166809 4193498430464643055929035 := by
  unfold tailWord_8166809
  simp only [CollatzResearch.WordTrace]
  refine ⟨297867995070053247778207481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198578663380035498518804987 297867995070053247778207481)
  ·
    refine ⟨223400996302539935833655611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297867995070053247778207481 223400996302539935833655611)
    ·
      refine ⟨335101494453809903750483417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223400996302539935833655611 335101494453809903750483417)
      ·
        refine ⟨251326120840357427812862563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335101494453809903750483417 251326120840357427812862563)
        ·
          refine ⟨376989181260536141719293845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251326120840357427812862563 376989181260536141719293845)
          ·
            refine ⟨17671367871587631643091899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 376989181260536141719293845 17671367871587631643091899)
            ·
              refine ⟨26507051807381447464637849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17671367871587631643091899 26507051807381447464637849)
              ·
                refine ⟨19880288855536085598478387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26507051807381447464637849 19880288855536085598478387)
                ·
                  refine ⟨29820433283304128397717581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19880288855536085598478387 29820433283304128397717581)
                  ·
                    refine ⟨11182662481239048149144093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29820433283304128397717581 11182662481239048149144093)
                    ·
                      refine ⟨4193498430464643055929035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11182662481239048149144093 4193498430464643055929035)
                      ·
                        rfl

theorem cell23_8166809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 3, 3].length) (baseStart_8166809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166809 prefixEnd_8166809 := by exact prefixLift 8166809
  have htrace : WordTrace (prefixWord ++ tailWord_8166809) baseStart_8166809 baseEnd_8166809 := by
    simpa [prefixWord, tailWord_8166809, baseEnd_8166809] using wordTrace_append hprefix tailTrace_8166809
  have hstable : (prefixWord ++ tailWord_8166809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166809).length < 2 ^ (prefixWord ++ tailWord_8166809).sum := by decide
  have hdescent : baseEnd_8166809 < baseStart_8166809 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166813 : List Nat := [1, 4, 2, 1, 3, 2, 3, 1, 1, 2, 3]
def baseStart_8166813 : Nat := 118140960795 + 8166813 * 2 ^ 59
def prefixEnd_8166813 : Nat := 4983230072969 + 3 ^ 40 * 8166813 * 2
def baseEnd_8166813 : Nat := 4193500484387261040279017

theorem tailTrace_8166813 : CollatzResearch.WordTrace tailWord_8166813 prefixEnd_8166813 4193500484387261040279017 := by
  unfold tailWord_8166813
  simp only [CollatzResearch.WordTrace]
  refine ⟨297868140962038756461353093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198578760641359170974235395 297868140962038756461353093)
  ·
    refine ⟨55850276430382266836503705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297868140962038756461353093 55850276430382266836503705)
    ·
      refine ⟨41887707322786700127377779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55850276430382266836503705 41887707322786700127377779)
      ·
        refine ⟨62831560984180050191066669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41887707322786700127377779 62831560984180050191066669)
        ·
          refine ⟨23561835369067518821650001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62831560984180050191066669 23561835369067518821650001)
          ·
            refine ⟨17671376526800639116237501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23561835369067518821650001 17671376526800639116237501)
            ·
              refine ⟨6626766197550239668589063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17671376526800639116237501 6626766197550239668589063)
              ·
                refine ⟨9940149296325359502883595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6626766197550239668589063 9940149296325359502883595)
                ·
                  refine ⟨14910223944488039254325393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9940149296325359502883595 14910223944488039254325393)
                  ·
                    refine ⟨11182667958366029440744045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14910223944488039254325393 11182667958366029440744045)
                    ·
                      refine ⟨4193500484387261040279017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11182667958366029440744045 4193500484387261040279017)
                      ·
                        rfl

theorem cell23_8166813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_8166813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166813 prefixEnd_8166813 := by exact prefixLift 8166813
  have htrace : WordTrace (prefixWord ++ tailWord_8166813) baseStart_8166813 baseEnd_8166813 := by
    simpa [prefixWord, tailWord_8166813, baseEnd_8166813] using wordTrace_append hprefix tailTrace_8166813
  have hstable : (prefixWord ++ tailWord_8166813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166813).length < 2 ^ (prefixWord ++ tailWord_8166813).sum := by decide
  have hdescent : baseEnd_8166813 < baseStart_8166813 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166829 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 2, 7]
def baseStart_8166829 : Nat := 118140960795 + 8166829 * 2 ^ 59
def prefixEnd_8166829 : Nat := 4983230072969 + 3 ^ 40 * 8166829 * 2
def baseEnd_8166829 : Nat := 1397836233359244325892981

theorem tailTrace_8166829 : CollatzResearch.WordTrace tailWord_8166829 prefixEnd_8166829 1397836233359244325892981 := by
  unfold tailWord_8166829
  simp only [CollatzResearch.WordTrace]
  refine ⟨297868724529980791193935541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198579149686653860795957027 297868724529980791193935541)
  ·
    refine ⟨27925192924685699174431457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 297868724529980791193935541 27925192924685699174431457)
    ·
      refine ⟨20943894693514274380823593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27925192924685699174431457 20943894693514274380823593)
      ·
        refine ⟨15707921020135705785617695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20943894693514274380823593 15707921020135705785617695)
        ·
          refine ⟨23561881530203558678426543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15707921020135705785617695 23561881530203558678426543)
          ·
            refine ⟨35342822295305338017639815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23561881530203558678426543 35342822295305338017639815)
            ·
              refine ⟨53014233442958007026459723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35342822295305338017639815 53014233442958007026459723)
              ·
                refine ⟨79521350164437010539689585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53014233442958007026459723 79521350164437010539689585)
                ·
                  refine ⟨59641012623327757904767189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79521350164437010539689585 59641012623327757904767189)
                  ·
                    refine ⟨1397836233359244325892981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59641012623327757904767189 1397836233359244325892981)
                    ·
                      rfl

theorem cell23_8166829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_8166829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166829 prefixEnd_8166829 := by exact prefixLift 8166829
  have htrace : WordTrace (prefixWord ++ tailWord_8166829) baseStart_8166829 baseEnd_8166829 := by
    simpa [prefixWord, tailWord_8166829, baseEnd_8166829] using wordTrace_append hprefix tailTrace_8166829
  have hstable : (prefixWord ++ tailWord_8166829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166829).length < 2 ^ (prefixWord ++ tailWord_8166829).sum := by decide
  have hdescent : baseEnd_8166829 < baseStart_8166829 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166870 : List Nat := [5, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2]
def baseStart_8166870 : Nat := 118140960795 + 8166870 * 2 ^ 59
def prefixEnd_8166870 : Nat := 4983230072969 + 3 ^ 40 * 8166870 * 2
def baseEnd_8166870 : Nat := 4193529752784567317266255

theorem tailTrace_8166870 : CollatzResearch.WordTrace tailWord_8166870 prefixEnd_8166870 4193529752784567317266255 := by
  unfold tailWord_8166870
  simp only [CollatzResearch.WordTrace]
  refine ⟨18616888745177015949761129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198580146615221503464118709 18616888745177015949761129)
  ·
    refine ⟨13962666558882761962320847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18616888745177015949761129 13962666558882761962320847)
    ·
      refine ⟨20943999838324142943481271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13962666558882761962320847 20943999838324142943481271)
      ·
        refine ⟨31415999757486214415221907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20943999838324142943481271 31415999757486214415221907)
        ·
          refine ⟨47123999636229321622832861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31415999757486214415221907 47123999636229321622832861)
          ·
            refine ⟨17671499863585995608562323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47123999636229321622832861 17671499863585995608562323)
            ·
              refine ⟨26507249795378993412843485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17671499863585995608562323 26507249795378993412843485)
              ·
                refine ⟨9940218673267122529816307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26507249795378993412843485 9940218673267122529816307)
                ·
                  refine ⟨14910328009900683794724461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9940218673267122529816307 14910328009900683794724461)
                  ·
                    refine ⟨5591373003712756423021673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14910328009900683794724461 5591373003712756423021673)
                    ·
                      refine ⟨4193529752784567317266255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5591373003712756423021673 4193529752784567317266255)
                      ·
                        rfl

theorem cell23_8166870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_8166870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166870 prefixEnd_8166870 := by exact prefixLift 8166870
  have htrace : WordTrace (prefixWord ++ tailWord_8166870) baseStart_8166870 baseEnd_8166870 := by
    simpa [prefixWord, tailWord_8166870, baseEnd_8166870] using wordTrace_append hprefix tailTrace_8166870
  have hstable : (prefixWord ++ tailWord_8166870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166870).length < 2 ^ (prefixWord ++ tailWord_8166870).sum := by decide
  have hdescent : baseEnd_8166870 < baseStart_8166870 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166883 : List Nat := [1, 1, 1, 6, 2, 2, 1, 1, 4, 2, 2]
def baseStart_8166883 : Nat := 118140960795 + 8166883 * 2 ^ 59
def prefixEnd_8166883 : Nat := 4983230072969 + 3 ^ 40 * 8166883 * 2
def baseEnd_8166883 : Nat := 4193536428033075766403695

theorem tailTrace_8166883 : CollatzResearch.WordTrace tailWord_8166883 prefixEnd_8166883 4193536428033075766403695 := by
  unfold tailWord_8166883
  simp only [CollatzResearch.WordTrace]
  refine ⟨297870694071785158416401303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198580462714523438944267535 297870694071785158416401303)
  ·
    refine ⟨446806041107677737624601955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297870694071785158416401303 446806041107677737624601955)
    ·
      refine ⟨670209061661516606436902933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446806041107677737624601955 670209061661516606436902933)
      ·
        refine ⟨31416049765383590926729825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 670209061661516606436902933 31416049765383590926729825)
        ·
          refine ⟨23562037324037693195047369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31416049765383590926729825 23562037324037693195047369)
          ·
            refine ⟨17671527993028269896285527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23562037324037693195047369 17671527993028269896285527)
            ·
              refine ⟨26507291989542404844428291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17671527993028269896285527 26507291989542404844428291)
              ·
                refine ⟨39760937984313607266642437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26507291989542404844428291 39760937984313607266642437)
                ·
                  refine ⟨7455175872058801362495457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39760937984313607266642437 7455175872058801362495457)
                  ·
                    refine ⟨5591381904044101021871593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7455175872058801362495457 5591381904044101021871593)
                    ·
                      refine ⟨4193536428033075766403695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5591381904044101021871593 4193536428033075766403695)
                      ·
                        rfl

theorem cell23_8166883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_8166883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166883 prefixEnd_8166883 := by exact prefixLift 8166883
  have htrace : WordTrace (prefixWord ++ tailWord_8166883) baseStart_8166883 baseEnd_8166883 := by
    simpa [prefixWord, tailWord_8166883, baseEnd_8166883] using wordTrace_append hprefix tailTrace_8166883
  have hstable : (prefixWord ++ tailWord_8166883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166883).length < 2 ^ (prefixWord ++ tailWord_8166883).sum := by decide
  have hdescent : baseEnd_8166883 < baseStart_8166883 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166919 : List Nat := [1, 1, 4, 3, 2, 1, 2, 1, 1, 7]
def baseStart_8166919 : Nat := 118140960795 + 8166919 * 2 ^ 59
def prefixEnd_8166919 : Nat := 4983230072969 + 3 ^ 40 * 8166919 * 2
def baseEnd_8166919 : Nat := 1397851637778879208517843

theorem tailTrace_8166919 : CollatzResearch.WordTrace tailWord_8166919 prefixEnd_8166919 1397851637778879208517843 := by
  unfold tailWord_8166919
  simp only [CollatzResearch.WordTrace]
  refine ⟨297872007099654736564711811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198581338066436491043141207 297872007099654736564711811)
  ·
    refine ⟨446808010649482104847067717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297872007099654736564711811 446808010649482104847067717)
    ·
      refine ⟨83776501996777894658825197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 446808010649482104847067717 83776501996777894658825197)
      ·
        refine ⟨31416188248791710497059449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83776501996777894658825197 31416188248791710497059449)
        ·
          refine ⟨23562141186593782872794587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31416188248791710497059449 23562141186593782872794587)
          ·
            refine ⟨35343211779890674309191881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23562141186593782872794587 35343211779890674309191881)
            ·
              refine ⟨26507408834918005731893911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35343211779890674309191881 26507408834918005731893911)
              ·
                refine ⟨39761113252377008597840867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26507408834918005731893911 39761113252377008597840867)
                ·
                  refine ⟨59641669878565512896761301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39761113252377008597840867 59641669878565512896761301)
                  ·
                    refine ⟨1397851637778879208517843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59641669878565512896761301 1397851637778879208517843)
                    ·
                      rfl

theorem cell23_8166919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_8166919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166919 prefixEnd_8166919 := by exact prefixLift 8166919
  have htrace : WordTrace (prefixWord ++ tailWord_8166919) baseStart_8166919 baseEnd_8166919 := by
    simpa [prefixWord, tailWord_8166919, baseEnd_8166919] using wordTrace_append hprefix tailTrace_8166919
  have hstable : (prefixWord ++ tailWord_8166919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166919).length < 2 ^ (prefixWord ++ tailWord_8166919).sum := by decide
  have hdescent : baseEnd_8166919 < baseStart_8166919 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166923 : List Nat := [1, 1, 1, 1, 8, 2, 1, 3, 5]
def baseStart_8166923 : Nat := 118140960795 + 8166923 * 2 ^ 59
def prefixEnd_8166923 : Nat := 4983230072969 + 3 ^ 40 * 8166923 * 2
def baseEnd_8166923 : Nat := 465950774139917289989279

theorem tailTrace_8166923 : CollatzResearch.WordTrace tailWord_8166923 prefixEnd_8166923 465950774139917289989279 := by
  unfold tailWord_8166923
  simp only [CollatzResearch.WordTrace]
  refine ⟨297872152991640245247857423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198581435327760163498571615 297872152991640245247857423)
  ·
    refine ⟨446808229487460367871786135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297872152991640245247857423 446808229487460367871786135)
    ·
      refine ⟨670212344231190551807679203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446808229487460367871786135 670212344231190551807679203)
      ·
        refine ⟨1005318516346785827711518805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670212344231190551807679203 1005318516346785827711518805)
        ·
          refine ⟨11781076363438896418494361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 1005318516346785827711518805 11781076363438896418494361)
          ·
            refine ⟨8835807272579172313870771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11781076363438896418494361 8835807272579172313870771)
            ·
              refine ⟨13253710908868758470806157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8835807272579172313870771 13253710908868758470806157)
              ·
                refine ⟨4970141590825784426552309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13253710908868758470806157 4970141590825784426552309)
                ·
                  refine ⟨465950774139917289989279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4970141590825784426552309 465950774139917289989279)
                  ·
                    rfl

theorem cell23_8166923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3, 5].length) (baseStart_8166923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166923 prefixEnd_8166923 := by exact prefixLift 8166923
  have htrace : WordTrace (prefixWord ++ tailWord_8166923) baseStart_8166923 baseEnd_8166923 := by
    simpa [prefixWord, tailWord_8166923, baseEnd_8166923] using wordTrace_append hprefix tailTrace_8166923
  have hstable : (prefixWord ++ tailWord_8166923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166923).length < 2 ^ (prefixWord ++ tailWord_8166923).sum := by decide
  have hdescent : baseEnd_8166923 < baseStart_8166923 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166936 : List Nat := [2, 1, 2, 3, 4, 1, 1, 2, 2, 5]
def baseStart_8166936 : Nat := 118140960795 + 8166936 * 2 ^ 59
def prefixEnd_8166936 : Nat := 4983230072969 + 3 ^ 40 * 8166936 * 2
def baseEnd_8166936 : Nat := 1397854547502588019680317

theorem tailTrace_8166936 : CollatzResearch.WordTrace tailWord_8166936 prefixEnd_8166936 1397854547502588019680317 := by
  unfold tailWord_8166936
  simp only [CollatzResearch.WordTrace]
  refine ⟨148936313570296574234040331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198581751427062098978720441 148936313570296574234040331)
  ·
    refine ⟨223404470355444861351060497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148936313570296574234040331 223404470355444861351060497)
    ·
      refine ⟨167553352766583646013295373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223404470355444861351060497 167553352766583646013295373)
      ·
        refine ⟨62832507287468867254985765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167553352766583646013295373 62832507287468867254985765)
        ·
          refine ⟨11781095116400412610309831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62832507287468867254985765 11781095116400412610309831)
          ·
            refine ⟨17671642674600618915464747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11781095116400412610309831 17671642674600618915464747)
            ·
              refine ⟨26507464011900928373197121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17671642674600618915464747 26507464011900928373197121)
              ·
                refine ⟨19880598008925696279897841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26507464011900928373197121 19880598008925696279897841)
                ·
                  refine ⟨14910448506694272209923381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19880598008925696279897841 14910448506694272209923381)
                  ·
                    refine ⟨1397854547502588019680317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14910448506694272209923381 1397854547502588019680317)
                    ·
                      rfl

theorem cell23_8166936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 2, 5].length) (baseStart_8166936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166936 prefixEnd_8166936 := by exact prefixLift 8166936
  have htrace : WordTrace (prefixWord ++ tailWord_8166936) baseStart_8166936 baseEnd_8166936 := by
    simpa [prefixWord, tailWord_8166936, baseEnd_8166936] using wordTrace_append hprefix tailTrace_8166936
  have hstable : (prefixWord ++ tailWord_8166936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166936).length < 2 ^ (prefixWord ++ tailWord_8166936).sum := by decide
  have hdescent : baseEnd_8166936 < baseStart_8166936 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166973 : List Nat := [1, 4, 1, 3, 3, 1, 2, 1, 2, 1, 4]
def baseStart_8166973 : Nat := 118140960795 + 8166973 * 2 ^ 59
def prefixEnd_8166973 : Nat := 4983230072969 + 3 ^ 40 * 8166973 * 2
def baseEnd_8166973 : Nat := 4193582641291980414278281

theorem tailTrace_8166973 : CollatzResearch.WordTrace tailWord_8166973 prefixEnd_8166973 4193582641291980414278281 := by
  unfold tailWord_8166973
  simp only [CollatzResearch.WordTrace]
  refine ⟨297873976641459103787177573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198582651094306069191451715 297873976641459103787177573)
  ·
    refine ⟨55851370620273581960095795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297873976641459103787177573 55851370620273581960095795)
    ·
      refine ⟨83777055930410372940143693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55851370620273581960095795 83777055930410372940143693)
      ·
        refine ⟨31416395973903889852553885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83777055930410372940143693 31416395973903889852553885)
        ·
          refine ⟨11781148490213958694707707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31416395973903889852553885 11781148490213958694707707)
          ·
            refine ⟨17671722735320938042061561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11781148490213958694707707 17671722735320938042061561)
            ·
              refine ⟨13253792051490703531546171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17671722735320938042061561 13253792051490703531546171)
              ·
                refine ⟨19880688077236055297319257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13253792051490703531546171 19880688077236055297319257)
                ·
                  refine ⟨14910516057927041472989443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19880688077236055297319257 14910516057927041472989443)
                  ·
                    refine ⟨22365774086890562209484165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14910516057927041472989443 22365774086890562209484165)
                    ·
                      refine ⟨4193582641291980414278281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22365774086890562209484165 4193582641291980414278281)
                      ·
                        rfl

theorem cell23_8166973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_8166973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166973 prefixEnd_8166973 := by exact prefixLift 8166973
  have htrace : WordTrace (prefixWord ++ tailWord_8166973) baseStart_8166973 baseEnd_8166973 := by
    simpa [prefixWord, tailWord_8166973, baseEnd_8166973] using wordTrace_append hprefix tailTrace_8166973
  have hstable : (prefixWord ++ tailWord_8166973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166973).length < 2 ^ (prefixWord ++ tailWord_8166973).sum := by decide
  have hdescent : baseEnd_8166973 < baseStart_8166973 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8166996 : List Nat := [2, 4, 1, 1, 1, 2, 4, 2, 6]
def baseStart_8166996 : Nat := 118140960795 + 8166996 * 2 ^ 59
def prefixEnd_8166996 : Nat := 4983230072969 + 3 ^ 40 * 8166996 * 2
def baseEnd_8166996 : Nat := 465954939038559313810075

theorem tailTrace_8166996 : CollatzResearch.WordTrace tailWord_8166996 prefixEnd_8166996 465954939038559313810075 := by
  unfold tailWord_8166996
  simp only [CollatzResearch.WordTrace]
  refine ⟨148937407760187889357632421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198583210346917185810176561 148937407760187889357632421)
  ·
    refine ⟨27925763955035229254556079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148937407760187889357632421 27925763955035229254556079)
    ·
      refine ⟨41888645932552843881834119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27925763955035229254556079 41888645932552843881834119)
      ·
        refine ⟨62832968898829265822751179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41888645932552843881834119 62832968898829265822751179)
        ·
          refine ⟨94249453348243898734126769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62832968898829265822751179 94249453348243898734126769)
          ·
            refine ⟨70687090011182924050595077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94249453348243898734126769 70687090011182924050595077)
            ·
              refine ⟨13253829377096798259486577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70687090011182924050595077 13253829377096798259486577)
              ·
                refine ⟨9940372032822598694614933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13253829377096798259486577 9940372032822598694614933)
                ·
                  refine ⟨465954939038559313810075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9940372032822598694614933 465954939038559313810075)
                  ·
                    rfl

theorem cell23_8166996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_8166996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8166996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8166996 prefixEnd_8166996 := by exact prefixLift 8166996
  have htrace : WordTrace (prefixWord ++ tailWord_8166996) baseStart_8166996 baseEnd_8166996 := by
    simpa [prefixWord, tailWord_8166996, baseEnd_8166996] using wordTrace_append hprefix tailTrace_8166996
  have hstable : (prefixWord ++ tailWord_8166996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8166996).length < 2 ^ (prefixWord ++ tailWord_8166996).sum := by decide
  have hdescent : baseEnd_8166996 < baseStart_8166996 := by decide
  rcases family_descends (prefixWord ++ tailWord_8166996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167009 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 5, 5]
def baseStart_8167009 : Nat := 118140960795 + 8167009 * 2 ^ 59
def prefixEnd_8167009 : Nat := 4983230072969 + 3 ^ 40 * 8167009 * 2
def baseEnd_8167009 : Nat := 1397867042198514091142705

theorem tailTrace_8167009 : CollatzResearch.WordTrace tailWord_8167009 prefixEnd_8167009 1397867042198514091142705 := by
  unfold tailWord_8167009
  simp only [CollatzResearch.WordTrace]
  refine ⟨297875289669328681935488081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198583526446219121290325387 297875289669328681935488081)
  ·
    refine ⟨223406467251996511451616061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297875289669328681935488081 223406467251996511451616061)
    ·
      refine ⟨83777425219498691794356023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223406467251996511451616061 83777425219498691794356023)
      ·
        refine ⟨125666137829248037691534035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83777425219498691794356023 125666137829248037691534035)
        ·
          refine ⟨188499206743872056537301053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125666137829248037691534035 188499206743872056537301053)
          ·
            refine ⟨70687202528952021201487895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188499206743872056537301053 70687202528952021201487895)
            ·
              refine ⟨106030803793428031802231843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70687202528952021201487895 106030803793428031802231843)
              ·
                refine ⟨159046205690142047703347765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106030803793428031802231843 159046205690142047703347765)
                ·
                  refine ⟨14910581783450816972188853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159046205690142047703347765 14910581783450816972188853)
                  ·
                    refine ⟨1397867042198514091142705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14910581783450816972188853 1397867042198514091142705)
                    ·
                      rfl

theorem cell23_8167009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_8167009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167009 prefixEnd_8167009 := by exact prefixLift 8167009
  have htrace : WordTrace (prefixWord ++ tailWord_8167009) baseStart_8167009 baseEnd_8167009 := by
    simpa [prefixWord, tailWord_8167009, baseEnd_8167009] using wordTrace_append hprefix tailTrace_8167009
  have hstable : (prefixWord ++ tailWord_8167009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167009).length < 2 ^ (prefixWord ++ tailWord_8167009).sum := by decide
  have hdescent : baseEnd_8167009 < baseStart_8167009 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167026 : List Nat := [3, 2, 1, 2, 3, 1, 2, 1, 3, 5]
def baseStart_8167026 : Nat := 118140960795 + 8167026 * 2 ^ 59
def prefixEnd_8167026 : Nat := 4983230072969 + 3 ^ 40 * 8167026 * 2
def baseEnd_8167026 : Nat := 1397869951922222902305179

theorem tailTrace_8167026 : CollatzResearch.WordTrace tailWord_8167026 prefixEnd_8167026 1397869951922222902305179 := by
  unfold tailWord_8167026
  simp only [CollatzResearch.WordTrace]
  refine ⟨74468977427566773459714233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198583939806844729225904621 74468977427566773459714233)
  ·
    refine ⟨55851733070675080094785675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74468977427566773459714233 55851733070675080094785675)
    ·
      refine ⟨83777599606012620142178513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55851733070675080094785675 83777599606012620142178513)
      ·
        refine ⟨62833199704509465106633885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83777599606012620142178513 62833199704509465106633885)
        ·
          refine ⟨23562449889191049414987707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62833199704509465106633885 23562449889191049414987707)
          ·
            refine ⟨35343674833786574122481561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23562449889191049414987707 35343674833786574122481561)
            ·
              refine ⟨26507756125339930591861171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35343674833786574122481561 26507756125339930591861171)
              ·
                refine ⟨39761634188009895887791757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26507756125339930591861171 39761634188009895887791757)
                ·
                  refine ⟨14910612820503710957921909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39761634188009895887791757 14910612820503710957921909)
                  ·
                    refine ⟨1397869951922222902305179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14910612820503710957921909 1397869951922222902305179)
                    ·
                      rfl

theorem cell23_8167026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_8167026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167026 prefixEnd_8167026 := by exact prefixLift 8167026
  have htrace : WordTrace (prefixWord ++ tailWord_8167026) baseStart_8167026 baseEnd_8167026 := by
    simpa [prefixWord, tailWord_8167026, baseEnd_8167026] using wordTrace_append hprefix tailTrace_8167026
  have hstable : (prefixWord ++ tailWord_8167026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167026).length < 2 ^ (prefixWord ++ tailWord_8167026).sum := by decide
  have hdescent : baseEnd_8167026 < baseStart_8167026 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167040 : List Nat := [2, 1, 1, 2, 1, 4, 4, 3, 1, 1, 3]
def baseStart_8167040 : Nat := 118140960795 + 8167040 * 2 ^ 59
def prefixEnd_8167040 : Nat := 4983230072969 + 3 ^ 40 * 8167040 * 2
def baseEnd_8167040 : Nat := 4193617044495831652140473

theorem tailTrace_8167040 : CollatzResearch.WordTrace tailWord_8167040 prefixEnd_8167040 4193617044495831652140473 := by
  unfold tailWord_8167040
  simp only [CollatzResearch.WordTrace]
  refine ⟨148938210166108187114933287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198584280221477582819911049 148938210166108187114933287)
  ·
    refine ⟨223407315249162280672399931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148938210166108187114933287 223407315249162280672399931)
    ·
      refine ⟨335110972873743421008599897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223407315249162280672399931 335110972873743421008599897)
      ·
        refine ⟨251333229655307565756449923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335110972873743421008599897 251333229655307565756449923)
        ·
          refine ⟨376999844482961348634674885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251333229655307565756449923 376999844482961348634674885)
          ·
            refine ⟨70687470840555252869001541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 376999844482961348634674885 70687470840555252869001541)
            ·
              refine ⟨13253900782604109912937789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70687470840555252869001541 13253900782604109912937789)
              ·
                refine ⟨4970212793476541217351671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13253900782604109912937789 4970212793476541217351671)
                ·
                  refine ⟨7455319190214811826027507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4970212793476541217351671 7455319190214811826027507)
                  ·
                    refine ⟨11182978785322217739041261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7455319190214811826027507 11182978785322217739041261)
                    ·
                      refine ⟨4193617044495831652140473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11182978785322217739041261 4193617044495831652140473)
                      ·
                        rfl

theorem cell23_8167040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3, 1, 1, 3].length) (baseStart_8167040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167040 prefixEnd_8167040 := by exact prefixLift 8167040
  have htrace : WordTrace (prefixWord ++ tailWord_8167040) baseStart_8167040 baseEnd_8167040 := by
    simpa [prefixWord, tailWord_8167040, baseEnd_8167040] using wordTrace_append hprefix tailTrace_8167040
  have hstable : (prefixWord ++ tailWord_8167040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167040).length < 2 ^ (prefixWord ++ tailWord_8167040).sum := by decide
  have hdescent : baseEnd_8167040 < baseStart_8167040 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167069 : List Nat := [1, 4, 2, 1, 1, 1, 1, 12]
def baseStart_8167069 : Nat := 118140960795 + 8167069 * 2 ^ 59
def prefixEnd_8167069 : Nat := 4983230072969 + 3 ^ 40 * 8167069 * 2
def baseEnd_8167069 : Nat := 155319701312400445876957

theorem tailTrace_8167069 : CollatzResearch.WordTrace tailWord_8167069 prefixEnd_8167069 155319701312400445876957 := by
  unfold tailWord_8167069
  simp only [CollatzResearch.WordTrace]
  refine ⟨297877478049111312182672261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198584985366074208121781507 297877478049111312182672261)
  ·
    refine ⟨55852027134208371034251049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297877478049111312182672261 55852027134208371034251049)
    ·
      refine ⟨41889020350656278275688287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55852027134208371034251049 41889020350656278275688287)
      ·
        refine ⟨62833530525984417413532431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41889020350656278275688287 62833530525984417413532431)
        ·
          refine ⟨94250295788976626120298647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62833530525984417413532431 94250295788976626120298647)
          ·
            refine ⟨141375443683464939180447971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94250295788976626120298647 141375443683464939180447971)
            ·
              refine ⟨212063165525197408770671957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141375443683464939180447971 212063165525197408770671957)
              ·
                refine ⟨155319701312400445876957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 212063165525197408770671957 155319701312400445876957)
                ·
                  rfl

theorem cell23_8167069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 12].length) (baseStart_8167069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167069 prefixEnd_8167069 := by exact prefixLift 8167069
  have htrace : WordTrace (prefixWord ++ tailWord_8167069) baseStart_8167069 baseEnd_8167069 := by
    simpa [prefixWord, tailWord_8167069, baseEnd_8167069] using wordTrace_append hprefix tailTrace_8167069
  have hstable : (prefixWord ++ tailWord_8167069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167069).length < 2 ^ (prefixWord ++ tailWord_8167069).sum := by decide
  have hdescent : baseEnd_8167069 < baseStart_8167069 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167073 : List Nat := [1, 2, 3, 3, 2, 3, 1, 1, 1, 6]
def baseStart_8167073 : Nat := 118140960795 + 8167073 * 2 ^ 59
def prefixEnd_8167073 : Nat := 4983230072969 + 3 ^ 40 * 8167073 * 2
def baseEnd_8167073 : Nat := 1397877996452476674342607

theorem tailTrace_8167073 : CollatzResearch.WordTrace tailWord_8167073 prefixEnd_8167073 1397877996452476674342607 := by
  unfold tailWord_8167073
  simp only [CollatzResearch.WordTrace]
  refine ⟨297877623941096820865817873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198585082627397880577211915 297877623941096820865817873)
  ·
    refine ⟨223408217955822615649363405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297877623941096820865817873 223408217955822615649363405)
    ·
      refine ⟨83778081733433480868511277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223408217955822615649363405 83778081733433480868511277)
      ·
        refine ⟨31416780650037555325691729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83778081733433480868511277 31416780650037555325691729)
        ·
          refine ⟨23562585487528166494268797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31416780650037555325691729 23562585487528166494268797)
          ·
            refine ⟨8835969557823062435350799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23562585487528166494268797 8835969557823062435350799)
            ·
              refine ⟨13253954336734593653026199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8835969557823062435350799 13253954336734593653026199)
              ·
                refine ⟨19880931505101890479539299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13253954336734593653026199 19880931505101890479539299)
                ·
                  refine ⟨29821397257652835719308949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19880931505101890479539299 29821397257652835719308949)
                  ·
                    refine ⟨1397877996452476674342607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29821397257652835719308949 1397877996452476674342607)
                    ·
                      rfl

theorem cell23_8167073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_8167073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167073 prefixEnd_8167073 := by exact prefixLift 8167073
  have htrace : WordTrace (prefixWord ++ tailWord_8167073) baseStart_8167073 baseEnd_8167073 := by
    simpa [prefixWord, tailWord_8167073, baseEnd_8167073] using wordTrace_append hprefix tailTrace_8167073
  have hstable : (prefixWord ++ tailWord_8167073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167073).length < 2 ^ (prefixWord ++ tailWord_8167073).sum := by decide
  have hdescent : baseEnd_8167073 < baseStart_8167073 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167076 : List Nat := [2, 3, 1, 2, 2, 3, 1, 1, 1, 1, 6]
def baseStart_8167076 : Nat := 118140960795 + 8167076 * 2 ^ 59
def prefixEnd_8167076 : Nat := 4983230072969 + 3 ^ 40 * 8167076 * 2
def baseEnd_8167076 : Nat := 4193635529799393511290307

theorem tailTrace_8167076 : CollatzResearch.WordTrace tailWord_8167076 prefixEnd_8167076 4193635529799393511290307 := by
  unfold tailWord_8167076
  simp only [CollatzResearch.WordTrace]
  refine ⟨148938866680042976189088541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198585155573390634918784721 148938866680042976189088541)
  ·
    refine ⟨55852075005016116070908203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148938866680042976189088541 55852075005016116070908203)
    ·
      refine ⟨83778112507524174106362305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55852075005016116070908203 83778112507524174106362305)
      ·
        refine ⟨62833584380643130579771729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83778112507524174106362305 62833584380643130579771729)
        ·
          refine ⟨47125188285482347934828797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62833584380643130579771729 47125188285482347934828797)
          ·
            refine ⟨17671945607055880475560799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47125188285482347934828797 17671945607055880475560799)
            ·
              refine ⟨26507918410583820713341199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17671945607055880475560799 26507918410583820713341199)
              ·
                refine ⟨39761877615875731070011799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26507918410583820713341199 39761877615875731070011799)
                ·
                  refine ⟨59642816423813596605017699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39761877615875731070011799 59642816423813596605017699)
                  ·
                    refine ⟨89464224635720394907526549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59642816423813596605017699 89464224635720394907526549)
                    ·
                      refine ⟨4193635529799393511290307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89464224635720394907526549 4193635529799393511290307)
                      ·
                        rfl

theorem cell23_8167076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_8167076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167076 prefixEnd_8167076 := by exact prefixLift 8167076
  have htrace : WordTrace (prefixWord ++ tailWord_8167076) baseStart_8167076 baseEnd_8167076 := by
    simpa [prefixWord, tailWord_8167076, baseEnd_8167076] using wordTrace_append hprefix tailTrace_8167076
  have hstable : (prefixWord ++ tailWord_8167076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167076).length < 2 ^ (prefixWord ++ tailWord_8167076).sum := by decide
  have hdescent : baseEnd_8167076 < baseStart_8167076 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167096 : List Nat := [2, 1, 2, 1, 2, 1, 1, 6, 1, 3, 3]
def baseStart_8167096 : Nat := 118140960795 + 8167096 * 2 ^ 59
def prefixEnd_8167096 : Nat := 4983230072969 + 3 ^ 40 * 8167096 * 2
def baseEnd_8167096 : Nat := 4193645799412483433040215

theorem tailTrace_8167096 : CollatzResearch.WordTrace tailWord_8167096 prefixEnd_8167096 4193645799412483433040215 := by
  unfold tailWord_8167096
  simp only [CollatzResearch.WordTrace]
  refine ⟨148939231410006747896952571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198585641880008997195936761 148939231410006747896952571)
  ·
    refine ⟨223408847115010121845428857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148939231410006747896952571 223408847115010121845428857)
    ·
      refine ⟨167556635336257591384071643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223408847115010121845428857 167556635336257591384071643)
      ·
        refine ⟨251334953004386387076107465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167556635336257591384071643 251334953004386387076107465)
        ·
          refine ⟨188501214753289790307080599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251334953004386387076107465 188501214753289790307080599)
          ·
            refine ⟨282751822129934685460620899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188501214753289790307080599 282751822129934685460620899)
            ·
              refine ⟨424127733194902028190931349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282751822129934685460620899 424127733194902028190931349)
              ·
                refine ⟨19880987493511032571449907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 424127733194902028190931349 19880987493511032571449907)
                ·
                  refine ⟨29821481240266548857174861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19880987493511032571449907 29821481240266548857174861)
                  ·
                    refine ⟨11183055465099955821440573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29821481240266548857174861 11183055465099955821440573)
                    ·
                      refine ⟨4193645799412483433040215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11183055465099955821440573 4193645799412483433040215)
                      ·
                        rfl

theorem cell23_8167096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 1, 3, 3].length) (baseStart_8167096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167096 prefixEnd_8167096 := by exact prefixLift 8167096
  have htrace : WordTrace (prefixWord ++ tailWord_8167096) baseStart_8167096 baseEnd_8167096 := by
    simpa [prefixWord, tailWord_8167096, baseEnd_8167096] using wordTrace_append hprefix tailTrace_8167096
  have hstable : (prefixWord ++ tailWord_8167096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167096).length < 2 ^ (prefixWord ++ tailWord_8167096).sum := by decide
  have hdescent : baseEnd_8167096 < baseStart_8167096 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167097 : List Nat := [1, 2, 1, 4, 1, 1, 5, 3, 1, 2, 2]
def baseStart_8167097 : Nat := 118140960795 + 8167097 * 2 ^ 59
def prefixEnd_8167097 : Nat := 4983230072969 + 3 ^ 40 * 8167097 * 2
def baseEnd_8167097 : Nat := 4193646312893137929127711

theorem tailTrace_8167097 : CollatzResearch.WordTrace tailWord_8167097 prefixEnd_8167097 4193646312893137929127711 := by
  unfold tailWord_8167097
  simp only [CollatzResearch.WordTrace]
  refine ⟨297878499293009872964691545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198585666195339915309794363 297878499293009872964691545)
  ·
    refine ⟨223408874469757404723518659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297878499293009872964691545 223408874469757404723518659)
    ·
      refine ⟨335113311704636107085277989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223408874469757404723518659 335113311704636107085277989)
      ·
        refine ⟨62833745944619270078489623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 335113311704636107085277989 62833745944619270078489623)
        ·
          refine ⟨94250618916928905117734435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62833745944619270078489623 94250618916928905117734435)
          ·
            refine ⟨141375928375393357676601653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94250618916928905117734435 141375928375393357676601653)
            ·
              refine ⟨13253993285193127282181405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141375928375393357676601653 13253993285193127282181405)
              ·
                refine ⟨4970247481947422730818027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13253993285193127282181405 4970247481947422730818027)
                ·
                  refine ⟨7455371222921134096227041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4970247481947422730818027 7455371222921134096227041)
                  ·
                    refine ⟨5591528417190850572170281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7455371222921134096227041 5591528417190850572170281)
                    ·
                      refine ⟨4193646312893137929127711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5591528417190850572170281 4193646312893137929127711)
                      ·
                        rfl

theorem cell23_8167097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_8167097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167097 prefixEnd_8167097 := by exact prefixLift 8167097
  have htrace : WordTrace (prefixWord ++ tailWord_8167097) baseStart_8167097 baseEnd_8167097 := by
    simpa [prefixWord, tailWord_8167097, baseEnd_8167097] using wordTrace_append hprefix tailTrace_8167097
  have hstable : (prefixWord ++ tailWord_8167097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167097).length < 2 ^ (prefixWord ++ tailWord_8167097).sum := by decide
  have hdescent : baseEnd_8167097 < baseStart_8167097 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167110 : List Nat := [6, 1, 2, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_8167110 : Nat := 118140960795 + 8167110 * 2 ^ 59
def prefixEnd_8167110 : Nat := 4983230072969 + 3 ^ 40 * 8167110 * 2
def baseEnd_8167110 : Nat := 4193652988141646378265151

theorem tailTrace_8167110 : CollatzResearch.WordTrace tailWord_8167110 prefixEnd_8167110 4193652988141646378265151 := by
  unfold tailWord_8167110
  simp only [CollatzResearch.WordTrace]
  refine ⟨9308717920061336755778587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 198585982294641850789943189 9308717920061336755778587)
  ·
    refine ⟨13963076880092005133667881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9308717920061336755778587 13963076880092005133667881)
    ·
      refine ⟨10472307660069003850250911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13963076880092005133667881 10472307660069003850250911)
      ·
        refine ⟨15708461490103505775376367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10472307660069003850250911 15708461490103505775376367)
        ·
          refine ⟨23562692235155258663064551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15708461490103505775376367 23562692235155258663064551)
          ·
            refine ⟨35344038352732887994596827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23562692235155258663064551 35344038352732887994596827)
            ·
              refine ⟨53016057529099331991895241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35344038352732887994596827 53016057529099331991895241)
              ·
                refine ⟨39762043146824498993921431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53016057529099331991895241 39762043146824498993921431)
                ·
                  refine ⟨59643064720236748490882147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39762043146824498993921431 59643064720236748490882147)
                  ·
                    refine ⟨89464597080355122736323221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59643064720236748490882147 89464597080355122736323221)
                    ·
                      refine ⟨4193652988141646378265151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89464597080355122736323221 4193652988141646378265151)
                      ·
                        rfl

theorem cell23_8167110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_8167110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167110 prefixEnd_8167110 := by exact prefixLift 8167110
  have htrace : WordTrace (prefixWord ++ tailWord_8167110) baseStart_8167110 baseEnd_8167110 := by
    simpa [prefixWord, tailWord_8167110, baseEnd_8167110] using wordTrace_append hprefix tailTrace_8167110
  have hstable : (prefixWord ++ tailWord_8167110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167110).length < 2 ^ (prefixWord ++ tailWord_8167110).sum := by decide
  have hdescent : baseEnd_8167110 < baseStart_8167110 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167114 : List Nat := [3, 1, 2, 1, 6, 1, 1, 1, 3, 2, 2]
def baseStart_8167114 : Nat := 118140960795 + 8167114 * 2 ^ 59
def prefixEnd_8167114 : Nat := 4983230072969 + 3 ^ 40 * 8167114 * 2
def baseEnd_8167114 : Nat := 4193655042064264362615133

theorem tailTrace_8167114 : CollatzResearch.WordTrace tailWord_8167114 prefixEnd_8167114 4193655042064264362615133 := by
  unfold tailWord_8167114
  simp only [CollatzResearch.WordTrace]
  refine ⟨74469779833487071217015099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198586079555965523245373597 74469779833487071217015099)
  ·
    refine ⟨111704669750230606825522649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74469779833487071217015099 111704669750230606825522649)
    ·
      refine ⟨83778502312672955119141987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111704669750230606825522649 83778502312672955119141987)
      ·
        refine ⟨125667753469009432678712981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83778502312672955119141987 125667753469009432678712981)
        ·
          refine ⟨5890675943859817156814671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 125667753469009432678712981 5890675943859817156814671)
          ·
            refine ⟨8836013915789725735222007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5890675943859817156814671 8836013915789725735222007)
            ·
              refine ⟨13254020873684588602833011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8836013915789725735222007 13254020873684588602833011)
              ·
                refine ⟨19881031310526882904249517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13254020873684588602833011 19881031310526882904249517)
                ·
                  refine ⟨7455386741447581089093569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19881031310526882904249517 7455386741447581089093569)
                  ·
                    refine ⟨5591540056085685816820177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7455386741447581089093569 5591540056085685816820177)
                    ·
                      refine ⟨4193655042064264362615133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5591540056085685816820177 4193655042064264362615133)
                      ·
                        rfl

theorem cell23_8167114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 3, 2, 2].length) (baseStart_8167114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167114 prefixEnd_8167114 := by exact prefixLift 8167114
  have htrace : WordTrace (prefixWord ++ tailWord_8167114) baseStart_8167114 baseEnd_8167114 := by
    simpa [prefixWord, tailWord_8167114, baseEnd_8167114] using wordTrace_append hprefix tailTrace_8167114
  have hstable : (prefixWord ++ tailWord_8167114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167114).length < 2 ^ (prefixWord ++ tailWord_8167114).sum := by decide
  have hdescent : baseEnd_8167114 < baseStart_8167114 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167130 : List Nat := [3, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3]
def baseStart_8167130 : Nat := 118140960795 + 8167130 * 2 ^ 59
def prefixEnd_8167130 : Nat := 4983230072969 + 3 ^ 40 * 8167130 * 2
def baseEnd_8167130 : Nat := 4193663257754736300015059

theorem tailTrace_8167130 : CollatzResearch.WordTrace tailWord_8167130 prefixEnd_8167130 4193663257754736300015059 := by
  unfold tailWord_8167130
  simp only [CollatzResearch.WordTrace]
  refine ⟨74469925725472579900160711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198586468601260213067095229 74469925725472579900160711)
  ·
    refine ⟨111704888588208869850241067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74469925725472579900160711 111704888588208869850241067)
    ·
      refine ⟨167557332882313304775361601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111704888588208869850241067 167557332882313304775361601)
      ·
        refine ⟨125667999661734978581521201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167557332882313304775361601 125667999661734978581521201)
        ·
          refine ⟨94250999746301233936140901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125667999661734978581521201 94250999746301233936140901)
          ·
            refine ⟨17672062452431481363026419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94250999746301233936140901 17672062452431481363026419)
            ·
              refine ⟨26508093678647222044539629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17672062452431481363026419 26508093678647222044539629)
              ·
                refine ⟨9940535129492708266702361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26508093678647222044539629 9940535129492708266702361)
                ·
                  refine ⟨7455401347119531200026771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9940535129492708266702361 7455401347119531200026771)
                  ·
                    refine ⟨11183102020679296800040157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7455401347119531200026771 11183102020679296800040157)
                    ·
                      refine ⟨4193663257754736300015059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11183102020679296800040157 4193663257754736300015059)
                      ·
                        rfl

theorem cell23_8167130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_8167130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167130 prefixEnd_8167130 := by exact prefixLift 8167130
  have htrace : WordTrace (prefixWord ++ tailWord_8167130) baseStart_8167130 baseEnd_8167130 := by
    simpa [prefixWord, tailWord_8167130, baseEnd_8167130] using wordTrace_append hprefix tailTrace_8167130
  have hstable : (prefixWord ++ tailWord_8167130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167130).length < 2 ^ (prefixWord ++ tailWord_8167130).sum := by decide
  have hdescent : baseEnd_8167130 < baseStart_8167130 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167153 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 3, 4, 2]
def baseStart_8167153 : Nat := 118140960795 + 8167153 * 2 ^ 59
def prefixEnd_8167153 : Nat := 4983230072969 + 3 ^ 40 * 8167153 * 2
def baseEnd_8167153 : Nat := 4193675067809789710027453

theorem tailTrace_8167153 : CollatzResearch.WordTrace tailWord_8167153 prefixEnd_8167153 4193675067809789710027453 := by
  unfold tailWord_8167153
  simp only [CollatzResearch.WordTrace]
  refine ⟨297880541780806994528730113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198587027853871329685820075 297880541780806994528730113)
  ·
    refine ⟨223410406335605245896547585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297880541780806994528730113 223410406335605245896547585)
    ·
      refine ⟨167557804751703934422410689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223410406335605245896547585 167557804751703934422410689)
      ·
        refine ⟨125668353563777950816808017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167557804751703934422410689 125668353563777950816808017)
        ·
          refine ⟨94251265172833463112606013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125668353563777950816808017 94251265172833463112606013)
          ·
            refine ⟨35344224439812548667227255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94251265172833463112606013 35344224439812548667227255)
            ·
              refine ⟨53016336659718823000840883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35344224439812548667227255 53016336659718823000840883)
              ·
                refine ⟨79524504989578234501261325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53016336659718823000840883 79524504989578234501261325)
                ·
                  refine ⟨29821689371091837937972997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79524504989578234501261325 29821689371091837937972997)
                  ·
                    refine ⟨5591566757079719613369937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29821689371091837937972997 5591566757079719613369937)
                    ·
                      refine ⟨4193675067809789710027453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5591566757079719613369937 4193675067809789710027453)
                      ·
                        rfl

theorem cell23_8167153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 4, 2].length) (baseStart_8167153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167153 prefixEnd_8167153 := by exact prefixLift 8167153
  have htrace : WordTrace (prefixWord ++ tailWord_8167153) baseStart_8167153 baseEnd_8167153 := by
    simpa [prefixWord, tailWord_8167153, baseEnd_8167153] using wordTrace_append hprefix tailTrace_8167153
  have hstable : (prefixWord ++ tailWord_8167153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167153).length < 2 ^ (prefixWord ++ tailWord_8167153).sum := by decide
  have hdescent : baseEnd_8167153 < baseStart_8167153 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167170 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 3, 4, 2]
def baseStart_8167170 : Nat := 118140960795 + 8167170 * 2 ^ 59
def prefixEnd_8167170 : Nat := 4983230072969 + 3 ^ 40 * 8167170 * 2
def baseEnd_8167170 : Nat := 4193683796980916143514875

theorem tailTrace_8167170 : CollatzResearch.WordTrace tailWord_8167170 prefixEnd_8167170 4193683796980916143514875 := by
  unfold tailWord_8167170
  simp only [CollatzResearch.WordTrace]
  refine ⟨74470290455436351608024741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198587441214496937621399309 74470290455436351608024741)
  ·
    refine ⟨13963179460394315926504639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74470290455436351608024741 13963179460394315926504639)
    ·
      refine ⟨20944769190591473889756959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13963179460394315926504639 20944769190591473889756959)
      ·
        refine ⟨31417153785887210834635439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20944769190591473889756959 31417153785887210834635439)
        ·
          refine ⟨47125730678830816251953159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31417153785887210834635439 47125730678830816251953159)
          ·
            refine ⟨70688596018246224377929739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47125730678830816251953159 70688596018246224377929739)
            ·
              refine ⟨106032894027369336566894609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70688596018246224377929739 106032894027369336566894609)
              ·
                refine ⟨79524670520527002425170957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106032894027369336566894609 79524670520527002425170957)
                ·
                  refine ⟨29821751445197625909439109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79524670520527002425170957 29821751445197625909439109)
                  ·
                    refine ⟨5591578395974554858019833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29821751445197625909439109 5591578395974554858019833)
                    ·
                      refine ⟨4193683796980916143514875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5591578395974554858019833 4193683796980916143514875)
                      ·
                        rfl

theorem cell23_8167170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_8167170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167170 prefixEnd_8167170 := by exact prefixLift 8167170
  have htrace : WordTrace (prefixWord ++ tailWord_8167170) baseStart_8167170 baseEnd_8167170 := by
    simpa [prefixWord, tailWord_8167170, baseEnd_8167170] using wordTrace_append hprefix tailTrace_8167170
  have hstable : (prefixWord ++ tailWord_8167170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167170).length < 2 ^ (prefixWord ++ tailWord_8167170).sum := by decide
  have hdescent : baseEnd_8167170 < baseStart_8167170 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167176 : List Nat := [2, 1, 3, 2, 2, 1, 2, 3, 7]
def baseStart_8167176 : Nat := 118140960795 + 8167176 * 2 ^ 59
def prefixEnd_8167176 : Nat := 4983230072969 + 3 ^ 40 * 8167176 * 2
def baseEnd_8167176 : Nat := 465965208651649235559983

theorem tailTrace_8167176 : CollatzResearch.WordTrace tailWord_8167176 prefixEnd_8167176 465965208651649235559983 := by
  unfold tailWord_8167176
  simp only [CollatzResearch.WordTrace]
  refine ⟨148940690329861834728408691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198587587106482446304544921 148940690329861834728408691)
  ·
    refine ⟨223411035494792752092613037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148940690329861834728408691 223411035494792752092613037)
    ·
      refine ⟨83779138310547282034729889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223411035494792752092613037 83779138310547282034729889)
      ·
        refine ⟨62834353732910461526047417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83779138310547282034729889 62834353732910461526047417)
        ·
          refine ⟨47125765299682846144535563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62834353732910461526047417 47125765299682846144535563)
          ·
            refine ⟨70688647949524269216803345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47125765299682846144535563 70688647949524269216803345)
            ·
              refine ⟨53016485962143201912602509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70688647949524269216803345 53016485962143201912602509)
              ·
                refine ⟨19881182235803700717225941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53016485962143201912602509 19881182235803700717225941)
                ·
                  refine ⟨465965208651649235559983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19881182235803700717225941 465965208651649235559983)
                  ·
                    rfl

theorem cell23_8167176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 7].length) (baseStart_8167176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167176 prefixEnd_8167176 := by exact prefixLift 8167176
  have htrace : WordTrace (prefixWord ++ tailWord_8167176) baseStart_8167176 baseEnd_8167176 := by
    simpa [prefixWord, tailWord_8167176, baseEnd_8167176] using wordTrace_append hprefix tailTrace_8167176
  have hstable : (prefixWord ++ tailWord_8167176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167176).length < 2 ^ (prefixWord ++ tailWord_8167176).sum := by decide
  have hdescent : baseEnd_8167176 < baseStart_8167176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167181 : List Nat := [1, 7, 2, 1, 1, 1, 2, 1, 1, 3, 3]
def baseStart_8167181 : Nat := 118140960795 + 8167181 * 2 ^ 59
def prefixEnd_8167181 : Nat := 4983230072969 + 3 ^ 40 * 8167181 * 2
def baseEnd_8167181 : Nat := 4193689445268115600477325

theorem tailTrace_8167181 : CollatzResearch.WordTrace tailWord_8167181 prefixEnd_8167181 4193689445268115600477325 := by
  unfold tailWord_8167181
  simp only [CollatzResearch.WordTrace]
  refine ⟨297881563024705555310749397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198587708683137036873832931 297881563024705555310749397)
  ·
    refine ⟨6981599133391536452595689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 297881563024705555310749397 6981599133391536452595689)
    ·
      refine ⟨5236199350043652339446767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6981599133391536452595689 5236199350043652339446767)
      ·
        refine ⟨7854299025065478509170151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5236199350043652339446767 7854299025065478509170151)
        ·
          refine ⟨11781448537598217763755227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7854299025065478509170151 11781448537598217763755227)
          ·
            refine ⟨17672172806397326645632841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11781448537598217763755227 17672172806397326645632841)
            ·
              refine ⟨13254129604797994984224631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17672172806397326645632841 13254129604797994984224631)
              ·
                refine ⟨19881194407196992476336947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13254129604797994984224631 19881194407196992476336947)
                ·
                  refine ⟨29821791610795488714505421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19881194407196992476336947 29821791610795488714505421)
                  ·
                    refine ⟨11183171854048308267939533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29821791610795488714505421 11183171854048308267939533)
                    ·
                      refine ⟨4193689445268115600477325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11183171854048308267939533 4193689445268115600477325)
                      ·
                        rfl

theorem cell23_8167181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_8167181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167181 prefixEnd_8167181 := by exact prefixLift 8167181
  have htrace : WordTrace (prefixWord ++ tailWord_8167181) baseStart_8167181 baseEnd_8167181 := by
    simpa [prefixWord, tailWord_8167181, baseEnd_8167181] using wordTrace_append hprefix tailTrace_8167181
  have hstable : (prefixWord ++ tailWord_8167181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167181).length < 2 ^ (prefixWord ++ tailWord_8167181).sum := by decide
  have hdescent : baseEnd_8167181 < baseStart_8167181 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167220 : List Nat := [2, 5, 1, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_8167220 : Nat := 118140960795 + 8167220 * 2 ^ 59
def prefixEnd_8167220 : Nat := 4983230072969 + 3 ^ 40 * 8167220 * 2
def baseEnd_8167220 : Nat := 4193709471013640947889645

theorem tailTrace_8167220 : CollatzResearch.WordTrace tailWord_8167220 prefixEnd_8167220 4193709471013640947889645 := by
  unfold tailWord_8167220
  simp only [CollatzResearch.WordTrace]
  refine ⟨148941492735782132485709557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198588656981042843314279409 148941492735782132485709557)
  ·
    refine ⟨13963264943979574920535271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148941492735782132485709557 13963264943979574920535271)
    ·
      refine ⟨20944897415969362380802907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13963264943979574920535271 20944897415969362380802907)
      ·
        refine ⟨31417346123954043571204361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20944897415969362380802907 31417346123954043571204361)
        ·
          refine ⟨23563009592965532678403271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31417346123954043571204361 23563009592965532678403271)
          ·
            refine ⟨35344514389448299017604907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23563009592965532678403271 35344514389448299017604907)
            ·
              refine ⟨53016771584172448526407361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35344514389448299017604907 53016771584172448526407361)
              ·
                refine ⟨39762578688129336394805521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53016771584172448526407361 39762578688129336394805521)
                ·
                  refine ⟨29821934016097002296104141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39762578688129336394805521 29821934016097002296104141)
                  ·
                    refine ⟨11183225256036375861039053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29821934016097002296104141 11183225256036375861039053)
                    ·
                      refine ⟨4193709471013640947889645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11183225256036375861039053 4193709471013640947889645)
                      ·
                        rfl

theorem cell23_8167220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_8167220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167220 prefixEnd_8167220 := by exact prefixLift 8167220
  have htrace : WordTrace (prefixWord ++ tailWord_8167220) baseStart_8167220 baseEnd_8167220 := by
    simpa [prefixWord, tailWord_8167220, baseEnd_8167220] using wordTrace_append hprefix tailTrace_8167220
  have hstable : (prefixWord ++ tailWord_8167220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167220).length < 2 ^ (prefixWord ++ tailWord_8167220).sum := by decide
  have hdescent : baseEnd_8167220 < baseStart_8167220 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167221 : List Nat := [1, 3, 3, 1, 5, 1, 1, 2, 2, 2, 2]
def baseStart_8167221 : Nat := 118140960795 + 8167221 * 2 ^ 59
def prefixEnd_8167221 : Nat := 4983230072969 + 3 ^ 40 * 8167221 * 2
def baseEnd_8167221 : Nat := 4193709984494295443977141

theorem tailTrace_8167221 : CollatzResearch.WordTrace tailWord_8167221 prefixEnd_8167221 4193709984494295443977141 := by
  unfold tailWord_8167221
  simp only [CollatzResearch.WordTrace]
  refine ⟨297883021944560642142205517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198588681296373761428137011 297883021944560642142205517)
  ·
    refine ⟨111706133229210240803327069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297883021944560642142205517 111706133229210240803327069)
    ·
      refine ⟨41889799960953840301247651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111706133229210240803327069 41889799960953840301247651)
      ·
        refine ⟨62834699941430760451871477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41889799960953840301247651 62834699941430760451871477)
        ·
          refine ⟨5890753119509133792362951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62834699941430760451871477 5890753119509133792362951)
          ·
            refine ⟨8836129679263700688544427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5890753119509133792362951 8836129679263700688544427)
            ·
              refine ⟨13254194518895551032816641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8836129679263700688544427 13254194518895551032816641)
              ·
                refine ⟨9940645889171663274612481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13254194518895551032816641 9940645889171663274612481)
                ·
                  refine ⟨7455484416878747455959361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9940645889171663274612481 7455484416878747455959361)
                  ·
                    refine ⟨5591613312659060591969521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7455484416878747455959361 5591613312659060591969521)
                    ·
                      refine ⟨4193709984494295443977141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5591613312659060591969521 4193709984494295443977141)
                      ·
                        rfl

theorem cell23_8167221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_8167221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167221 prefixEnd_8167221 := by exact prefixLift 8167221
  have htrace : WordTrace (prefixWord ++ tailWord_8167221) baseStart_8167221 baseEnd_8167221 := by
    simpa [prefixWord, tailWord_8167221, baseEnd_8167221] using wordTrace_append hprefix tailTrace_8167221
  have hstable : (prefixWord ++ tailWord_8167221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167221).length < 2 ^ (prefixWord ++ tailWord_8167221).sum := by decide
  have hdescent : baseEnd_8167221 < baseStart_8167221 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167238 : List Nat := [6, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2]
def baseStart_8167238 : Nat := 118140960795 + 8167238 * 2 ^ 59
def prefixEnd_8167238 : Nat := 4983230072969 + 3 ^ 40 * 8167238 * 2
def baseEnd_8167238 : Nat := 4193718713665421877464563

theorem tailTrace_8167238 : CollatzResearch.WordTrace tailWord_8167238 prefixEnd_8167238 4193718713665421877464563 := by
  unfold tailWord_8167238
  simp only [CollatzResearch.WordTrace]
  refine ⟨9308863812046845438924199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 198589094656999369363716245 9308863812046845438924199)
  ·
    refine ⟨13963295718070268158386299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9308863812046845438924199 13963295718070268158386299)
    ·
      refine ⟨20944943577105402237579449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13963295718070268158386299 20944943577105402237579449)
      ·
        refine ⟨15708707682829051678184587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20944943577105402237579449 15708707682829051678184587)
        ·
          refine ⟨23563061524243577517276881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15708707682829051678184587 23563061524243577517276881)
          ·
            refine ⟨17672296143182683137957661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23563061524243577517276881 17672296143182683137957661)
            ·
              refine ⟨6627111053693506176734123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17672296143182683137957661 6627111053693506176734123)
              ·
                refine ⟨9940666580540259265101185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6627111053693506176734123 9940666580540259265101185)
                ·
                  refine ⟨7455499935405194448825889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9940666580540259265101185 7455499935405194448825889)
                  ·
                    refine ⟨5591624951553895836619417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7455499935405194448825889 5591624951553895836619417)
                    ·
                      refine ⟨4193718713665421877464563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5591624951553895836619417 4193718713665421877464563)
                      ·
                        rfl

theorem cell23_8167238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_8167238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167238 prefixEnd_8167238 := by exact prefixLift 8167238
  have htrace : WordTrace (prefixWord ++ tailWord_8167238) baseStart_8167238 baseEnd_8167238 := by
    simpa [prefixWord, tailWord_8167238, baseEnd_8167238] using wordTrace_append hprefix tailTrace_8167238
  have hstable : (prefixWord ++ tailWord_8167238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167238).length < 2 ^ (prefixWord ++ tailWord_8167238).sum := by decide
  have hdescent : baseEnd_8167238 < baseStart_8167238 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167263 : List Nat := [1, 1, 2, 3, 1, 4, 2, 1, 1, 4, 3]
def baseStart_8167263 : Nat := 118140960795 + 8167263 * 2 ^ 59
def prefixEnd_8167263 : Nat := 4983230072969 + 3 ^ 40 * 8167263 * 2
def baseEnd_8167263 : Nat := 4193731550681784279651947

theorem tailTrace_8167263 : CollatzResearch.WordTrace tailWord_8167263 prefixEnd_8167263 4193731550681784279651947 := by
  unfold tailWord_8167263
  simp only [CollatzResearch.WordTrace]
  refine ⟨297884553810408483315234443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198589702540272322210156295 297884553810408483315234443)
  ·
    refine ⟨446826830715612724972851665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297884553810408483315234443 446826830715612724972851665)
    ·
      refine ⟨335120123036709543729638749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446826830715612724972851665 335120123036709543729638749)
      ·
        refine ⟨125670046138766078898614531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335120123036709543729638749 125670046138766078898614531)
        ·
          refine ⟨188505069208149118347921797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125670046138766078898614531 188505069208149118347921797)
          ·
            refine ⟨35344700476527959690235337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188505069208149118347921797 35344700476527959690235337)
            ·
              refine ⟨26508525357395969767676503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35344700476527959690235337 26508525357395969767676503)
              ·
                refine ⟨39762788036093954651514755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26508525357395969767676503 39762788036093954651514755)
                ·
                  refine ⟨59644182054140931977272133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39762788036093954651514755 59644182054140931977272133)
                  ·
                    refine ⟨11183284135151424745738525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59644182054140931977272133 11183284135151424745738525)
                    ·
                      refine ⟨4193731550681784279651947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11183284135151424745738525 4193731550681784279651947)
                      ·
                        rfl

theorem cell23_8167263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_8167263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167263 prefixEnd_8167263 := by exact prefixLift 8167263
  have htrace : WordTrace (prefixWord ++ tailWord_8167263) baseStart_8167263 baseEnd_8167263 := by
    simpa [prefixWord, tailWord_8167263, baseEnd_8167263] using wordTrace_append hprefix tailTrace_8167263
  have hstable : (prefixWord ++ tailWord_8167263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167263).length < 2 ^ (prefixWord ++ tailWord_8167263).sum := by decide
  have hdescent : baseEnd_8167263 < baseStart_8167263 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167300 : List Nat := [2, 3, 2, 1, 1, 1, 6, 1, 6]
def baseStart_8167300 : Nat := 118140960795 + 8167300 * 2 ^ 59
def prefixEnd_8167300 : Nat := 4983230072969 + 3 ^ 40 * 8167300 * 2
def baseEnd_8167300 : Nat := 465972283274000070543253

theorem tailTrace_8167300 : CollatzResearch.WordTrace tailWord_8167300 prefixEnd_8167300 465972283274000070543253 := by
  unfold tailWord_8167300
  simp only [CollatzResearch.WordTrace]
  refine ⟨148942951655637219317165677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198590602207516292422887569 148942951655637219317165677)
  ·
    refine ⟨55853606870863957243937129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148942951655637219317165677 55853606870863957243937129)
    ·
      refine ⟨41890205153147967932952847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55853606870863957243937129 41890205153147967932952847)
      ·
        refine ⟨62835307729721951899429271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41890205153147967932952847 62835307729721951899429271)
        ·
          refine ⟨94252961594582927849143907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62835307729721951899429271 94252961594582927849143907)
          ·
            refine ⟨141379442391874391773715861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94252961594582927849143907 141379442391874391773715861)
            ·
              refine ⟨6627161362119112114392931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141379442391874391773715861 6627161362119112114392931)
              ·
                refine ⟨9940742043178668171589397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6627161362119112114392931 9940742043178668171589397)
                ·
                  refine ⟨465972283274000070543253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9940742043178668171589397 465972283274000070543253)
                  ·
                    rfl

theorem cell23_8167300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 6].length) (baseStart_8167300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167300 prefixEnd_8167300 := by exact prefixLift 8167300
  have htrace : WordTrace (prefixWord ++ tailWord_8167300) baseStart_8167300 baseEnd_8167300 := by
    simpa [prefixWord, tailWord_8167300, baseEnd_8167300] using wordTrace_append hprefix tailTrace_8167300
  have hstable : (prefixWord ++ tailWord_8167300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167300).length < 2 ^ (prefixWord ++ tailWord_8167300).sum := by decide
  have hdescent : baseEnd_8167300 < baseStart_8167300 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167353 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 3, 1, 5]
def baseStart_8167353 : Nat := 118140960795 + 8167353 * 2 ^ 59
def prefixEnd_8167353 : Nat := 4983230072969 + 3 ^ 40 * 8167353 * 2
def baseEnd_8167353 : Nat := 4193777763940688927526533

theorem tailTrace_8167353 : CollatzResearch.WordTrace tailWord_8167353 prefixEnd_8167353 4193777763940688927526533 := by
  unfold tailWord_8167353
  simp only [CollatzResearch.WordTrace]
  refine ⟨297887836380082428686010713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198591890920054952457340475 297887836380082428686010713)
  ·
    refine ⟨223415877285061821514508035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297887836380082428686010713 223415877285061821514508035)
    ·
      refine ⟨335123815927592732271762053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223415877285061821514508035 335123815927592732271762053)
      ·
        refine ⟨62835715486423637300955385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 335123815927592732271762053 62835715486423637300955385)
        ·
          refine ⟨47126786614817727975716539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62835715486423637300955385 47126786614817727975716539)
          ·
            refine ⟨70690179922226591963574809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47126786614817727975716539 70690179922226591963574809)
            ·
              refine ⟨53017634941669943972681107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70690179922226591963574809 53017634941669943972681107)
              ·
                refine ⟨79526452412504915959021661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53017634941669943972681107 79526452412504915959021661)
                ·
                  refine ⟨29822419654689343484633123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79526452412504915959021661 29822419654689343484633123)
                  ·
                    refine ⟨44733629482034015226949685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29822419654689343484633123 44733629482034015226949685)
                    ·
                      refine ⟨4193777763940688927526533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44733629482034015226949685 4193777763940688927526533)
                      ·
                        rfl

theorem cell23_8167353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_8167353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167353 prefixEnd_8167353 := by exact prefixLift 8167353
  have htrace : WordTrace (prefixWord ++ tailWord_8167353) baseStart_8167353 baseEnd_8167353 := by
    simpa [prefixWord, tailWord_8167353, baseEnd_8167353] using wordTrace_append hprefix tailTrace_8167353
  have hstable : (prefixWord ++ tailWord_8167353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167353).length < 2 ^ (prefixWord ++ tailWord_8167353).sum := by decide
  have hdescent : baseEnd_8167353 < baseStart_8167353 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167360 : List Nat := [2, 1, 1, 2, 3, 2, 1, 5, 2, 4]
def baseStart_8167360 : Nat := 118140960795 + 8167360 * 2 ^ 59
def prefixEnd_8167360 : Nat := 4983230072969 + 3 ^ 40 * 8167360 * 2
def baseEnd_8167360 : Nat := 1397927119435090133379667

theorem tailTrace_8167360 : CollatzResearch.WordTrace tailWord_8167360 prefixEnd_8167360 1397927119435090133379667 := by
  unfold tailWord_8167360
  simp only [CollatzResearch.WordTrace]
  refine ⟨148944045845528534440757767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198592061127371379254343689 148944045845528534440757767)
  ·
    refine ⟨223416068768292801661136651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148944045845528534440757767 223416068768292801661136651)
    ·
      refine ⟨335124103152439202491704977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223416068768292801661136651 335124103152439202491704977)
      ·
        refine ⟨251343077364329401868778733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335124103152439202491704977 251343077364329401868778733)
        ·
          refine ⟨94253654011623525700792025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251343077364329401868778733 94253654011623525700792025)
          ·
            refine ⟨70690240508717644275594019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94253654011623525700792025 70690240508717644275594019)
            ·
              refine ⟨106035360763076466413391029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70690240508717644275594019 106035360763076466413391029)
              ·
                refine ⟨9940815071538418726255409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106035360763076466413391029 9940815071538418726255409)
                ·
                  refine ⟨7455611303653814044691557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9940815071538418726255409 7455611303653814044691557)
                  ·
                    refine ⟨1397927119435090133379667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7455611303653814044691557 1397927119435090133379667)
                    ·
                      rfl

theorem cell23_8167360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 2, 4].length) (baseStart_8167360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167360 prefixEnd_8167360 := by exact prefixLift 8167360
  have htrace : WordTrace (prefixWord ++ tailWord_8167360) baseStart_8167360 baseEnd_8167360 := by
    simpa [prefixWord, tailWord_8167360, baseEnd_8167360] using wordTrace_append hprefix tailTrace_8167360
  have hstable : (prefixWord ++ tailWord_8167360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167360).length < 2 ^ (prefixWord ++ tailWord_8167360).sum := by decide
  have hdescent : baseEnd_8167360 < baseStart_8167360 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167370 : List Nat := [3, 1, 2, 1, 2, 1, 4, 1, 3, 2, 3]
def baseStart_8167370 : Nat := 118140960795 + 8167370 * 2 ^ 59
def prefixEnd_8167370 : Nat := 4983230072969 + 3 ^ 40 * 8167370 * 2
def baseEnd_8167370 : Nat := 4193786493111815361013955

theorem tailTrace_8167370 : CollatzResearch.WordTrace tailWord_8167370 prefixEnd_8167370 4193786493111815361013955 := by
  unfold tailWord_8167370
  simp only [CollatzResearch.WordTrace]
  refine ⟨74472114105255210147344891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198592304280680560392919709 74472114105255210147344891)
  ·
    refine ⟨111708171157882815221017337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74472114105255210147344891 111708171157882815221017337)
    ·
      refine ⟨83781128368412111415763003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111708171157882815221017337 83781128368412111415763003)
      ·
        refine ⟨125671692552618167123644505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83781128368412111415763003 125671692552618167123644505)
        ·
          refine ⟨94253769414463625342733379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125671692552618167123644505 94253769414463625342733379)
          ·
            refine ⟨141380654121695438014100069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94253769414463625342733379 141380654121695438014100069)
            ·
              refine ⟨26508872647817894627643763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141380654121695438014100069 26508872647817894627643763)
              ·
                refine ⟨39763308971726841941465645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26508872647817894627643763 39763308971726841941465645)
                ·
                  refine ⟨14911240864397565728049617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39763308971726841941465645 14911240864397565728049617)
                  ·
                    refine ⟨11183430648298174296037213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14911240864397565728049617 11183430648298174296037213)
                    ·
                      refine ⟨4193786493111815361013955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11183430648298174296037213 4193786493111815361013955)
                      ·
                        rfl

theorem cell23_8167370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_8167370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167370 prefixEnd_8167370 := by exact prefixLift 8167370
  have htrace : WordTrace (prefixWord ++ tailWord_8167370) baseStart_8167370 baseEnd_8167370 := by
    simpa [prefixWord, tailWord_8167370, baseEnd_8167370] using wordTrace_append hprefix tailTrace_8167370
  have hstable : (prefixWord ++ tailWord_8167370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167370).length < 2 ^ (prefixWord ++ tailWord_8167370).sum := by decide
  have hdescent : baseEnd_8167370 < baseStart_8167370 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167380 : List Nat := [2, 4, 1, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_8167380 : Nat := 118140960795 + 8167380 * 2 ^ 59
def prefixEnd_8167380 : Nat := 4983230072969 + 3 ^ 40 * 8167380 * 2
def baseEnd_8167380 : Nat := 4193791627918360321888909

theorem tailTrace_8167380 : CollatzResearch.WordTrace tailWord_8167380 prefixEnd_8167380 4193791627918360321888909 := by
  unfold tailWord_8167380
  simp only [CollatzResearch.WordTrace]
  refine ⟨148944410575492306148621797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198592547433989741531495729 148944410575492306148621797)
  ·
    refine ⟨27927076982904807402866587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148944410575492306148621797 27927076982904807402866587)
    ·
      refine ⟨41890615474357211104299881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27927076982904807402866587 41890615474357211104299881)
      ·
        refine ⟨31417961605767908328224911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41890615474357211104299881 31417961605767908328224911)
        ·
          refine ⟨47126942408651862492337367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31417961605767908328224911 47126942408651862492337367)
          ·
            refine ⟨70690413612977793738506051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47126942408651862492337367 70690413612977793738506051)
            ·
              refine ⟨106035620419466690607759077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70690413612977793738506051 106035620419466690607759077)
              ·
                refine ⟨19881678828650004488954827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106035620419466690607759077 19881678828650004488954827)
                ·
                  refine ⟨29822518242975006733432241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19881678828650004488954827 29822518242975006733432241)
                  ·
                    refine ⟨22366888682231255050074181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29822518242975006733432241 22366888682231255050074181)
                    ·
                      refine ⟨4193791627918360321888909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22366888682231255050074181 4193791627918360321888909)
                      ·
                        rfl

theorem cell23_8167380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_8167380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167380 prefixEnd_8167380 := by exact prefixLift 8167380
  have htrace : WordTrace (prefixWord ++ tailWord_8167380) baseStart_8167380 baseEnd_8167380 := by
    simpa [prefixWord, tailWord_8167380, baseEnd_8167380] using wordTrace_append hprefix tailTrace_8167380
  have hstable : (prefixWord ++ tailWord_8167380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167380).length < 2 ^ (prefixWord ++ tailWord_8167380).sum := by decide
  have hdescent : baseEnd_8167380 < baseStart_8167380 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167394 : List Nat := [3, 3, 3, 1, 2, 1, 1, 1, 4, 4]
def baseStart_8167394 : Nat := 118140960795 + 8167394 * 2 ^ 59
def prefixEnd_8167394 : Nat := 4983230072969 + 3 ^ 40 * 8167394 * 2
def baseEnd_8167394 : Nat := 1397932938882507755704615

theorem tailTrace_8167394 : CollatzResearch.WordTrace tailWord_8167394 prefixEnd_8167394 1397932938882507755704615 := by
  unfold tailWord_8167394
  simp only [CollatzResearch.WordTrace]
  refine ⟨74472332943233473172063309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198592887848622595125502157 74472332943233473172063309)
  ·
    refine ⟨27927124853712552439523741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74472332943233473172063309 27927124853712552439523741)
    ·
      refine ⟨10472671820142207164821403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27927124853712552439523741 10472671820142207164821403)
      ·
        refine ⟨15709007730213310747232105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10472671820142207164821403 15709007730213310747232105)
        ·
          refine ⟨11781755797659983060424079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15709007730213310747232105 11781755797659983060424079)
          ·
            refine ⟨17672633696489974590636119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11781755797659983060424079 17672633696489974590636119)
            ·
              refine ⟨26508950544734961885954179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17672633696489974590636119 26508950544734961885954179)
              ·
                refine ⟨39763425817102442828931269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26508950544734961885954179 39763425817102442828931269)
                ·
                  refine ⟨7455642340706708030424613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39763425817102442828931269 7455642340706708030424613)
                  ·
                    refine ⟨1397932938882507755704615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7455642340706708030424613 1397932938882507755704615)
                    ·
                      rfl

theorem cell23_8167394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_8167394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167394 prefixEnd_8167394 := by exact prefixLift 8167394
  have htrace : WordTrace (prefixWord ++ tailWord_8167394) baseStart_8167394 baseEnd_8167394 := by
    simpa [prefixWord, tailWord_8167394, baseEnd_8167394] using wordTrace_append hprefix tailTrace_8167394
  have hstable : (prefixWord ++ tailWord_8167394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167394).length < 2 ^ (prefixWord ++ tailWord_8167394).sum := by decide
  have hdescent : baseEnd_8167394 < baseStart_8167394 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167414 : List Nat := [5, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4]
def baseStart_8167414 : Nat := 118140960795 + 8167414 * 2 ^ 59
def prefixEnd_8167414 : Nat := 4983230072969 + 3 ^ 40 * 8167414 * 2
def baseEnd_8167414 : Nat := 4193809086260613188863753

theorem tailTrace_8167414 : CollatzResearch.WordTrace tailWord_8167414 prefixEnd_8167414 4193809086260613188863753 := by
  unfold tailWord_8167414
  simp only [CollatzResearch.WordTrace]
  refine ⟨18618128827053839756498831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198593374155240957402654197 18618128827053839756498831)
  ·
    refine ⟨27927193240580759634748247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18618128827053839756498831 27927193240580759634748247)
    ·
      refine ⟨41890789860871139452122371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27927193240580759634748247 41890789860871139452122371)
      ·
        refine ⟨62836184791306709178183557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41890789860871139452122371 62836184791306709178183557)
        ·
          refine ⟨11781784648370007970909417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62836184791306709178183557 11781784648370007970909417)
          ·
            refine ⟨8836338486277505978182063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11781784648370007970909417 8836338486277505978182063)
            ·
              refine ⟨13254507729416258967273095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8836338486277505978182063 13254507729416258967273095)
              ·
                refine ⟨19881761594124388450909643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13254507729416258967273095 19881761594124388450909643)
                ·
                  refine ⟨29822642391186582676364465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19881761594124388450909643 29822642391186582676364465)
                  ·
                    refine ⟨22366981793389937007273349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29822642391186582676364465 22366981793389937007273349)
                    ·
                      refine ⟨4193809086260613188863753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22366981793389937007273349 4193809086260613188863753)
                      ·
                        rfl

theorem cell23_8167414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_8167414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167414 prefixEnd_8167414 := by exact prefixLift 8167414
  have htrace : WordTrace (prefixWord ++ tailWord_8167414) baseStart_8167414 baseEnd_8167414 := by
    simpa [prefixWord, tailWord_8167414, baseEnd_8167414] using wordTrace_append hprefix tailTrace_8167414
  have hstable : (prefixWord ++ tailWord_8167414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167414).length < 2 ^ (prefixWord ++ tailWord_8167414).sum := by decide
  have hdescent : baseEnd_8167414 < baseStart_8167414 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167417 : List Nat := [1, 2, 1, 3, 1, 6, 1, 1, 1, 3, 3]
def baseStart_8167417 : Nat := 118140960795 + 8167417 * 2 ^ 59
def prefixEnd_8167417 : Nat := 4983230072969 + 3 ^ 40 * 8167417 * 2
def baseEnd_8167417 : Nat := 4193810626702576677126239

theorem tailTrace_8167417 : CollatzResearch.WordTrace tailWord_8167417 prefixEnd_8167417 4193810626702576677126239 := by
  unfold tailWord_8167417
  simp only [CollatzResearch.WordTrace]
  refine ⟨297890170651850567616340505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198593447101233711744227003 297890170651850567616340505)
  ·
    refine ⟨223417627988887925712255379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297890170651850567616340505 223417627988887925712255379)
    ·
      refine ⟨335126441983331888568383069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223417627988887925712255379 335126441983331888568383069)
      ·
        refine ⟨125672415743749458213143651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335126441983331888568383069 125672415743749458213143651)
        ·
          refine ⟨188508623615624187319715477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125672415743749458213143651 188508623615624187319715477)
          ·
            refine ⟨8836341731982383780611663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 188508623615624187319715477 8836341731982383780611663)
            ·
              refine ⟨13254512597973575670917495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8836341731982383780611663 13254512597973575670917495)
              ·
                refine ⟨19881768896960363506376243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13254512597973575670917495 19881768896960363506376243)
                ·
                  refine ⟨29822653345440545259564365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19881768896960363506376243 29822653345440545259564365)
                  ·
                    refine ⟨11183495004540204472336637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29822653345440545259564365 11183495004540204472336637)
                    ·
                      refine ⟨4193810626702576677126239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11183495004540204472336637 4193810626702576677126239)
                      ·
                        rfl

theorem cell23_8167417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_8167417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167417 prefixEnd_8167417 := by exact prefixLift 8167417
  have htrace : WordTrace (prefixWord ++ tailWord_8167417) baseStart_8167417 baseEnd_8167417 := by
    simpa [prefixWord, tailWord_8167417, baseEnd_8167417] using wordTrace_append hprefix tailTrace_8167417
  have hstable : (prefixWord ++ tailWord_8167417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167417).length < 2 ^ (prefixWord ++ tailWord_8167417).sum := by decide
  have hdescent : baseEnd_8167417 < baseStart_8167417 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167423 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 4]
def baseStart_8167423 : Nat := 118140960795 + 8167423 * 2 ^ 59
def prefixEnd_8167423 : Nat := 4983230072969 + 3 ^ 40 * 8167423 * 2
def baseEnd_8167423 : Nat := 4193813707586503653651211

theorem tailTrace_8167423 : CollatzResearch.WordTrace tailWord_8167423 prefixEnd_8167423 4193813707586503653651211 := by
  unfold tailWord_8167423
  simp only [CollatzResearch.WordTrace]
  refine ⟨297890389489828830641058923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198593592993219220427372615 297890389489828830641058923)
  ·
    refine ⟨446835584234743245961588385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297890389489828830641058923 446835584234743245961588385)
    ·
      refine ⟨335126688176057434471191289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446835584234743245961588385 335126688176057434471191289)
      ·
        refine ⟨251345016132043075853393467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335126688176057434471191289 251345016132043075853393467)
        ·
          refine ⟨377017524198064613780090201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251345016132043075853393467 377017524198064613780090201)
          ·
            refine ⟨282763143148548460335067651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377017524198064613780090201 282763143148548460335067651)
            ·
              refine ⟨424144714722822690502601477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282763143148548460335067651 424144714722822690502601477)
              ·
                refine ⟨79527134010529254469237777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 424144714722822690502601477 79527134010529254469237777)
                ·
                  refine ⟨59645350507896940851928333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79527134010529254469237777 59645350507896940851928333)
                  ·
                    refine ⟨22367006440461352819473125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59645350507896940851928333 22367006440461352819473125)
                    ·
                      refine ⟨4193813707586503653651211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22367006440461352819473125 4193813707586503653651211)
                      ·
                        rfl

theorem cell23_8167423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_8167423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167423 prefixEnd_8167423 := by exact prefixLift 8167423
  have htrace : WordTrace (prefixWord ++ tailWord_8167423) baseStart_8167423 baseEnd_8167423 := by
    simpa [prefixWord, tailWord_8167423, baseEnd_8167423] using wordTrace_append hprefix tailTrace_8167423
  have hstable : (prefixWord ++ tailWord_8167423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167423).length < 2 ^ (prefixWord ++ tailWord_8167423).sum := by decide
  have hdescent : baseEnd_8167423 < baseStart_8167423 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167443 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 5]
def baseStart_8167443 : Nat := 118140960795 + 8167443 * 2 ^ 59
def prefixEnd_8167443 : Nat := 4983230072969 + 3 ^ 40 * 8167443 * 2
def baseEnd_8167443 : Nat := 4193823977199593575401119

theorem tailTrace_8167443 : CollatzResearch.WordTrace tailWord_8167443 prefixEnd_8167443 4193823977199593575401119 := by
  unfold tailWord_8167443
  simp only [CollatzResearch.WordTrace]
  refine ⟨297891118949756374056786983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198594079299837582704524655 297891118949756374056786983)
  ·
    refine ⟨446836678424634561085180475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297891118949756374056786983 446836678424634561085180475)
    ·
      refine ⟨670255017636951841627770713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446836678424634561085180475 670255017636951841627770713)
      ·
        refine ⟨502691263227713881220828035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 670255017636951841627770713 502691263227713881220828035)
        ·
          refine ⟨754036894841570821831242053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502691263227713881220828035 754036894841570821831242053)
          ·
            refine ⟨141381917782794529093357885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 754036894841570821831242053 141381917782794529093357885)
            ·
              refine ⟨53018219168547948410009207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141381917782794529093357885 53018219168547948410009207)
              ·
                refine ⟨79527328752821922615013811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53018219168547948410009207 79527328752821922615013811)
                ·
                  refine ⟨119290993129232883922520717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79527328752821922615013811 119290993129232883922520717)
                  ·
                    refine ⟨44734122423462331470945269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119290993129232883922520717 44734122423462331470945269)
                    ·
                      refine ⟨4193823977199593575401119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44734122423462331470945269 4193823977199593575401119)
                      ·
                        rfl

theorem cell23_8167443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 5].length) (baseStart_8167443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167443 prefixEnd_8167443 := by exact prefixLift 8167443
  have htrace : WordTrace (prefixWord ++ tailWord_8167443) baseStart_8167443 baseEnd_8167443 := by
    simpa [prefixWord, tailWord_8167443, baseEnd_8167443] using wordTrace_append hprefix tailTrace_8167443
  have hstable : (prefixWord ++ tailWord_8167443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167443).length < 2 ^ (prefixWord ++ tailWord_8167443).sum := by decide
  have hdescent : baseEnd_8167443 < baseStart_8167443 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167503 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 7]
def baseStart_8167503 : Nat := 118140960795 + 8167503 * 2 ^ 59
def prefixEnd_8167503 : Nat := 4983230072969 + 3 ^ 40 * 8167503 * 2
def baseEnd_8167503 : Nat := 4193854786038863340650843

theorem tailTrace_8167503 : CollatzResearch.WordTrace tailWord_8167503 prefixEnd_8167503 4193854786038863340650843 := by
  unfold tailWord_8167503
  simp only [CollatzResearch.WordTrace]
  refine ⟨297893307329539004303971163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198595538219692669535980775 297893307329539004303971163)
  ·
    refine ⟨446839960994308506455956745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297893307329539004303971163 446839960994308506455956745)
    ·
      refine ⟨335129970745731379841967559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446839960994308506455956745 335129970745731379841967559)
      ·
        refine ⟨502694956118597069762951339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335129970745731379841967559 502694956118597069762951339)
        ·
          refine ⟨754042434177895604644427009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502694956118597069762951339 754042434177895604644427009)
          ·
            refine ⟨565531825633421703483320257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 754042434177895604644427009 565531825633421703483320257)
            ·
              refine ⟨424148869225066277612490193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 565531825633421703483320257 424148869225066277612490193)
              ·
                refine ⟨318111651918799708209367645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 424148869225066277612490193 318111651918799708209367645)
                ·
                  refine ⟨119291869469549890578512867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 318111651918799708209367645 119291869469549890578512867)
                  ·
                    refine ⟨178937804204324835867769301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119291869469549890578512867 178937804204324835867769301)
                    ·
                      refine ⟨4193854786038863340650843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 178937804204324835867769301 4193854786038863340650843)
                      ·
                        rfl

theorem cell23_8167503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 7].length) (baseStart_8167503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167503 prefixEnd_8167503 := by exact prefixLift 8167503
  have htrace : WordTrace (prefixWord ++ tailWord_8167503) baseStart_8167503 baseEnd_8167503 := by
    simpa [prefixWord, tailWord_8167503, baseEnd_8167503] using wordTrace_append hprefix tailTrace_8167503
  have hstable : (prefixWord ++ tailWord_8167503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167503).length < 2 ^ (prefixWord ++ tailWord_8167503).sum := by decide
  have hdescent : baseEnd_8167503 < baseStart_8167503 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167520 : List Nat := [2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 5]
def baseStart_8167520 : Nat := 118140960795 + 8167520 * 2 ^ 59
def prefixEnd_8167520 : Nat := 4983230072969 + 3 ^ 40 * 8167520 * 2
def baseEnd_8167520 : Nat := 4193863515209989774138265

theorem tailTrace_8167520 : CollatzResearch.WordTrace tailWord_8167520 prefixEnd_8167520 4193863515209989774138265 := by
  unfold tailWord_8167520
  simp only [CollatzResearch.WordTrace]
  refine ⟨148946963685238708103670007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198595951580318277471560009 148946963685238708103670007)
  ·
    refine ⟨223420445527858062155505011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148946963685238708103670007 223420445527858062155505011)
    ·
      refine ⟨335130668291787093233257517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223420445527858062155505011 335130668291787093233257517)
      ·
        refine ⟨125674000609420159962471569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335130668291787093233257517 125674000609420159962471569)
        ·
          refine ⟨94255500457065119971853677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125674000609420159962471569 94255500457065119971853677)
          ·
            refine ⟨35345812671399419989445129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94255500457065119971853677 35345812671399419989445129)
            ·
              refine ⟨26509359503549564992083847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35345812671399419989445129 26509359503549564992083847)
              ·
                refine ⟨39764039255324347488125771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26509359503549564992083847 39764039255324347488125771)
                ·
                  refine ⟨59646058882986521232188657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39764039255324347488125771 59646058882986521232188657)
                  ·
                    refine ⟨44734544162239890924141493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59646058882986521232188657 44734544162239890924141493)
                    ·
                      refine ⟨4193863515209989774138265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44734544162239890924141493 4193863515209989774138265)
                      ·
                        rfl

theorem cell23_8167520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_8167520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167520 prefixEnd_8167520 := by exact prefixLift 8167520
  have htrace : WordTrace (prefixWord ++ tailWord_8167520) baseStart_8167520 baseEnd_8167520 := by
    simpa [prefixWord, tailWord_8167520, baseEnd_8167520] using wordTrace_append hprefix tailTrace_8167520
  have hstable : (prefixWord ++ tailWord_8167520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167520).length < 2 ^ (prefixWord ++ tailWord_8167520).sum := by decide
  have hdescent : baseEnd_8167520 < baseStart_8167520 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167618 : List Nat := [3, 5, 1, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_8167618 : Nat := 118140960795 + 8167618 * 2 ^ 59
def prefixEnd_8167618 : Nat := 4983230072969 + 3 ^ 40 * 8167618 * 2
def baseEnd_8167618 : Nat := 4193913836314130390712815

theorem tailTrace_8167618 : CollatzResearch.WordTrace tailWord_8167618 prefixEnd_8167618 4193913836314130390712815 := by
  unfold tailWord_8167618
  simp only [CollatzResearch.WordTrace]
  refine ⟨74474375431030594736101877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198598334482748252629605005 74474375431030594736101877)
  ·
    refine ⟨6981972696659118256509551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74474375431030594736101877 6981972696659118256509551)
    ·
      refine ⟨10472959044988677384764327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6981972696659118256509551 10472959044988677384764327)
      ·
        refine ⟨15709438567483016077146491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10472959044988677384764327 15709438567483016077146491)
        ·
          refine ⟨23564157851224524115719737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15709438567483016077146491 23564157851224524115719737)
          ·
            refine ⟨17673118388418393086789803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23564157851224524115719737 17673118388418393086789803)
            ·
              refine ⟨26509677582627589630184705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17673118388418393086789803 26509677582627589630184705)
              ·
                refine ⟨19882258186970692222638529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26509677582627589630184705 19882258186970692222638529)
                ·
                  refine ⟨14911693640228019166978897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19882258186970692222638529 14911693640228019166978897)
                  ·
                    refine ⟨11183770230171014375234173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14911693640228019166978897 11183770230171014375234173)
                    ·
                      refine ⟨4193913836314130390712815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11183770230171014375234173 4193913836314130390712815)
                      ·
                        rfl

theorem cell23_8167618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_8167618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167618 prefixEnd_8167618 := by exact prefixLift 8167618
  have htrace : WordTrace (prefixWord ++ tailWord_8167618) baseStart_8167618 baseEnd_8167618 := by
    simpa [prefixWord, tailWord_8167618, baseEnd_8167618] using wordTrace_append hprefix tailTrace_8167618
  have hstable : (prefixWord ++ tailWord_8167618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167618).length < 2 ^ (prefixWord ++ tailWord_8167618).sum := by decide
  have hdescent : baseEnd_8167618 < baseStart_8167618 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167638 : List Nat := [5, 2, 1, 2, 1, 3, 2, 1, 6]
def baseStart_8167638 : Nat := 118140960795 + 8167638 * 2 ^ 59
def prefixEnd_8167638 : Nat := 4983230072969 + 3 ^ 40 * 8167638 * 2
def baseEnd_8167638 : Nat := 465991567325246701384747

theorem tailTrace_8167638 : CollatzResearch.WordTrace tailWord_8167638 prefixEnd_8167638 465991567325246701384747 := by
  unfold tailWord_8167638
  simp only [CollatzResearch.WordTrace]
  refine ⟨18618639449003120147508473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198598820789366614906757045 18618639449003120147508473)
  ·
    refine ⟨13963979586752340110631355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18618639449003120147508473 13963979586752340110631355)
    ·
      refine ⟨20945969380128510165947033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13963979586752340110631355 20945969380128510165947033)
      ·
        refine ⟨15709477035096382624460275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20945969380128510165947033 15709477035096382624460275)
        ·
          refine ⟨23564215552644573936690413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15709477035096382624460275 23564215552644573936690413)
          ·
            refine ⟨8836580832241715226258905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23564215552644573936690413 8836580832241715226258905)
            ·
              refine ⟨6627435624181286419694179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8836580832241715226258905 6627435624181286419694179)
              ·
                refine ⟨9941153436271929629541269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6627435624181286419694179 9941153436271929629541269)
                ·
                  refine ⟨465991567325246701384747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9941153436271929629541269 465991567325246701384747)
                  ·
                    rfl

theorem cell23_8167638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_8167638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167638 prefixEnd_8167638 := by exact prefixLift 8167638
  have htrace : WordTrace (prefixWord ++ tailWord_8167638) baseStart_8167638 baseEnd_8167638 := by
    simpa [prefixWord, tailWord_8167638, baseEnd_8167638] using wordTrace_append hprefix tailTrace_8167638
  have hstable : (prefixWord ++ tailWord_8167638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167638).length < 2 ^ (prefixWord ++ tailWord_8167638).sum := by decide
  have hdescent : baseEnd_8167638 < baseStart_8167638 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167657 : List Nat := [1, 2, 1, 1, 1, 2, 2, 5, 3, 2, 3]
def baseStart_8167657 : Nat := 118140960795 + 8167657 * 2 ^ 59
def prefixEnd_8167657 : Nat := 4983230072969 + 3 ^ 40 * 8167657 * 2
def baseEnd_8167657 : Nat := 4193933862059655738125135

theorem tailTrace_8167657 : CollatzResearch.WordTrace tailWord_8167657 prefixEnd_8167657 4193933862059655738125135 := by
  unfold tailWord_8167657
  simp only [CollatzResearch.WordTrace]
  refine ⟨297898924170981088605077225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198599282780654059070051483 297898924170981088605077225)
  ·
    refine ⟨223424193128235816453807919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297898924170981088605077225 223424193128235816453807919)
    ·
      refine ⟨335136289692353724680711879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223424193128235816453807919 335136289692353724680711879)
      ·
        refine ⟨502704434538530587021067819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335136289692353724680711879 502704434538530587021067819)
        ·
          refine ⟨754056651807795880531601729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502704434538530587021067819 754056651807795880531601729)
          ·
            refine ⟨565542488855846910398701297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 754056651807795880531601729 565542488855846910398701297)
            ·
              refine ⟨424156866641885182799025973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 565542488855846910398701297 424156866641885182799025973)
              ·
                refine ⟨39764706247676735887408685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 424156866641885182799025973 39764706247676735887408685)
                ·
                  refine ⟨14911764842878775957778257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39764706247676735887408685 14911764842878775957778257)
                  ·
                    refine ⟨11183823632159081968333693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14911764842878775957778257 11183823632159081968333693)
                    ·
                      refine ⟨4193933862059655738125135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11183823632159081968333693 4193933862059655738125135)
                      ·
                        rfl

theorem cell23_8167657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 2, 3].length) (baseStart_8167657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167657 prefixEnd_8167657 := by exact prefixLift 8167657
  have htrace : WordTrace (prefixWord ++ tailWord_8167657) baseStart_8167657 baseEnd_8167657 := by
    simpa [prefixWord, tailWord_8167657, baseEnd_8167657] using wordTrace_append hprefix tailTrace_8167657
  have hstable : (prefixWord ++ tailWord_8167657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167657).length < 2 ^ (prefixWord ++ tailWord_8167657).sum := by decide
  have hdescent : baseEnd_8167657 < baseStart_8167657 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167660 : List Nat := [2, 2, 1, 1, 2, 3, 1, 11]
def baseStart_8167660 : Nat := 118140960795 + 8167660 * 2 ^ 59
def prefixEnd_8167660 : Nat := 4983230072969 + 3 ^ 40 * 8167660 * 2
def baseEnd_8167660 : Nat := 155330940833393304681023

theorem tailTrace_8167660 : CollatzResearch.WordTrace tailWord_8167660 prefixEnd_8167660 155330940833393304681023 := by
  unfold tailWord_8167660
  simp only [CollatzResearch.WordTrace]
  refine ⟨148949516794985110058718217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198599355726646813411624289 148949516794985110058718217)
  ·
    refine ⟨111712137596238832544038663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148949516794985110058718217 111712137596238832544038663)
    ·
      refine ⟨167568206394358248816057995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111712137596238832544038663 167568206394358248816057995)
      ·
        refine ⟨251352309591537373224086993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167568206394358248816057995 251352309591537373224086993)
        ·
          refine ⟨188514232193653029918065245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251352309591537373224086993 188514232193653029918065245)
          ·
            refine ⟨70692837072619886219274467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188514232193653029918065245 70692837072619886219274467)
            ·
              refine ⟨106039255608929829328911701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70692837072619886219274467 106039255608929829328911701)
              ·
                refine ⟨155330940833393304681023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 106039255608929829328911701 155330940833393304681023)
                ·
                  rfl

theorem cell23_8167660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 11].length) (baseStart_8167660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167660 prefixEnd_8167660 := by exact prefixLift 8167660
  have htrace : WordTrace (prefixWord ++ tailWord_8167660) baseStart_8167660 baseEnd_8167660 := by
    simpa [prefixWord, tailWord_8167660, baseEnd_8167660] using wordTrace_append hprefix tailTrace_8167660
  have hstable : (prefixWord ++ tailWord_8167660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167660).length < 2 ^ (prefixWord ++ tailWord_8167660).sum := by decide
  have hdescent : baseEnd_8167660 < baseStart_8167660 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167667 : List Nat := [1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 4]
def baseStart_8167667 : Nat := 118140960795 + 8167667 * 2 ^ 59
def prefixEnd_8167667 : Nat := 4983230072969 + 3 ^ 40 * 8167667 * 2
def baseEnd_8167667 : Nat := 4193938996866200699000089

theorem tailTrace_8167667 : CollatzResearch.WordTrace tailWord_8167667 prefixEnd_8167667 4193938996866200699000089 := by
  unfold tailWord_8167667
  simp only [CollatzResearch.WordTrace]
  refine ⟨297899288900944860312941255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198599525933963240208627503 297899288900944860312941255)
  ·
    refine ⟨446848933351417290469411883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297899288900944860312941255 446848933351417290469411883)
    ·
      refine ⟨670273400027125935704117825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446848933351417290469411883 670273400027125935704117825)
      ·
        refine ⟨502705050020344451778088369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 670273400027125935704117825 502705050020344451778088369)
        ·
          refine ⟨377028787515258338833566277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502705050020344451778088369 377028787515258338833566277)
          ·
            refine ⟨70692897659110938531293677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 377028787515258338833566277 70692897659110938531293677)
            ·
              refine ⟨26509836622166601949235129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70692897659110938531293677 26509836622166601949235129)
              ·
                refine ⟨19882377466624951461926347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26509836622166601949235129 19882377466624951461926347)
                ·
                  refine ⟨29823566199937427192889521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19882377466624951461926347 29823566199937427192889521)
                  ·
                    refine ⟨22367674649953070394667141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29823566199937427192889521 22367674649953070394667141)
                    ·
                      refine ⟨4193938996866200699000089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22367674649953070394667141 4193938996866200699000089)
                      ·
                        rfl

theorem cell23_8167667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 4].length) (baseStart_8167667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167667 prefixEnd_8167667 := by exact prefixLift 8167667
  have htrace : WordTrace (prefixWord ++ tailWord_8167667) baseStart_8167667 baseEnd_8167667 := by
    simpa [prefixWord, tailWord_8167667, baseEnd_8167667] using wordTrace_append hprefix tailTrace_8167667
  have hstable : (prefixWord ++ tailWord_8167667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167667).length < 2 ^ (prefixWord ++ tailWord_8167667).sum := by decide
  have hdescent : baseEnd_8167667 < baseStart_8167667 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167674 : List Nat := [3, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5]
def baseStart_8167674 : Nat := 118140960795 + 8167674 * 2 ^ 59
def prefixEnd_8167674 : Nat := 4983230072969 + 3 ^ 40 * 8167674 * 2
def baseEnd_8167674 : Nat := 4193942591230782171612557

theorem tailTrace_8167674 : CollatzResearch.WordTrace tailWord_8167674 prefixEnd_8167674 4193942591230782171612557 := by
  unfold tailWord_8167674
  simp only [CollatzResearch.WordTrace]
  refine ⟨74474886052979875127111519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198599696141279667005630717 74474886052979875127111519)
  ·
    refine ⟨111712329079469812690667279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74474886052979875127111519 111712329079469812690667279)
    ·
      refine ⟨167568493619204719036000919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111712329079469812690667279 167568493619204719036000919)
      ·
        refine ⟨251352740428807078554001379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167568493619204719036000919 251352740428807078554001379)
        ·
          refine ⟨377029110643210617831002069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251352740428807078554001379 377029110643210617831002069)
          ·
            refine ⟨8836619780700248855414111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 377029110643210617831002069 8836619780700248855414111)
            ·
              refine ⟨13254929671050373283121167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8836619780700248855414111 13254929671050373283121167)
              ·
                refine ⟨19882394506575559924681751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13254929671050373283121167 19882394506575559924681751)
                ·
                  refine ⟨29823591759863339887022627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19882394506575559924681751 29823591759863339887022627)
                  ·
                    refine ⟨44735387639795009830533941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29823591759863339887022627 44735387639795009830533941)
                    ·
                      refine ⟨4193942591230782171612557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44735387639795009830533941 4193942591230782171612557)
                      ·
                        rfl

theorem cell23_8167674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 1, 1, 5].length) (baseStart_8167674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167674 prefixEnd_8167674 := by exact prefixLift 8167674
  have htrace : WordTrace (prefixWord ++ tailWord_8167674) baseStart_8167674 baseEnd_8167674 := by
    simpa [prefixWord, tailWord_8167674, baseEnd_8167674] using wordTrace_append hprefix tailTrace_8167674
  have hstable : (prefixWord ++ tailWord_8167674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167674).length < 2 ^ (prefixWord ++ tailWord_8167674).sum := by decide
  have hdescent : baseEnd_8167674 < baseStart_8167674 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167682 : List Nat := [3, 4, 1, 1, 2, 3, 2, 2, 1, 1, 3]
def baseStart_8167682 : Nat := 118140960795 + 8167682 * 2 ^ 59
def prefixEnd_8167682 : Nat := 4983230072969 + 3 ^ 40 * 8167682 * 2
def baseEnd_8167682 : Nat := 4193946699076018140312521

theorem tailTrace_8167682 : CollatzResearch.WordTrace tailWord_8167682 prefixEnd_8167682 4193946699076018140312521 := by
  unfold tailWord_8167682
  simp only [CollatzResearch.WordTrace]
  refine ⟨74474958998972629468684325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198599890663927011916491533 74474958998972629468684325)
  ·
    refine ⟨13964054812307368025378311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74474958998972629468684325 13964054812307368025378311)
    ·
      refine ⟨20946082218461052038067467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13964054812307368025378311 20946082218461052038067467)
      ·
        refine ⟨31419123327691578057101201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20946082218461052038067467 31419123327691578057101201)
        ·
          refine ⟨23564342495768683542825901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31419123327691578057101201 23564342495768683542825901)
          ·
            refine ⟨8836628435913256328559713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23564342495768683542825901 8836628435913256328559713)
            ·
              refine ⟨6627471326934942246419785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8836628435913256328559713 6627471326934942246419785)
              ·
                refine ⟨4970603495201206684814839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6627471326934942246419785 4970603495201206684814839)
                ·
                  refine ⟨7455905242801810027222259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4970603495201206684814839 7455905242801810027222259)
                  ·
                    refine ⟨11183857864202715040833389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7455905242801810027222259 11183857864202715040833389)
                    ·
                      refine ⟨4193946699076018140312521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11183857864202715040833389 4193946699076018140312521)
                      ·
                        rfl

theorem cell23_8167682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_8167682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167682 prefixEnd_8167682 := by exact prefixLift 8167682
  have htrace : WordTrace (prefixWord ++ tailWord_8167682) baseStart_8167682 baseEnd_8167682 := by
    simpa [prefixWord, tailWord_8167682, baseEnd_8167682] using wordTrace_append hprefix tailTrace_8167682
  have hstable : (prefixWord ++ tailWord_8167682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167682).length < 2 ^ (prefixWord ++ tailWord_8167682).sum := by decide
  have hdescent : baseEnd_8167682 < baseStart_8167682 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167704 : List Nat := [2, 1, 2, 3, 1, 2, 4, 1, 1, 3, 3]
def baseStart_8167704 : Nat := 118140960795 + 8167704 * 2 ^ 59
def prefixEnd_8167704 : Nat := 4983230072969 + 3 ^ 40 * 8167704 * 2
def baseEnd_8167704 : Nat := 4193957995650417054237419

theorem tailTrace_8167704 : CollatzResearch.WordTrace tailWord_8167704 prefixEnd_8167704 4193957995650417054237419 := by
  unfold tailWord_8167704
  simp only [CollatzResearch.WordTrace]
  refine ⟨148950319200905407816019083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198600425601207210421358777 148950319200905407816019083)
  ·
    refine ⟨223425478801358111724028625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148950319200905407816019083 223425478801358111724028625)
    ·
      refine ⟨167569109101018583793021469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223425478801358111724028625 167569109101018583793021469)
      ·
        refine ⟨62838415912881968922383051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167569109101018583793021469 62838415912881968922383051)
        ·
          refine ⟨94257623869322953383574577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62838415912881968922383051 94257623869322953383574577)
          ·
            refine ⟨70693217901992215037680933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94257623869322953383574577 70693217901992215037680933)
            ·
              refine ⟨13254978356623540319565175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70693217901992215037680933 13254978356623540319565175)
              ·
                refine ⟨19882467534935310479347763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13254978356623540319565175 19882467534935310479347763)
                ·
                  refine ⟨29823701302402965719021645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19882467534935310479347763 29823701302402965719021645)
                  ·
                    refine ⟨11183887988401112144633117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29823701302402965719021645 11183887988401112144633117)
                    ·
                      refine ⟨4193957995650417054237419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11183887988401112144633117 4193957995650417054237419)
                      ·
                        rfl

theorem cell23_8167704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_8167704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167704 prefixEnd_8167704 := by exact prefixLift 8167704
  have htrace : WordTrace (prefixWord ++ tailWord_8167704) baseStart_8167704 baseEnd_8167704 := by
    simpa [prefixWord, tailWord_8167704, baseEnd_8167704] using wordTrace_append hprefix tailTrace_8167704
  have hstable : (prefixWord ++ tailWord_8167704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167704).length < 2 ^ (prefixWord ++ tailWord_8167704).sum := by decide
  have hdescent : baseEnd_8167704 < baseStart_8167704 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167722 : List Nat := [3, 1, 4, 2, 2, 1, 2, 3, 1, 2, 2]
def baseStart_8167722 : Nat := 118140960795 + 8167722 * 2 ^ 59
def prefixEnd_8167722 : Nat := 4983230072969 + 3 ^ 40 * 8167722 * 2
def baseEnd_8167722 : Nat := 4193967238302197983812337

theorem tailTrace_8167722 : CollatzResearch.WordTrace tailWord_8167722 prefixEnd_8167722 4193967238302197983812337 := by
  unfold tailWord_8167722
  simp only [CollatzResearch.WordTrace]
  refine ⟨74475323728936401176548355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198600863277163736470795613 74475323728936401176548355)
  ·
    refine ⟨111712985593404601764822533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74475323728936401176548355 111712985593404601764822533)
    ·
      refine ⟨20946184798763362830904225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111712985593404601764822533 20946184798763362830904225)
      ·
        refine ⟨15709638599072522123178169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20946184798763362830904225 15709638599072522123178169)
        ·
          refine ⟨11782228949304391592383627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15709638599072522123178169 11782228949304391592383627)
          ·
            refine ⟨17673343423956587388575441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11782228949304391592383627 17673343423956587388575441)
            ·
              refine ⟨13255007567967440541431581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17673343423956587388575441 13255007567967440541431581)
              ·
                refine ⟨4970627837987790203036843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13255007567967440541431581 4970627837987790203036843)
                ·
                  refine ⟨7455941756981685304555265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4970627837987790203036843 7455941756981685304555265)
                  ·
                    refine ⟨5591956317736263978416449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7455941756981685304555265 5591956317736263978416449)
                    ·
                      refine ⟨4193967238302197983812337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5591956317736263978416449 4193967238302197983812337)
                      ·
                        rfl

theorem cell23_8167722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_8167722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167722 prefixEnd_8167722 := by exact prefixLift 8167722
  have htrace : WordTrace (prefixWord ++ tailWord_8167722) baseStart_8167722 baseEnd_8167722 := by
    simpa [prefixWord, tailWord_8167722, baseEnd_8167722] using wordTrace_append hprefix tailTrace_8167722
  have hstable : (prefixWord ++ tailWord_8167722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167722).length < 2 ^ (prefixWord ++ tailWord_8167722).sum := by decide
  have hdescent : baseEnd_8167722 < baseStart_8167722 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167731 : List Nat := [1, 1, 1, 2, 5, 1, 3, 3, 1, 3, 2]
def baseStart_8167731 : Nat := 118140960795 + 8167731 * 2 ^ 59
def prefixEnd_8167731 : Nat := 4983230072969 + 3 ^ 40 * 8167731 * 2
def baseEnd_8167731 : Nat := 4193971859628088448599795

theorem tailTrace_8167731 : CollatzResearch.WordTrace tailWord_8167731 prefixEnd_8167731 4193971859628088448599795 := by
  unfold tailWord_8167731
  simp only [CollatzResearch.WordTrace]
  refine ⟨297901623172712999243271047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198601082115141999495514031 297901623172712999243271047)
  ·
    refine ⟨446852434759069498864906571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297901623172712999243271047 446852434759069498864906571)
    ·
      refine ⟨670278652138604248297359857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446852434759069498864906571 670278652138604248297359857)
      ·
        refine ⟨502708989103953186223019893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 670278652138604248297359857 502708989103953186223019893)
        ·
          refine ⟨47128967728495611208408115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 502708989103953186223019893 47128967728495611208408115)
          ·
            refine ⟨70693451592743416812612173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47128967728495611208408115 70693451592743416812612173)
            ·
              refine ⟨26510044347278781304729565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70693451592743416812612173 26510044347278781304729565)
              ·
                refine ⟨9941266630229542989273587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26510044347278781304729565 9941266630229542989273587)
                ·
                  refine ⟨14911899945344314483910381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9941266630229542989273587 14911899945344314483910381)
                  ·
                    refine ⟨5591962479504117931466393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14911899945344314483910381 5591962479504117931466393)
                    ·
                      refine ⟨4193971859628088448599795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5591962479504117931466393 4193971859628088448599795)
                      ·
                        rfl

theorem cell23_8167731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 3, 2].length) (baseStart_8167731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167731 prefixEnd_8167731 := by exact prefixLift 8167731
  have htrace : WordTrace (prefixWord ++ tailWord_8167731) baseStart_8167731 baseEnd_8167731 := by
    simpa [prefixWord, tailWord_8167731, baseEnd_8167731] using wordTrace_append hprefix tailTrace_8167731
  have hstable : (prefixWord ++ tailWord_8167731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167731).length < 2 ^ (prefixWord ++ tailWord_8167731).sum := by decide
  have hdescent : baseEnd_8167731 < baseStart_8167731 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167738 : List Nat := [3, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3]
def baseStart_8167738 : Nat := 118140960795 + 8167738 * 2 ^ 59
def prefixEnd_8167738 : Nat := 4983230072969 + 3 ^ 40 * 8167738 * 2
def baseEnd_8167738 : Nat := 4193975453992669921212263

theorem tailTrace_8167738 : CollatzResearch.WordTrace tailWord_8167738 prefixEnd_8167738 4193975453992669921212263 := by
  unfold tailWord_8167738
  simp only [CollatzResearch.WordTrace]
  refine ⟨74475469620921909859693967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198601252322458426292517245 74475469620921909859693967)
  ·
    refine ⟨111713204431382864789540951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74475469620921909859693967 111713204431382864789540951)
    ·
      refine ⟨167569806647074297184311427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111713204431382864789540951 167569806647074297184311427)
      ·
        refine ⟨251354709970611445776467141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167569806647074297184311427 251354709970611445776467141)
        ·
          refine ⟨47129008119489646083087589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251354709970611445776467141 47129008119489646083087589)
          ·
            refine ⟨8836689022404308640578923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47129008119489646083087589 8836689022404308640578923)
            ·
              refine ⟨13255033533606462960868385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8836689022404308640578923 13255033533606462960868385)
              ·
                refine ⟨9941275150204847220651289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13255033533606462960868385 9941275150204847220651289)
                ·
                  refine ⟨7455956362653635415488467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9941275150204847220651289 7455956362653635415488467)
                  ·
                    refine ⟨11183934543980453123232701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7455956362653635415488467 11183934543980453123232701)
                    ·
                      refine ⟨4193975453992669921212263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11183934543980453123232701 4193975453992669921212263)
                      ·
                        rfl

theorem cell23_8167738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3].length) (baseStart_8167738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167738 prefixEnd_8167738 := by exact prefixLift 8167738
  have htrace : WordTrace (prefixWord ++ tailWord_8167738) baseStart_8167738 baseEnd_8167738 := by
    simpa [prefixWord, tailWord_8167738, baseEnd_8167738] using wordTrace_append hprefix tailTrace_8167738
  have hstable : (prefixWord ++ tailWord_8167738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167738).length < 2 ^ (prefixWord ++ tailWord_8167738).sum := by decide
  have hdescent : baseEnd_8167738 < baseStart_8167738 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167747 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 1, 6, 3]
def baseStart_8167747 : Nat := 118140960795 + 8167747 * 2 ^ 59
def prefixEnd_8167747 : Nat := 4983230072969 + 3 ^ 40 * 8167747 * 2
def baseEnd_8167747 : Nat := 4193980075318560385999721

theorem tailTrace_8167747 : CollatzResearch.WordTrace tailWord_8167747 prefixEnd_8167747 4193980075318560385999721 := by
  unfold tailWord_8167747
  simp only [CollatzResearch.WordTrace]
  refine ⟨297902206740655033975853495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198601471160436689317235663 297902206740655033975853495)
  ·
    refine ⟨446853310110982550963780243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297902206740655033975853495 446853310110982550963780243)
    ·
      refine ⟨670279965166473826445670365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446853310110982550963780243 670279965166473826445670365)
      ·
        refine ⟨251354986937427684917126387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 670279965166473826445670365 251354986937427684917126387)
        ·
          refine ⟨377032480406141527375689581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251354986937427684917126387 377032480406141527375689581)
          ·
            refine ⟨141387180152303072765883593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 377032480406141527375689581 141387180152303072765883593)
            ·
              refine ⟨106040385114227304574412695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141387180152303072765883593 106040385114227304574412695)
              ·
                refine ⟨159060577671340956861619043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106040385114227304574412695 159060577671340956861619043)
                ·
                  refine ⟨238590866507011435292428565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159060577671340956861619043 238590866507011435292428565)
                  ·
                    refine ⟨11183946867516161029332589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 238590866507011435292428565 11183946867516161029332589)
                    ·
                      refine ⟨4193980075318560385999721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11183946867516161029332589 4193980075318560385999721)
                      ·
                        rfl

theorem cell23_8167747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6, 3].length) (baseStart_8167747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167747 prefixEnd_8167747 := by exact prefixLift 8167747
  have htrace : WordTrace (prefixWord ++ tailWord_8167747) baseStart_8167747 baseEnd_8167747 := by
    simpa [prefixWord, tailWord_8167747, baseEnd_8167747] using wordTrace_append hprefix tailTrace_8167747
  have hstable : (prefixWord ++ tailWord_8167747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167747).length < 2 ^ (prefixWord ++ tailWord_8167747).sum := by decide
  have hdescent : baseEnd_8167747 < baseStart_8167747 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167761 : List Nat := [1, 2, 2, 1, 4, 2, 3, 1, 1, 4, 2]
def baseStart_8167761 : Nat := 118140960795 + 8167761 * 2 ^ 59
def prefixEnd_8167761 : Nat := 4983230072969 + 3 ^ 40 * 8167761 * 2
def baseEnd_8167761 : Nat := 4193987264047723331224657

theorem tailTrace_8167761 : CollatzResearch.WordTrace tailWord_8167761 prefixEnd_8167761 4193987264047723331224657 := by
  unfold tailWord_8167761
  simp only [CollatzResearch.WordTrace]
  refine ⟨297902717362604314366863137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198601811575069542911242091 297902717362604314366863137)
  ·
    refine ⟨223427038021953235775147353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297902717362604314366863137 223427038021953235775147353)
    ·
      refine ⟨167570278516464926831360515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223427038021953235775147353 167570278516464926831360515)
      ·
        refine ⟨251355417774697390247040773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167570278516464926831360515 251355417774697390247040773)
        ·
          refine ⟨47129140832755760671320145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251355417774697390247040773 47129140832755760671320145)
          ·
            refine ⟨35346855624566820503490109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47129140832755760671320145 35346855624566820503490109)
            ·
              refine ⟨13255070859212557688808791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35346855624566820503490109 13255070859212557688808791)
              ·
                refine ⟨19882606288818836533213187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13255070859212557688808791 19882606288818836533213187)
                ·
                  refine ⟨29823909433228254799819781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19882606288818836533213187 29823909433228254799819781)
                  ·
                    refine ⟨5591983018730297774966209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29823909433228254799819781 5591983018730297774966209)
                    ·
                      refine ⟨4193987264047723331224657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5591983018730297774966209 4193987264047723331224657)
                      ·
                        rfl

theorem cell23_8167761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 4, 2].length) (baseStart_8167761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167761 prefixEnd_8167761 := by exact prefixLift 8167761
  have htrace : WordTrace (prefixWord ++ tailWord_8167761) baseStart_8167761 baseEnd_8167761 := by
    simpa [prefixWord, tailWord_8167761, baseEnd_8167761] using wordTrace_append hprefix tailTrace_8167761
  have hstable : (prefixWord ++ tailWord_8167761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167761).length < 2 ^ (prefixWord ++ tailWord_8167761).sum := by decide
  have hdescent : baseEnd_8167761 < baseStart_8167761 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167767 : List Nat := [1, 1, 3, 2, 3, 1, 1, 4, 7]
def baseStart_8167767 : Nat := 118140960795 + 8167767 * 2 ^ 59
def prefixEnd_8167767 : Nat := 4983230072969 + 3 ^ 40 * 8167767 * 2
def baseEnd_8167767 : Nat := 465998927214627811972181

theorem tailTrace_8167767 : CollatzResearch.WordTrace tailWord_8167767 prefixEnd_8167767 465998927214627811972181 := by
  unfold tailWord_8167767
  simp only [CollatzResearch.WordTrace]
  refine ⟨297902936200582577391581555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198601957467055051594387703 297902936200582577391581555)
  ·
    refine ⟨446854404300873866087372333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297902936200582577391581555 446854404300873866087372333)
    ·
      refine ⟨167570401612827699782764625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446854404300873866087372333 167570401612827699782764625)
      ·
        refine ⟨125677801209620774837073469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167570401612827699782764625 125677801209620774837073469)
        ·
          refine ⟨47129175453607790563902551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125677801209620774837073469 47129175453607790563902551)
          ·
            refine ⟨70693763180411685845853827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47129175453607790563902551 70693763180411685845853827)
            ·
              refine ⟨106040644770617528768780741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70693763180411685845853827 106040644770617528768780741)
              ·
                refine ⟨19882620894490786644146389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106040644770617528768780741 19882620894490786644146389)
                ·
                  refine ⟨465998927214627811972181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19882620894490786644146389 465998927214627811972181)
                  ·
                    rfl

theorem cell23_8167767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 7].length) (baseStart_8167767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167767 prefixEnd_8167767 := by exact prefixLift 8167767
  have htrace : WordTrace (prefixWord ++ tailWord_8167767) baseStart_8167767 baseEnd_8167767 := by
    simpa [prefixWord, tailWord_8167767, baseEnd_8167767] using wordTrace_append hprefix tailTrace_8167767
  have hstable : (prefixWord ++ tailWord_8167767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167767).length < 2 ^ (prefixWord ++ tailWord_8167767).sum := by decide
  have hdescent : baseEnd_8167767 < baseStart_8167767 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167778 : List Nat := [3, 3, 2, 1, 1, 2, 1, 2, 4, 2, 2]
def baseStart_8167778 : Nat := 118140960795 + 8167778 * 2 ^ 59
def prefixEnd_8167778 : Nat := 4983230072969 + 3 ^ 40 * 8167778 * 2
def baseEnd_8167778 : Nat := 4193995993218849764712079

theorem tailTrace_8167778 : CollatzResearch.WordTrace tailWord_8167778 prefixEnd_8167778 4193995993218849764712079 := by
  unfold tailWord_8167778
  simp only [CollatzResearch.WordTrace]
  refine ⟨74475834350885681567557997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198602224935695150846821325 74475834350885681567557997)
  ·
    refine ⟨27928437881582130587834249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74475834350885681567557997 27928437881582130587834249)
    ·
      refine ⟨20946328411186597940875687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27928437881582130587834249 20946328411186597940875687)
      ·
        refine ⟨31419492616779896911313531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20946328411186597940875687 31419492616779896911313531)
        ·
          refine ⟨47129238925169845366970297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31419492616779896911313531 47129238925169845366970297)
          ·
            refine ⟨35346929193877384025227723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47129238925169845366970297 35346929193877384025227723)
            ·
              refine ⟨53020393790816076037841585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35346929193877384025227723 53020393790816076037841585)
              ·
                refine ⟨39765295343112057028381189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53020393790816076037841585 39765295343112057028381189)
                ·
                  refine ⟨7455992876833510692821473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39765295343112057028381189 7455992876833510692821473)
                  ·
                    refine ⟨5591994657625133019616105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7455992876833510692821473 5591994657625133019616105)
                    ·
                      refine ⟨4193995993218849764712079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5591994657625133019616105 4193995993218849764712079)
                      ·
                        rfl

theorem cell23_8167778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_8167778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167778 prefixEnd_8167778 := by exact prefixLift 8167778
  have htrace : WordTrace (prefixWord ++ tailWord_8167778) baseStart_8167778 baseEnd_8167778 := by
    simpa [prefixWord, tailWord_8167778, baseEnd_8167778] using wordTrace_append hprefix tailTrace_8167778
  have hstable : (prefixWord ++ tailWord_8167778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167778).length < 2 ^ (prefixWord ++ tailWord_8167778).sum := by decide
  have hdescent : baseEnd_8167778 < baseStart_8167778 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167807 : List Nat := [1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 5]
def baseStart_8167807 : Nat := 118140960795 + 8167807 * 2 ^ 59
def prefixEnd_8167807 : Nat := 4983230072969 + 3 ^ 40 * 8167807 * 2
def baseEnd_8167807 : Nat := 4194010884157830151249445

theorem tailTrace_8167807 : CollatzResearch.WordTrace tailWord_8167807 prefixEnd_8167807 4194010884157830151249445 := by
  unfold tailWord_8167807
  simp only [CollatzResearch.WordTrace]
  refine ⟨297904395120437664223037675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198602930080291776148691783 297904395120437664223037675)
  ·
    refine ⟨446856592680656496334556513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297904395120437664223037675 446856592680656496334556513)
    ·
      refine ⟨335142444510492372250917385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446856592680656496334556513 335142444510492372250917385)
      ·
        refine ⟨251356833382869279188188039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335142444510492372250917385 251356833382869279188188039)
        ·
          refine ⟨377035250074303918782282059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251356833382869279188188039 377035250074303918782282059)
          ·
            refine ⟨565552875111455878173423089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377035250074303918782282059 565552875111455878173423089)
            ·
              refine ⟨424164656333591908630067317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 565552875111455878173423089 424164656333591908630067317)
              ·
                refine ⟨39765436531274241434068811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 424164656333591908630067317 39765436531274241434068811)
                ·
                  refine ⟨59648154796911362151103217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39765436531274241434068811 59648154796911362151103217)
                  ·
                    refine ⟨44736116097683521613327413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59648154796911362151103217 44736116097683521613327413)
                    ·
                      refine ⟨4194010884157830151249445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44736116097683521613327413 4194010884157830151249445)
                      ·
                        rfl

theorem cell23_8167807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_8167807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167807 prefixEnd_8167807 := by exact prefixLift 8167807
  have htrace : WordTrace (prefixWord ++ tailWord_8167807) baseStart_8167807 baseEnd_8167807 := by
    simpa [prefixWord, tailWord_8167807, baseEnd_8167807] using wordTrace_append hprefix tailTrace_8167807
  have hstable : (prefixWord ++ tailWord_8167807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167807).length < 2 ^ (prefixWord ++ tailWord_8167807).sum := by decide
  have hdescent : baseEnd_8167807 < baseStart_8167807 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167868 : List Nat := [2, 2, 2, 4, 1, 2, 1, 1, 2, 4, 2]
def baseStart_8167868 : Nat := 118140960795 + 8167868 * 2 ^ 59
def prefixEnd_8167868 : Nat := 4983230072969 + 3 ^ 40 * 8167868 * 2
def baseEnd_8167868 : Nat := 4194042206477754412586665

theorem tailTrace_8167868 : CollatzResearch.WordTrace tailWord_8167868 prefixEnd_8167868 4194042206477754412586665 := by
  unfold tailWord_8167868
  simp only [CollatzResearch.WordTrace]
  refine ⟨148953309986608335820504129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198604413315477781094005505 148953309986608335820504129)
  ·
    refine ⟨111714982489956251865378097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148953309986608335820504129 111714982489956251865378097)
    ·
      refine ⟨83786236867467188899033573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111714982489956251865378097 83786236867467188899033573)
      ·
        refine ⟨15709919412650097918568795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83786236867467188899033573 15709919412650097918568795)
        ·
          refine ⟨23564879118975146877853193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15709919412650097918568795 23564879118975146877853193)
          ·
            refine ⟨17673659339231360158389895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23564879118975146877853193 17673659339231360158389895)
            ·
              refine ⟨26510489008847040237584843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17673659339231360158389895 26510489008847040237584843)
              ·
                refine ⟨39765733513270560356377265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26510489008847040237584843 39765733513270560356377265)
                ·
                  refine ⟨29824300134952920267282949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39765733513270560356377265 29824300134952920267282949)
                  ·
                    refine ⟨5592056275303672550115553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29824300134952920267282949 5592056275303672550115553)
                    ·
                      refine ⟨4194042206477754412586665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5592056275303672550115553 4194042206477754412586665)
                      ·
                        rfl

theorem cell23_8167868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_8167868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167868 prefixEnd_8167868 := by exact prefixLift 8167868
  have htrace : WordTrace (prefixWord ++ tailWord_8167868) baseStart_8167868 baseEnd_8167868 := by
    simpa [prefixWord, tailWord_8167868, baseEnd_8167868] using wordTrace_append hprefix tailTrace_8167868
  have hstable : (prefixWord ++ tailWord_8167868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167868).length < 2 ^ (prefixWord ++ tailWord_8167868).sum := by decide
  have hdescent : baseEnd_8167868 < baseStart_8167868 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167918 : List Nat := [4, 1, 2, 1, 2, 2, 1, 3, 3, 1, 3]
def baseStart_8167918 : Nat := 118140960795 + 8167918 * 2 ^ 59
def prefixEnd_8167918 : Nat := 4983230072969 + 3 ^ 40 * 8167918 * 2
def baseEnd_8167918 : Nat := 4194067880510479216961435

theorem tailTrace_8167918 : CollatzResearch.WordTrace tailWord_8167918 prefixEnd_8167918 4194067880510479216961435 := by
  unfold tailWord_8167918
  simp only [CollatzResearch.WordTrace]
  refine ⟨37238555452879441272541051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198605629082023686786885605 37238555452879441272541051)
  ·
    refine ⟨55857833179319161908811577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37238555452879441272541051 55857833179319161908811577)
    ·
      refine ⟨41893374884489371431608683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55857833179319161908811577 41893374884489371431608683)
      ·
        refine ⟨62840062326734057147413025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41893374884489371431608683 62840062326734057147413025)
        ·
          refine ⟨47130046745050542860559769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62840062326734057147413025 47130046745050542860559769)
          ·
            refine ⟨35347535058787907145419827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47130046745050542860559769 35347535058787907145419827)
            ·
              refine ⟨53021302588181860718129741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35347535058787907145419827 53021302588181860718129741)
              ·
                refine ⟨19882988470568197769298653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53021302588181860718129741 19882988470568197769298653)
                ·
                  refine ⟨7456120676463074163486995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19882988470568197769298653 7456120676463074163486995)
                  ·
                    refine ⟨11184181014694611245230493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7456120676463074163486995 11184181014694611245230493)
                    ·
                      refine ⟨4194067880510479216961435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11184181014694611245230493 4194067880510479216961435)
                      ·
                        rfl

theorem cell23_8167918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_8167918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167918 prefixEnd_8167918 := by exact prefixLift 8167918
  have htrace : WordTrace (prefixWord ++ tailWord_8167918) baseStart_8167918 baseEnd_8167918 := by
    simpa [prefixWord, tailWord_8167918, baseEnd_8167918] using wordTrace_append hprefix tailTrace_8167918
  have hstable : (prefixWord ++ tailWord_8167918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167918).length < 2 ^ (prefixWord ++ tailWord_8167918).sum := by decide
  have hdescent : baseEnd_8167918 < baseStart_8167918 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167925 : List Nat := [1, 3, 5, 1, 2, 1, 3, 1, 6]
def baseStart_8167925 : Nat := 118140960795 + 8167925 * 2 ^ 59
def prefixEnd_8167925 : Nat := 4983230072969 + 3 ^ 40 * 8167925 * 2
def baseEnd_8167925 : Nat := 466007941652784521063767

theorem tailTrace_8167925 : CollatzResearch.WordTrace tailWord_8167925 prefixEnd_8167925 466007941652784521063767 := by
  unfold tailWord_8167925
  simp only [CollatzResearch.WordTrace]
  refine ⟨297908698934010170375833229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198605799289340113583888819 297908698934010170375833229)
  ·
    refine ⟨111715762100253813890937461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297908698934010170375833229 111715762100253813890937461)
    ·
      refine ⟨10473352696898795052275387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111715762100253813890937461 10473352696898795052275387)
      ·
        refine ⟨15710029045348192578413081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10473352696898795052275387 15710029045348192578413081)
        ·
          refine ⟨11782521784011144433809811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15710029045348192578413081 11782521784011144433809811)
          ·
            refine ⟨17673782676016716650714717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11782521784011144433809811 17673782676016716650714717)
            ·
              refine ⟨6627668503506268744018019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17673782676016716650714717 6627668503506268744018019)
              ·
                refine ⟨9941502755259403116027029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6627668503506268744018019 9941502755259403116027029)
                ·
                  refine ⟨466007941652784521063767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9941502755259403116027029 466007941652784521063767)
                  ·
                    rfl

theorem cell23_8167925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 6].length) (baseStart_8167925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167925 prefixEnd_8167925 := by exact prefixLift 8167925
  have htrace : WordTrace (prefixWord ++ tailWord_8167925) baseStart_8167925 baseEnd_8167925 := by
    simpa [prefixWord, tailWord_8167925, baseEnd_8167925] using wordTrace_append hprefix tailTrace_8167925
  have hstable : (prefixWord ++ tailWord_8167925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167925).length < 2 ^ (prefixWord ++ tailWord_8167925).sum := by decide
  have hdescent : baseEnd_8167925 < baseStart_8167925 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167941 : List Nat := [1, 3, 1, 1, 2, 2, 3, 4, 1, 1, 4]
def baseStart_8167941 : Nat := 118140960795 + 8167941 * 2 ^ 59
def prefixEnd_8167941 : Nat := 4983230072969 + 3 ^ 40 * 8167941 * 2
def baseEnd_8167941 : Nat := 4194079690565532626973829

theorem tailTrace_8167941 : CollatzResearch.WordTrace tailWord_8167941 prefixEnd_8167941 4194079690565532626973829 := by
  unfold tailWord_8167941
  simp only [CollatzResearch.WordTrace]
  refine ⟨297909282501952205108415677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198606188334634803405610451 297909282501952205108415677)
  ·
    refine ⟨111715980938232076915655879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297909282501952205108415677 111715980938232076915655879)
    ·
      refine ⟨167573971407348115373483819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111715980938232076915655879 167573971407348115373483819)
      ·
        refine ⟨251360957111022173060225729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167573971407348115373483819 251360957111022173060225729)
        ·
          refine ⟨188520717833266629795169297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251360957111022173060225729 188520717833266629795169297)
          ·
            refine ⟨141390538374949972346376973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188520717833266629795169297 141390538374949972346376973)
            ·
              refine ⟨53021451890606239629891365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141390538374949972346376973 53021451890606239629891365)
              ·
                refine ⟨9941522229488669930604631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53021451890606239629891365 9941522229488669930604631)
                ·
                  refine ⟨14912283344233004895906947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9941522229488669930604631 14912283344233004895906947)
                  ·
                    refine ⟨22368425016349507343860421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14912283344233004895906947 22368425016349507343860421)
                    ·
                      refine ⟨4194079690565532626973829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22368425016349507343860421 4194079690565532626973829)
                      ·
                        rfl

theorem cell23_8167941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 1, 4].length) (baseStart_8167941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167941 prefixEnd_8167941 := by exact prefixLift 8167941
  have htrace : WordTrace (prefixWord ++ tailWord_8167941) baseStart_8167941 baseEnd_8167941 := by
    simpa [prefixWord, tailWord_8167941, baseEnd_8167941] using wordTrace_append hprefix tailTrace_8167941
  have hstable : (prefixWord ++ tailWord_8167941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167941).length < 2 ^ (prefixWord ++ tailWord_8167941).sum := by decide
  have hdescent : baseEnd_8167941 < baseStart_8167941 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167944 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 5, 1, 5]
def baseStart_8167944 : Nat := 118140960795 + 8167944 * 2 ^ 59
def prefixEnd_8167944 : Nat := 4983230072969 + 3 ^ 40 * 8167944 * 2
def baseEnd_8167944 : Nat := 4194081231007496115236315

theorem tailTrace_8167944 : CollatzResearch.WordTrace tailWord_8167944 prefixEnd_8167944 4194081231007496115236315 := by
  unfold tailWord_8167944
  simp only [CollatzResearch.WordTrace]
  refine ⟨148954695960470668310387443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198606261280627557747183257 148954695960470668310387443)
  ·
    refine ⟨223432043940706002465581165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148954695960470668310387443 223432043940706002465581165)
    ·
      refine ⟨83787016477764750924592937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223432043940706002465581165 83787016477764750924592937)
      ·
        refine ⟨62840262358323563193444703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83787016477764750924592937 62840262358323563193444703)
        ·
          refine ⟨94260393537485344790167055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62840262358323563193444703 94260393537485344790167055)
          ·
            refine ⟨141390590306228017185250583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94260393537485344790167055 141390590306228017185250583)
            ·
              refine ⟨212085885459342025777875875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141390590306228017185250583 212085885459342025777875875)
              ·
                refine ⟨318128828189013038666813813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212085885459342025777875875 318128828189013038666813813)
                ·
                  refine ⟨29824577642719972375013795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 318128828189013038666813813 29824577642719972375013795)
                  ·
                    refine ⟨44736866464079958562520693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29824577642719972375013795 44736866464079958562520693)
                    ·
                      refine ⟨4194081231007496115236315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44736866464079958562520693 4194081231007496115236315)
                      ·
                        rfl

theorem cell23_8167944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_8167944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167944 prefixEnd_8167944 := by exact prefixLift 8167944
  have htrace : WordTrace (prefixWord ++ tailWord_8167944) baseStart_8167944 baseEnd_8167944 := by
    simpa [prefixWord, tailWord_8167944, baseEnd_8167944] using wordTrace_append hprefix tailTrace_8167944
  have hstable : (prefixWord ++ tailWord_8167944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167944).length < 2 ^ (prefixWord ++ tailWord_8167944).sum := by decide
  have hdescent : baseEnd_8167944 < baseStart_8167944 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
