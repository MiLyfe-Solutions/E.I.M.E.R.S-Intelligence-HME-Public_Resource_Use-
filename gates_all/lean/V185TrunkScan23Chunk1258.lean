import V185TrunkScan23Chunk1257

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7450943 : List Nat := [1, 1, 2, 2, 4, 1, 1, 4, 3, 2, 2]
def baseStart_7450943 : Nat := 118140960795 + 7450943 * 2 ^ 59
def prefixEnd_7450943 : Nat := 4983230072969 + 3 ^ 40 * 7450943 * 2
def baseEnd_7450943 : Nat := 3825915088253146884946243

theorem tailTrace_7450943 : CollatzResearch.WordTrace tailWord_7450943 prefixEnd_7450943 3825915088253146884946243 := by
  unfold tailWord_7450943
  simp only [CollatzResearch.WordTrace]
  refine ⟨271758217045513505599037483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181172144697009003732691655 271758217045513505599037483)
  ·
    refine ⟨407637325568270258398556225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271758217045513505599037483 407637325568270258398556225)
    ·
      refine ⟨305727994176202693798917169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407637325568270258398556225 305727994176202693798917169)
      ·
        refine ⟨229295995632152020349187877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305727994176202693798917169 229295995632152020349187877)
        ·
          refine ⟨42992999181028503815472727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229295995632152020349187877 42992999181028503815472727)
          ·
            refine ⟨64489498771542755723209091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42992999181028503815472727 64489498771542755723209091)
            ·
              refine ⟨96734248157314133584813637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64489498771542755723209091 96734248157314133584813637)
              ·
                refine ⟨18137671529496400047152557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96734248157314133584813637 18137671529496400047152557)
                ·
                  refine ⟨6801626823561150017682209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18137671529496400047152557 6801626823561150017682209)
                  ·
                    refine ⟨5101220117670862513261657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6801626823561150017682209 5101220117670862513261657)
                    ·
                      refine ⟨3825915088253146884946243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5101220117670862513261657 3825915088253146884946243)
                      ·
                        rfl

theorem cell23_7450943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3, 2, 2].length) (baseStart_7450943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450943 prefixEnd_7450943 := by exact prefixLift 7450943
  have htrace : WordTrace (prefixWord ++ tailWord_7450943) baseStart_7450943 baseEnd_7450943 := by
    simpa [prefixWord, tailWord_7450943, baseEnd_7450943] using wordTrace_append hprefix tailTrace_7450943
  have hstable : (prefixWord ++ tailWord_7450943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450943).length < 2 ^ (prefixWord ++ tailWord_7450943).sum := by decide
  have hdescent : baseEnd_7450943 < baseStart_7450943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450979 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 2, 7]
def baseStart_7450979 : Nat := 118140960795 + 7450979 * 2 ^ 59
def prefixEnd_7450979 : Nat := 4983230072969 + 3 ^ 40 * 7450979 * 2
def baseEnd_7450979 : Nat := 1275311191185569581365359

theorem tailTrace_7450979 : CollatzResearch.WordTrace tailWord_7450979 prefixEnd_7450979 1275311191185569581365359 := by
  unfold tailWord_7450979
  simp only [CollatzResearch.WordTrace]
  refine ⟨271759530073383083747347991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181173020048922055831565327 271759530073383083747347991)
  ·
    refine ⟨407639295110074625621021987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271759530073383083747347991 407639295110074625621021987)
    ·
      refine ⟨611458942665111938431532981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407639295110074625621021987 611458942665111938431532981)
      ·
        refine ⟨57324275874854244227956217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 611458942665111938431532981 57324275874854244227956217)
        ·
          refine ⟨42993206906140683170967163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57324275874854244227956217 42993206906140683170967163)
          ·
            refine ⟨64489810359211024756450745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42993206906140683170967163 64489810359211024756450745)
            ·
              refine ⟨48367357769408268567338059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64489810359211024756450745 48367357769408268567338059)
              ·
                refine ⟨72551036654112402851007089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48367357769408268567338059 72551036654112402851007089)
                ·
                  refine ⟨54413277490584302138255317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72551036654112402851007089 54413277490584302138255317)
                  ·
                    refine ⟨1275311191185569581365359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54413277490584302138255317 1275311191185569581365359)
                    ·
                      rfl

theorem cell23_7450979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 7].length) (baseStart_7450979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450979 prefixEnd_7450979 := by exact prefixLift 7450979
  have htrace : WordTrace (prefixWord ++ tailWord_7450979) baseStart_7450979 baseEnd_7450979 := by
    simpa [prefixWord, tailWord_7450979, baseEnd_7450979] using wordTrace_append hprefix tailTrace_7450979
  have hstable : (prefixWord ++ tailWord_7450979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450979).length < 2 ^ (prefixWord ++ tailWord_7450979).sum := by decide
  have hdescent : baseEnd_7450979 < baseStart_7450979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450999 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 4]
def baseStart_7450999 : Nat := 118140960795 + 7450999 * 2 ^ 59
def prefixEnd_7450999 : Nat := 4983230072969 + 3 ^ 40 * 7450999 * 2
def baseEnd_7450999 : Nat := 3825943843169798665845985

theorem tailTrace_7450999 : CollatzResearch.WordTrace tailWord_7450999 prefixEnd_7450999 3825943843169798665845985 := by
  unfold tailWord_7450999
  simp only [CollatzResearch.WordTrace]
  refine ⟨271760259533310627163076051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181173506355540418108717367 271760259533310627163076051)
  ·
    refine ⟨407640389299965940744614077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271760259533310627163076051 407640389299965940744614077)
    ·
      refine ⟨152865145987487227779230279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407640389299965940744614077 152865145987487227779230279)
      ·
        refine ⟨229297718981230841668845419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152865145987487227779230279 229297718981230841668845419)
        ·
          refine ⟨343946578471846262503268129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229297718981230841668845419 343946578471846262503268129)
          ·
            refine ⟨257959933853884696877451097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343946578471846262503268129 257959933853884696877451097)
            ·
              refine ⟨193469950390413522658088323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257959933853884696877451097 193469950390413522658088323)
              ·
                refine ⟨290204925585620283987132485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193469950390413522658088323 290204925585620283987132485)
                ·
                  refine ⟨54413423547303803247587341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 290204925585620283987132485 54413423547303803247587341)
                  ·
                    refine ⟨20405033830238926217845253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54413423547303803247587341 20405033830238926217845253)
                    ·
                      refine ⟨3825943843169798665845985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20405033830238926217845253 3825943843169798665845985)
                      ·
                        rfl

theorem cell23_7450999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_7450999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450999 prefixEnd_7450999 := by exact prefixLift 7450999
  have htrace : WordTrace (prefixWord ++ tailWord_7450999) baseStart_7450999 baseEnd_7450999 := by
    simpa [prefixWord, tailWord_7450999, baseEnd_7450999] using wordTrace_append hprefix tailTrace_7450999
  have hstable : (prefixWord ++ tailWord_7450999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450999).length < 2 ^ (prefixWord ++ tailWord_7450999).sum := by decide
  have hdescent : baseEnd_7450999 < baseStart_7450999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451003 : List Nat := [1, 1, 1, 1, 1, 8, 1, 1, 3, 3, 2]
def baseStart_7451003 : Nat := 118140960795 + 7451003 * 2 ^ 59
def prefixEnd_7451003 : Nat := 4983230072969 + 3 ^ 40 * 7451003 * 2
def baseEnd_7451003 : Nat := 3825945897092416650195967

theorem tailTrace_7451003 : CollatzResearch.WordTrace tailWord_7451003 prefixEnd_7451003 3825945897092416650195967 := by
  unfold tailWord_7451003
  simp only [CollatzResearch.WordTrace]
  refine ⟨271760405425296135846221663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181173603616864090564147775 271760405425296135846221663)
  ·
    refine ⟨407640608137944203769332495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271760405425296135846221663 407640608137944203769332495)
    ·
      refine ⟨611460912206916305653998743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407640608137944203769332495 611460912206916305653998743)
      ·
        refine ⟨917191368310374458480998115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611460912206916305653998743 917191368310374458480998115)
        ·
          refine ⟨1375787052465561687721497173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 917191368310374458480998115 1375787052465561687721497173)
          ·
            refine ⟨16122504521080801027986295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1375787052465561687721497173 16122504521080801027986295)
            ·
              refine ⟨24183756781621201541979443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16122504521080801027986295 24183756781621201541979443)
              ·
                refine ⟨36275635172431802312969165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24183756781621201541979443 36275635172431802312969165)
                ·
                  refine ⟨13603363189661925867363437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36275635172431802312969165 13603363189661925867363437)
                  ·
                    refine ⟨5101261196123222200261289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13603363189661925867363437 5101261196123222200261289)
                    ·
                      refine ⟨3825945897092416650195967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5101261196123222200261289 3825945897092416650195967)
                      ·
                        rfl

theorem cell23_7451003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 3, 2].length) (baseStart_7451003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451003 prefixEnd_7451003 := by exact prefixLift 7451003
  have htrace : WordTrace (prefixWord ++ tailWord_7451003) baseStart_7451003 baseEnd_7451003 := by
    simpa [prefixWord, tailWord_7451003, baseEnd_7451003] using wordTrace_append hprefix tailTrace_7451003
  have hstable : (prefixWord ++ tailWord_7451003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451003).length < 2 ^ (prefixWord ++ tailWord_7451003).sum := by decide
  have hdescent : baseEnd_7451003 < baseStart_7451003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451028 : List Nat := [2, 4, 2, 1, 4, 1, 2, 2, 1, 2, 2]
def baseStart_7451028 : Nat := 118140960795 + 7451028 * 2 ^ 59
def prefixEnd_7451028 : Nat := 4983230072969 + 3 ^ 40 * 7451028 * 2
def baseEnd_7451028 : Nat := 3825958734108779052383353

theorem tailTrace_7451028 : CollatzResearch.WordTrace tailWord_7451028 prefixEnd_7451028 3825958734108779052383353 := by
  unfold tailWord_7451028
  simp only [CollatzResearch.WordTrace]
  refine ⟨135880658625102782557940869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181174211500137043410587825 135880658625102782557940869)
  ·
    refine ⟨25477623492206771729613913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135880658625102782557940869 25477623492206771729613913)
    ·
      refine ⟨19108217619155078797210435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25477623492206771729613913 19108217619155078797210435)
      ·
        refine ⟨28662326428732618195815653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19108217619155078797210435 28662326428732618195815653)
        ·
          refine ⟨5374186205387365911715435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28662326428732618195815653 5374186205387365911715435)
          ·
            refine ⟨8061279308081048867573153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5374186205387365911715435 8061279308081048867573153)
            ·
              refine ⟨6045959481060786650679865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8061279308081048867573153 6045959481060786650679865)
              ·
                refine ⟨4534469610795589988009899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6045959481060786650679865 4534469610795589988009899)
                ·
                  refine ⟨6801704416193384982014849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4534469610795589988009899 6801704416193384982014849)
                  ·
                    refine ⟨5101278312145038736511137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6801704416193384982014849 5101278312145038736511137)
                    ·
                      refine ⟨3825958734108779052383353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5101278312145038736511137 3825958734108779052383353)
                      ·
                        rfl

theorem cell23_7451028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_7451028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451028 prefixEnd_7451028 := by exact prefixLift 7451028
  have htrace : WordTrace (prefixWord ++ tailWord_7451028) baseStart_7451028 baseEnd_7451028 := by
    simpa [prefixWord, tailWord_7451028, baseEnd_7451028] using wordTrace_append hprefix tailTrace_7451028
  have hstable : (prefixWord ++ tailWord_7451028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451028).length < 2 ^ (prefixWord ++ tailWord_7451028).sum := by decide
  have hdescent : baseEnd_7451028 < baseStart_7451028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451029 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 2, 3, 6]
def baseStart_7451029 : Nat := 118140960795 + 7451029 * 2 ^ 59
def prefixEnd_7451029 : Nat := 4983230072969 + 3 ^ 40 * 7451029 * 2
def baseEnd_7451029 : Nat := 3825959247589433548470847

theorem tailTrace_7451029 : CollatzResearch.WordTrace tailWord_7451029 prefixEnd_7451029 3825959247589433548470847 := by
  unfold tailWord_7451029
  simp only [CollatzResearch.WordTrace]
  refine ⟨271761353723201942286668141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181174235815467961524445427 271761353723201942286668141)
  ·
    refine ⟨101910507646200728357500553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271761353723201942286668141 101910507646200728357500553)
    ·
      refine ⟨76432880734650546268125415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101910507646200728357500553 76432880734650546268125415)
      ·
        refine ⟨114649321101975819402188123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76432880734650546268125415 114649321101975819402188123)
        ·
          refine ⟨171973981652963729103282185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114649321101975819402188123 171973981652963729103282185)
          ·
            refine ⟨128980486239722796827461639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171973981652963729103282185 128980486239722796827461639)
            ·
              refine ⟨193470729359584195241192459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128980486239722796827461639 193470729359584195241192459)
              ·
                refine ⟨290206094039376292861788689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193470729359584195241192459 290206094039376292861788689)
                ·
                  refine ⟨217654570529532219646341517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 290206094039376292861788689 217654570529532219646341517)
                  ·
                    refine ⟨81620463948574582367378069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 217654570529532219646341517 81620463948574582367378069)
                    ·
                      refine ⟨3825959247589433548470847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81620463948574582367378069 3825959247589433548470847)
                      ·
                        rfl

theorem cell23_7451029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_7451029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451029 prefixEnd_7451029 := by exact prefixLift 7451029
  have htrace : WordTrace (prefixWord ++ tailWord_7451029) baseStart_7451029 baseEnd_7451029 := by
    simpa [prefixWord, tailWord_7451029, baseEnd_7451029] using wordTrace_append hprefix tailTrace_7451029
  have hstable : (prefixWord ++ tailWord_7451029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451029).length < 2 ^ (prefixWord ++ tailWord_7451029).sum := by decide
  have hdescent : baseEnd_7451029 < baseStart_7451029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451084 : List Nat := [2, 2, 1, 4, 3, 2, 1, 2, 2, 2, 2]
def baseStart_7451084 : Nat := 118140960795 + 7451084 * 2 ^ 59
def prefixEnd_7451084 : Nat := 4983230072969 + 3 ^ 40 * 7451084 * 2
def baseEnd_7451084 : Nat := 3825987489025430833283095

theorem tailTrace_7451084 : CollatzResearch.WordTrace tailWord_7451084 prefixEnd_7451084 3825987489025430833283095 := by
  unfold tailWord_7451084
  simp only [CollatzResearch.WordTrace]
  refine ⟨135881679869001343339960153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181175573158668457786613537 135881679869001343339960153)
  ·
    refine ⟨101911259901751007504970115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135881679869001343339960153 101911259901751007504970115)
    ·
      refine ⟨152866889852626511257455173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101911259901751007504970115 152866889852626511257455173)
      ·
        refine ⟨28662541847367470860772845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152866889852626511257455173 28662541847367470860772845)
        ·
          refine ⟨10748453192762801572789817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28662541847367470860772845 10748453192762801572789817)
          ·
            refine ⟨8061339894572101179592363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10748453192762801572789817 8061339894572101179592363)
            ·
              refine ⟨12092009841858151769388545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8061339894572101179592363 12092009841858151769388545)
              ·
                refine ⟨9069007381393613827041409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12092009841858151769388545 9069007381393613827041409)
                ·
                  refine ⟨6801755536045210370281057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9069007381393613827041409 6801755536045210370281057)
                  ·
                    refine ⟨5101316652033907777710793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6801755536045210370281057 5101316652033907777710793)
                    ·
                      refine ⟨3825987489025430833283095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5101316652033907777710793 3825987489025430833283095)
                      ·
                        rfl

theorem cell23_7451084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_7451084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451084 prefixEnd_7451084 := by exact prefixLift 7451084
  have htrace : WordTrace (prefixWord ++ tailWord_7451084) baseStart_7451084 baseEnd_7451084 := by
    simpa [prefixWord, tailWord_7451084, baseEnd_7451084] using wordTrace_append hprefix tailTrace_7451084
  have hstable : (prefixWord ++ tailWord_7451084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451084).length < 2 ^ (prefixWord ++ tailWord_7451084).sum := by decide
  have hdescent : baseEnd_7451084 < baseStart_7451084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451086 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 4, 5]
def baseStart_7451086 : Nat := 118140960795 + 7451086 * 2 ^ 59
def prefixEnd_7451086 : Nat := 4983230072969 + 3 ^ 40 * 7451086 * 2
def baseEnd_7451086 : Nat := 1275329505328913275152695

theorem tailTrace_7451086 : CollatzResearch.WordTrace tailWord_7451086 prefixEnd_7451086 1275329505328913275152695 := by
  unfold tailWord_7451086
  simp only [CollatzResearch.WordTrace]
  refine ⟨33970429085499430127686639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181175621789330294014328741 33970429085499430127686639)
  ·
    refine ⟨50955643628249145191529959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33970429085499430127686639 50955643628249145191529959)
    ·
      refine ⟨76433465442373717787294939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50955643628249145191529959 76433465442373717787294939)
      ·
        refine ⟨114650198163560576680942409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76433465442373717787294939 114650198163560576680942409)
        ·
          refine ⟨85987648622670432510706807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114650198163560576680942409 85987648622670432510706807)
          ·
            refine ⟨128981472934005648766060211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85987648622670432510706807 128981472934005648766060211)
            ·
              refine ⟨193472209401008473149090317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128981472934005648766060211 193472209401008473149090317)
              ·
                refine ⟨72552078525378177430908869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193472209401008473149090317 72552078525378177430908869)
                ·
                  refine ⟨13603514723508408268295413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72552078525378177430908869 13603514723508408268295413)
                  ·
                    refine ⟨1275329505328913275152695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13603514723508408268295413 1275329505328913275152695)
                    ·
                      rfl

theorem cell23_7451086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_7451086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451086 prefixEnd_7451086 := by exact prefixLift 7451086
  have htrace : WordTrace (prefixWord ++ tailWord_7451086) baseStart_7451086 baseEnd_7451086 := by
    simpa [prefixWord, tailWord_7451086, baseEnd_7451086] using wordTrace_append hprefix tailTrace_7451086
  have hstable : (prefixWord ++ tailWord_7451086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451086).length < 2 ^ (prefixWord ++ tailWord_7451086).sum := by decide
  have hdescent : baseEnd_7451086 < baseStart_7451086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451090 : List Nat := [3, 2, 2, 4, 1, 1, 2, 1, 7]
def baseStart_7451090 : Nat := 118140960795 + 7451090 * 2 ^ 59
def prefixEnd_7451090 : Nat := 4983230072969 + 3 ^ 40 * 7451090 * 2
def baseEnd_7451090 : Nat := 425110063323261978867563

theorem tailTrace_7451090 : CollatzResearch.WordTrace tailWord_7451090 prefixEnd_7451090 425110063323261978867563 := by
  unfold tailWord_7451090
  simp only [CollatzResearch.WordTrace]
  refine ⟨67940894643995237426159681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181175719050653966469759149 67940894643995237426159681)
  ·
    refine ⟨50955670982996428069619761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67940894643995237426159681 50955670982996428069619761)
    ·
      refine ⟨38216753237247321052214821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50955670982996428069619761 38216753237247321052214821)
      ·
        refine ⟨7165641231983872697290279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38216753237247321052214821 7165641231983872697290279)
        ·
          refine ⟨10748461847975809045935419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7165641231983872697290279 10748461847975809045935419)
          ·
            refine ⟨16122692771963713568903129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10748461847975809045935419 16122692771963713568903129)
            ·
              refine ⟨12092019578972785176677347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16122692771963713568903129 12092019578972785176677347)
              ·
                refine ⟨18138029368459177765016021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12092019578972785176677347 18138029368459177765016021)
                ·
                  refine ⟨425110063323261978867563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18138029368459177765016021 425110063323261978867563)
                  ·
                    rfl

theorem cell23_7451090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 7].length) (baseStart_7451090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451090 prefixEnd_7451090 := by exact prefixLift 7451090
  have htrace : WordTrace (prefixWord ++ tailWord_7451090) baseStart_7451090 baseEnd_7451090 := by
    simpa [prefixWord, tailWord_7451090, baseEnd_7451090] using wordTrace_append hprefix tailTrace_7451090
  have hstable : (prefixWord ++ tailWord_7451090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451090).length < 2 ^ (prefixWord ++ tailWord_7451090).sum := by decide
  have hdescent : baseEnd_7451090 < baseStart_7451090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451140 : List Nat := [2, 3, 2, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_7451140 : Nat := 118140960795 + 7451140 * 2 ^ 59
def prefixEnd_7451140 : Nat := 4983230072969 + 3 ^ 40 * 7451140 * 2
def baseEnd_7451140 : Nat := 3826016243942082614182837

theorem tailTrace_7451140 : CollatzResearch.WordTrace tailWord_7451140 prefixEnd_7451140 3826016243942082614182837 := by
  unfold tailWord_7451140
  simp only [CollatzResearch.WordTrace]
  refine ⟨135882701112899904121979437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181176934817199872162639249 135882701112899904121979437)
  ·
    refine ⟨50956012917337464045742289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135882701112899904121979437 50956012917337464045742289)
    ·
      refine ⟨38217009688003098034306717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50956012917337464045742289 38217009688003098034306717)
      ·
        refine ⟨14331378633001161762865019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38217009688003098034306717 14331378633001161762865019)
        ·
          refine ⟨21497067949501742644297529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14331378633001161762865019 21497067949501742644297529)
          ·
            refine ⟨16122800962126306983223147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21497067949501742644297529 16122800962126306983223147)
            ·
              refine ⟨24184201443189460474834721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16122800962126306983223147 24184201443189460474834721)
              ·
                refine ⟨18138151082392095356126041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24184201443189460474834721 18138151082392095356126041)
                ·
                  refine ⟨13603613311794071517094531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18138151082392095356126041 13603613311794071517094531)
                  ·
                    refine ⟨20405419967691107275641797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13603613311794071517094531 20405419967691107275641797)
                    ·
                      refine ⟨3826016243942082614182837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20405419967691107275641797 3826016243942082614182837)
                      ·
                        rfl

theorem cell23_7451140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_7451140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451140 prefixEnd_7451140 := by exact prefixLift 7451140
  have htrace : WordTrace (prefixWord ++ tailWord_7451140) baseStart_7451140 baseEnd_7451140 := by
    simpa [prefixWord, tailWord_7451140, baseEnd_7451140] using wordTrace_append hprefix tailTrace_7451140
  have hstable : (prefixWord ++ tailWord_7451140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451140).length < 2 ^ (prefixWord ++ tailWord_7451140).sum := by decide
  have hdescent : baseEnd_7451140 < baseStart_7451140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451146 : List Nat := [3, 1, 2, 2, 2, 1, 1, 3, 8]
def baseStart_7451146 : Nat := 118140960795 + 7451146 * 2 ^ 59
def prefixEnd_7451146 : Nat := 4983230072969 + 3 ^ 40 * 7451146 * 2
def baseEnd_7451146 : Nat := 425113258314001065634201

theorem tailTrace_7451146 : CollatzResearch.WordTrace tailWord_7451146 prefixEnd_7451146 425113258314001065634201 := by
  unfold tailWord_7451146
  simp only [CollatzResearch.WordTrace]
  refine ⟨67941405265944517817169323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181177080709185380845784861 67941405265944517817169323)
  ·
    refine ⟨101912107898916776725753985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67941405265944517817169323 101912107898916776725753985)
    ·
      refine ⟨76434080924187582544315489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101912107898916776725753985 76434080924187582544315489)
      ·
        refine ⟨57325560693140686908236617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76434080924187582544315489 57325560693140686908236617)
        ·
          refine ⟨42994170519855515181177463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57325560693140686908236617 42994170519855515181177463)
          ·
            refine ⟨64491255779783272771766195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42994170519855515181177463 64491255779783272771766195)
            ·
              refine ⟨96736883669674909157649293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64491255779783272771766195 96736883669674909157649293)
              ·
                refine ⟨36276331376128090934118485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96736883669674909157649293 36276331376128090934118485)
                ·
                  refine ⟨425113258314001065634201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36276331376128090934118485 425113258314001065634201)
                  ·
                    rfl

theorem cell23_7451146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 8].length) (baseStart_7451146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451146 prefixEnd_7451146 := by exact prefixLift 7451146
  have htrace : WordTrace (prefixWord ++ tailWord_7451146) baseStart_7451146 baseEnd_7451146 := by
    simpa [prefixWord, tailWord_7451146, baseEnd_7451146] using wordTrace_append hprefix tailTrace_7451146
  have hstable : (prefixWord ++ tailWord_7451146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451146).length < 2 ^ (prefixWord ++ tailWord_7451146).sum := by decide
  have hdescent : baseEnd_7451146 < baseStart_7451146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451150 : List Nat := [4, 1, 1, 2, 3, 1, 3, 1, 3, 4]
def baseStart_7451150 : Nat := 118140960795 + 7451150 * 2 ^ 59
def prefixEnd_7451150 : Nat := 4983230072969 + 3 ^ 40 * 7451150 * 2
def baseEnd_7451150 : Nat := 1275340459582875858352597

theorem tailTrace_7451150 : CollatzResearch.WordTrace tailWord_7451150 prefixEnd_7451150 1275340459582875858352597 := by
  unfold tailWord_7451150
  simp only [CollatzResearch.WordTrace]
  refine ⟨33970720869470447493977863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181177177970509053301215269 33970720869470447493977863)
  ·
    refine ⟨50956081304205671240966795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33970720869470447493977863 50956081304205671240966795)
    ·
      refine ⟨76434121956308506861450193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50956081304205671240966795 76434121956308506861450193)
      ·
        refine ⟨57325591467231380146087645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76434121956308506861450193 57325591467231380146087645)
        ·
          refine ⟨21497096800211767554782867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57325591467231380146087645 21497096800211767554782867)
          ·
            refine ⟨32245645200317651332174301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21497096800211767554782867 32245645200317651332174301)
            ·
              refine ⟨12092116950119119249565363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32245645200317651332174301 12092116950119119249565363)
              ·
                refine ⟨18138175425178678874348045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12092116950119119249565363 18138175425178678874348045)
                ·
                  refine ⟨6801815784442004577880517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18138175425178678874348045 6801815784442004577880517)
                  ·
                    refine ⟨1275340459582875858352597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6801815784442004577880517 1275340459582875858352597)
                    ·
                      rfl

theorem cell23_7451150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_7451150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451150 prefixEnd_7451150 := by exact prefixLift 7451150
  have htrace : WordTrace (prefixWord ++ tailWord_7451150) baseStart_7451150 baseEnd_7451150 := by
    simpa [prefixWord, tailWord_7451150, baseEnd_7451150] using wordTrace_append hprefix tailTrace_7451150
  have hstable : (prefixWord ++ tailWord_7451150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451150).length < 2 ^ (prefixWord ++ tailWord_7451150).sum := by decide
  have hdescent : baseEnd_7451150 < baseStart_7451150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451200 : List Nat := [2, 1, 1, 2, 2, 2, 4, 2, 2, 3, 2]
def baseStart_7451200 : Nat := 118140960795 + 7451200 * 2 ^ 59
def prefixEnd_7451200 : Nat := 4983230072969 + 3 ^ 40 * 7451200 * 2
def baseEnd_7451200 : Nat := 3826047052781352379432561

theorem tailTrace_7451200 : CollatzResearch.WordTrace tailWord_7451200 prefixEnd_7451200 3826047052781352379432561 := by
  unfold tailWord_7451200
  simp only [CollatzResearch.WordTrace]
  refine ⟨135883795302791219245571527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181178393737054958994095369 135883795302791219245571527)
  ·
    refine ⟨203825692954186828868357291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135883795302791219245571527 203825692954186828868357291)
    ·
      refine ⟨305738539431280243302535937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203825692954186828868357291 305738539431280243302535937)
      ·
        refine ⟨229303904573460182476901953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305738539431280243302535937 229303904573460182476901953)
        ·
          refine ⟨171977928430095136857676465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229303904573460182476901953 171977928430095136857676465)
          ·
            refine ⟨128983446322571352643257349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171977928430095136857676465 128983446322571352643257349)
            ·
              refine ⟨24184396185482128620610753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128983446322571352643257349 24184396185482128620610753)
              ·
                refine ⟨18138297139111596465458065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24184396185482128620610753 18138297139111596465458065)
                ·
                  refine ⟨13603722854333697349093549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18138297139111596465458065 13603722854333697349093549)
                  ·
                    refine ⟨5101396070375136505910081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13603722854333697349093549 5101396070375136505910081)
                    ·
                      refine ⟨3826047052781352379432561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5101396070375136505910081 3826047052781352379432561)
                      ·
                        rfl

theorem cell23_7451200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 2, 3, 2].length) (baseStart_7451200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451200 prefixEnd_7451200 := by exact prefixLift 7451200
  have htrace : WordTrace (prefixWord ++ tailWord_7451200) baseStart_7451200 baseEnd_7451200 := by
    simpa [prefixWord, tailWord_7451200, baseEnd_7451200] using wordTrace_append hprefix tailTrace_7451200
  have hstable : (prefixWord ++ tailWord_7451200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451200).length < 2 ^ (prefixWord ++ tailWord_7451200).sum := by decide
  have hdescent : baseEnd_7451200 < baseStart_7451200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451223 : List Nat := [1, 1, 3, 2, 2, 2, 4, 1, 1, 6]
def baseStart_7451223 : Nat := 118140960795 + 7451223 * 2 ^ 59
def prefixEnd_7451223 : Nat := 4983230072969 + 3 ^ 40 * 7451223 * 2
def baseEnd_7451223 : Nat := 1275352954278801929814985

theorem tailTrace_7451223 : CollatzResearch.WordTrace tailWord_7451223 prefixEnd_7451223 1275352954278801929814985 := by
  unfold tailWord_7451223
  simp only [CollatzResearch.WordTrace]
  refine ⟨271768429484499113419230323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181178952989666075612820215 271768429484499113419230323)
  ·
    refine ⟨407652644226748670128845485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271768429484499113419230323 407652644226748670128845485)
    ·
      refine ⟨152869741585030751298317057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407652644226748670128845485 152869741585030751298317057)
      ·
        refine ⟨114652306188773063473737793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152869741585030751298317057 114652306188773063473737793)
        ·
          refine ⟨85989229641579797605303345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114652306188773063473737793 85989229641579797605303345)
          ·
            refine ⟨64491922231184848203977509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85989229641579797605303345 64491922231184848203977509)
            ·
              refine ⟨12092235418347159038245783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64491922231184848203977509 12092235418347159038245783)
              ·
                refine ⟨18138353127520738557368675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12092235418347159038245783 18138353127520738557368675)
                ·
                  refine ⟨27207529691281107836053013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18138353127520738557368675 27207529691281107836053013)
                  ·
                    refine ⟨1275352954278801929814985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27207529691281107836053013 1275352954278801929814985)
                    ·
                      rfl

theorem cell23_7451223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 6].length) (baseStart_7451223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451223 prefixEnd_7451223 := by exact prefixLift 7451223
  have htrace : WordTrace (prefixWord ++ tailWord_7451223) baseStart_7451223 baseEnd_7451223 := by
    simpa [prefixWord, tailWord_7451223, baseEnd_7451223] using wordTrace_append hprefix tailTrace_7451223
  have hstable : (prefixWord ++ tailWord_7451223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451223).length < 2 ^ (prefixWord ++ tailWord_7451223).sum := by decide
  have hdescent : baseEnd_7451223 < baseStart_7451223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451234 : List Nat := [3, 3, 2, 3, 1, 1, 1, 1, 1, 5, 2]
def baseStart_7451234 : Nat := 118140960795 + 7451234 * 2 ^ 59
def prefixEnd_7451234 : Nat := 4983230072969 + 3 ^ 40 * 7451234 * 2
def baseEnd_7451234 : Nat := 3826064511123605246407405

theorem tailTrace_7451234 : CollatzResearch.WordTrace tailWord_7451234 prefixEnd_7451234 3826064511123605246407405 := by
  unfold tailWord_7451234
  simp only [CollatzResearch.WordTrace]
  refine ⟨67942207671864815574470189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181179220458306174865253837 67942207671864815574470189)
  ·
    refine ⟨25478327876949305840426321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67942207671864815574470189 25478327876949305840426321)
    ·
      refine ⟨19108745907711979380319741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25478327876949305840426321 19108745907711979380319741)
      ·
        refine ⟨7165779715391992267619903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19108745907711979380319741 7165779715391992267619903)
        ·
          refine ⟨10748669573087988401429855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7165779715391992267619903 10748669573087988401429855)
          ·
            refine ⟨16123004359631982602144783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10748669573087988401429855 16123004359631982602144783)
            ·
              refine ⟨24184506539447973903217175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16123004359631982602144783 24184506539447973903217175)
              ·
                refine ⟨36276759809171960854825763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24184506539447973903217175 36276759809171960854825763)
                ·
                  refine ⟨54415139713757941282238645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36276759809171960854825763 54415139713757941282238645)
                  ·
                    refine ⟨5101419348164806995209873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54415139713757941282238645 5101419348164806995209873)
                    ·
                      refine ⟨3826064511123605246407405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5101419348164806995209873 3826064511123605246407405)
                      ·
                        rfl

theorem cell23_7451234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_7451234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451234 prefixEnd_7451234 := by exact prefixLift 7451234
  have htrace : WordTrace (prefixWord ++ tailWord_7451234) baseStart_7451234 baseEnd_7451234 := by
    simpa [prefixWord, tailWord_7451234, baseEnd_7451234] using wordTrace_append hprefix tailTrace_7451234
  have hstable : (prefixWord ++ tailWord_7451234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451234).length < 2 ^ (prefixWord ++ tailWord_7451234).sum := by decide
  have hdescent : baseEnd_7451234 < baseStart_7451234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451257 : List Nat := [1, 2, 1, 3, 3, 4, 1, 2, 2, 4]
def baseStart_7451257 : Nat := 118140960795 + 7451257 * 2 ^ 59
def prefixEnd_7451257 : Nat := 4983230072969 + 3 ^ 40 * 7451257 * 2
def baseEnd_7451257 : Nat := 1275358773726219552139933

theorem tailTrace_7451257 : CollatzResearch.WordTrace tailWord_7451257 prefixEnd_7451257 1275358773726219552139933 := by
  unfold tailWord_7451257
  simp only [CollatzResearch.WordTrace]
  refine ⟨271769669566375937225968025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181179779710917291483978683 271769669566375937225968025)
  ·
    refine ⟨203827252174781952919476019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271769669566375937225968025 203827252174781952919476019)
    ·
      refine ⟨305740878262172929379214029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203827252174781952919476019 305740878262172929379214029)
      ·
        refine ⟨114652829348314848517205261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305740878262172929379214029 114652829348314848517205261)
        ·
          refine ⟨42994811005618068193951973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114652829348314848517205261 42994811005618068193951973)
          ·
            refine ⟨8061527063553387786365995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42994811005618068193951973 8061527063553387786365995)
            ·
              refine ⟨12092290595330081679548993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8061527063553387786365995 12092290595330081679548993)
              ·
                refine ⟨9069217946497561259661745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12092290595330081679548993 9069217946497561259661745)
                ·
                  refine ⟨6801913459873170944746309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9069217946497561259661745 6801913459873170944746309)
                  ·
                    refine ⟨1275358773726219552139933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6801913459873170944746309 1275358773726219552139933)
                    ·
                      rfl

theorem cell23_7451257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2, 4].length) (baseStart_7451257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451257 prefixEnd_7451257 := by exact prefixLift 7451257
  have htrace : WordTrace (prefixWord ++ tailWord_7451257) baseStart_7451257 baseEnd_7451257 := by
    simpa [prefixWord, tailWord_7451257, baseEnd_7451257] using wordTrace_append hprefix tailTrace_7451257
  have hstable : (prefixWord ++ tailWord_7451257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451257).length < 2 ^ (prefixWord ++ tailWord_7451257).sum := by decide
  have hdescent : baseEnd_7451257 < baseStart_7451257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451264 : List Nat := [2, 1, 1, 2, 1, 5, 2, 4, 1, 2, 2]
def baseStart_7451264 : Nat := 118140960795 + 7451264 * 2 ^ 59
def prefixEnd_7451264 : Nat := 4983230072969 + 3 ^ 40 * 7451264 * 2
def baseEnd_7451264 : Nat := 3826079915543240129032267

theorem tailTrace_7451264 : CollatzResearch.WordTrace tailWord_7451264 prefixEnd_7451264 3826079915543240129032267 := by
  unfold tailWord_7451264
  simp only [CollatzResearch.WordTrace]
  refine ⟨135884962438675288710736423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181179949918233718280981897 135884962438675288710736423)
  ·
    refine ⟨203827443658012933066104635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135884962438675288710736423 203827443658012933066104635)
    ·
      refine ⟨305741165487019399599156953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203827443658012933066104635 305741165487019399599156953)
      ·
        refine ⟨229305874115264549699367715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305741165487019399599156953 229305874115264549699367715)
        ·
          refine ⟨343958811172896824549051573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229305874115264549699367715 343958811172896824549051573)
          ·
            refine ⟨32246138547459077301473585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 343958811172896824549051573 32246138547459077301473585)
            ·
              refine ⟨24184603910594307976105189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32246138547459077301473585 24184603910594307976105189)
              ·
                refine ⟨4534613233236432745519723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24184603910594307976105189 4534613233236432745519723)
                ·
                  refine ⟨6801919849854649118279585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4534613233236432745519723 6801919849854649118279585)
                  ·
                    refine ⟨5101439887390986838709689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6801919849854649118279585 5101439887390986838709689)
                    ·
                      refine ⟨3826079915543240129032267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5101439887390986838709689 3826079915543240129032267)
                      ·
                        rfl

theorem cell23_7451264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4, 1, 2, 2].length) (baseStart_7451264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451264 prefixEnd_7451264 := by exact prefixLift 7451264
  have htrace : WordTrace (prefixWord ++ tailWord_7451264) baseStart_7451264 baseEnd_7451264 := by
    simpa [prefixWord, tailWord_7451264, baseEnd_7451264] using wordTrace_append hprefix tailTrace_7451264
  have hstable : (prefixWord ++ tailWord_7451264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451264).length < 2 ^ (prefixWord ++ tailWord_7451264).sum := by decide
  have hdescent : baseEnd_7451264 < baseStart_7451264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451274 : List Nat := [3, 1, 2, 3, 3, 1, 3, 1, 2, 4]
def baseStart_7451274 : Nat := 118140960795 + 7451274 * 2 ^ 59
def prefixEnd_7451274 : Nat := 4983230072969 + 3 ^ 40 * 7451274 * 2
def baseEnd_7451274 : Nat := 1275361683449928363302407

theorem tailTrace_7451274 : CollatzResearch.WordTrace tailWord_7451274 prefixEnd_7451274 1275361683449928363302407 := by
  unfold tailWord_7451274
  simp only [CollatzResearch.WordTrace]
  refine ⟨67942572401828587282334219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181180193071542899419557917 67942572401828587282334219)
  ·
    refine ⟨101913858602742880923501329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67942572401828587282334219 101913858602742880923501329)
    ·
      refine ⟨76435393952057160692625997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101913858602742880923501329 76435393952057160692625997)
      ·
        refine ⟨28663272732021435259734749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76435393952057160692625997 28663272732021435259734749)
        ·
          refine ⟨10748727274508038222400531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28663272732021435259734749 10748727274508038222400531)
          ·
            refine ⟨16123090911762057333600797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10748727274508038222400531 16123090911762057333600797)
            ·
              refine ⟨6046159091910771500100299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16123090911762057333600797 6046159091910771500100299)
              ·
                refine ⟨9069238637866157250150449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6046159091910771500100299 9069238637866157250150449)
                ·
                  refine ⟨6801928978399617937612837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9069238637866157250150449 6801928978399617937612837)
                  ·
                    refine ⟨1275361683449928363302407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6801928978399617937612837 1275361683449928363302407)
                    ·
                      rfl

theorem cell23_7451274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_7451274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451274 prefixEnd_7451274 := by exact prefixLift 7451274
  have htrace : WordTrace (prefixWord ++ tailWord_7451274) baseStart_7451274 baseEnd_7451274 := by
    simpa [prefixWord, tailWord_7451274, baseEnd_7451274] using wordTrace_append hprefix tailTrace_7451274
  have hstable : (prefixWord ++ tailWord_7451274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451274).length < 2 ^ (prefixWord ++ tailWord_7451274).sum := by decide
  have hdescent : baseEnd_7451274 < baseStart_7451274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451284 : List Nat := [2, 4, 2, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_7451284 : Nat := 118140960795 + 7451284 * 2 ^ 59
def prefixEnd_7451284 : Nat := 4983230072969 + 3 ^ 40 * 7451284 * 2
def baseEnd_7451284 : Nat := 3826090185156330050782175

theorem tailTrace_7451284 : CollatzResearch.WordTrace tailWord_7451284 prefixEnd_7451284 3826090185156330050782175 := by
  unfold tailWord_7451284
  simp only [CollatzResearch.WordTrace]
  refine ⟨135885327168639060418600453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181180436224852080558133937 135885327168639060418600453)
  ·
    refine ⟨25478498844119823828487585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135885327168639060418600453 25478498844119823828487585)
    ·
      refine ⟨19108874133089867871365689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25478498844119823828487585 19108874133089867871365689)
      ·
        refine ⟨14331655599817400903524267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19108874133089867871365689 14331655599817400903524267)
        ·
          refine ⟨21497483399726101355286401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14331655599817400903524267 21497483399726101355286401)
          ·
            refine ⟨16123112549794576016464801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21497483399726101355286401 16123112549794576016464801)
            ·
              refine ⟨12092334412345932012348601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16123112549794576016464801 12092334412345932012348601)
              ·
                refine ⟨9069250809259449009261451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12092334412345932012348601 9069250809259449009261451)
                ·
                  refine ⟨13603876213889173513892177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9069250809259449009261451 13603876213889173513892177)
                  ·
                    refine ⟨10202907160416880135419133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13603876213889173513892177 10202907160416880135419133)
                    ·
                      refine ⟨3826090185156330050782175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10202907160416880135419133 3826090185156330050782175)
                      ·
                        rfl

theorem cell23_7451284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_7451284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451284 prefixEnd_7451284 := by exact prefixLift 7451284
  have htrace : WordTrace (prefixWord ++ tailWord_7451284) baseStart_7451284 baseEnd_7451284 := by
    simpa [prefixWord, tailWord_7451284, baseEnd_7451284] using wordTrace_append hprefix tailTrace_7451284
  have hstable : (prefixWord ++ tailWord_7451284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451284).length < 2 ^ (prefixWord ++ tailWord_7451284).sum := by decide
  have hdescent : baseEnd_7451284 < baseStart_7451284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451293 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_7451293 : Nat := 118140960795 + 7451293 * 2 ^ 59
def prefixEnd_7451293 : Nat := 4983230072969 + 3 ^ 40 * 7451293 * 2
def baseEnd_7451293 : Nat := 3826094806482220515569633

theorem tailTrace_7451293 : CollatzResearch.WordTrace tailWord_7451293 prefixEnd_7451293 3826094806482220515569633 := by
  unfold tailWord_7451293
  simp only [CollatzResearch.WordTrace]
  refine ⟨271770982594245515374278533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181180655062830343582852355 271770982594245515374278533)
  ·
    refine ⟨50957059236421034132677225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271770982594245515374278533 50957059236421034132677225)
    ·
      refine ⟨38217794427315775599507919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50957059236421034132677225 38217794427315775599507919)
      ·
        refine ⟨57326691640973663399261879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38217794427315775599507919 57326691640973663399261879)
        ·
          refine ⟨85990037461460495098892819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57326691640973663399261879 85990037461460495098892819)
          ·
            refine ⟨128985056192190742648339229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85990037461460495098892819 128985056192190742648339229)
            ·
              refine ⟨48369396072071528493127211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128985056192190742648339229 48369396072071528493127211)
              ·
                refine ⟨72554094108107292739690817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48369396072071528493127211 72554094108107292739690817)
                ·
                  refine ⟨54415570581080469554768113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72554094108107292739690817 54415570581080469554768113)
                  ·
                    refine ⟨40811677935810352166076085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54415570581080469554768113 40811677935810352166076085)
                    ·
                      refine ⟨3826094806482220515569633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40811677935810352166076085 3826094806482220515569633)
                      ·
                        rfl

theorem cell23_7451293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_7451293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451293 prefixEnd_7451293 := by exact prefixLift 7451293
  have htrace : WordTrace (prefixWord ++ tailWord_7451293) baseStart_7451293 baseEnd_7451293 := by
    simpa [prefixWord, tailWord_7451293, baseEnd_7451293] using wordTrace_append hprefix tailTrace_7451293
  have hstable : (prefixWord ++ tailWord_7451293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451293).length < 2 ^ (prefixWord ++ tailWord_7451293).sum := by decide
  have hdescent : baseEnd_7451293 < baseStart_7451293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451340 : List Nat := [2, 2, 1, 5, 1, 1, 1, 2, 2, 1, 5]
def baseStart_7451340 : Nat := 118140960795 + 7451340 * 2 ^ 59
def prefixEnd_7451340 : Nat := 4983230072969 + 3 ^ 40 * 7451340 * 2
def baseEnd_7451340 : Nat := 3826118940072981831681917

theorem tailTrace_7451340 : CollatzResearch.WordTrace tailWord_7451340 prefixEnd_7451340 3826118940072981831681917 := by
  unfold tailWord_7451340
  simp only [CollatzResearch.WordTrace]
  refine ⟨135886348412537621200619737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181181797883383494934159649 135886348412537621200619737)
  ·
    refine ⟨101914761309403215900464803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135886348412537621200619737 101914761309403215900464803)
    ·
      refine ⟨152872141964104823850697205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101914761309403215900464803 152872141964104823850697205)
      ·
        refine ⟨14331763309134827236002863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152872141964104823850697205 14331763309134827236002863)
        ·
          refine ⟨21497644963702240854004295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14331763309134827236002863 21497644963702240854004295)
          ·
            refine ⟨32246467445553361281006443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21497644963702240854004295 32246467445553361281006443)
            ·
              refine ⟨48369701168330041921509665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32246467445553361281006443 48369701168330041921509665)
              ·
                refine ⟨36277275876247531441132249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48369701168330041921509665 36277275876247531441132249)
                ·
                  refine ⟨27207956907185648580849187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36277275876247531441132249 27207956907185648580849187)
                  ·
                    refine ⟨40811935360778472871273781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27207956907185648580849187 40811935360778472871273781)
                    ·
                      refine ⟨3826118940072981831681917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40811935360778472871273781 3826118940072981831681917)
                      ·
                        rfl

theorem cell23_7451340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_7451340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451340 prefixEnd_7451340 := by exact prefixLift 7451340
  have htrace : WordTrace (prefixWord ++ tailWord_7451340) baseStart_7451340 baseEnd_7451340 := by
    simpa [prefixWord, tailWord_7451340, baseEnd_7451340] using wordTrace_append hprefix tailTrace_7451340
  have hstable : (prefixWord ++ tailWord_7451340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451340).length < 2 ^ (prefixWord ++ tailWord_7451340).sum := by decide
  have hdescent : baseEnd_7451340 < baseStart_7451340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451341 : List Nat := [1, 6, 2, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_7451341 : Nat := 118140960795 + 7451341 * 2 ^ 59
def prefixEnd_7451341 : Nat := 4983230072969 + 3 ^ 40 * 7451341 * 2
def baseEnd_7451341 : Nat := 3826119453553636327769413

theorem tailTrace_7451341 : CollatzResearch.WordTrace tailWord_7451341 prefixEnd_7451341 3826119453553636327769413 := by
  unfold tailWord_7451341
  simp only [CollatzResearch.WordTrace]
  refine ⟨271772733298071619572025877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181181822198714413048017251 271772733298071619572025877)
  ·
    refine ⟨12739346873347107167438713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 271772733298071619572025877 12739346873347107167438713)
    ·
      refine ⟨9554510155010330375579035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12739346873347107167438713 9554510155010330375579035)
      ·
        refine ⟨14331765232515495563368553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9554510155010330375579035 14331765232515495563368553)
        ·
          refine ⟨10748823924386621672526415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14331765232515495563368553 10748823924386621672526415)
          ·
            refine ⟨16123235886579932508789623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10748823924386621672526415 16123235886579932508789623)
            ·
              refine ⟨24184853829869898763184435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16123235886579932508789623 24184853829869898763184435)
              ·
                refine ⟨36277280744804848144776653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24184853829869898763184435 36277280744804848144776653)
                ·
                  refine ⟨13603980279301818054291245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36277280744804848144776653 13603980279301818054291245)
                  ·
                    refine ⟨5101492604738181770359217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13603980279301818054291245 5101492604738181770359217)
                    ·
                      refine ⟨3826119453553636327769413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5101492604738181770359217 3826119453553636327769413)
                      ·
                        rfl

theorem cell23_7451341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_7451341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451341 prefixEnd_7451341 := by exact prefixLift 7451341
  have htrace : WordTrace (prefixWord ++ tailWord_7451341) baseStart_7451341 baseEnd_7451341 := by
    simpa [prefixWord, tailWord_7451341, baseEnd_7451341] using wordTrace_append hprefix tailTrace_7451341
  have hstable : (prefixWord ++ tailWord_7451341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451341).length < 2 ^ (prefixWord ++ tailWord_7451341).sum := by decide
  have hdescent : baseEnd_7451341 < baseStart_7451341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451360 : List Nat := [2, 1, 1, 3, 1, 2, 1, 7, 5]
def baseStart_7451360 : Nat := 118140960795 + 7451360 * 2 ^ 59
def prefixEnd_7451360 : Nat := 4983230072969 + 3 ^ 40 * 7451360 * 2
def baseEnd_7451360 : Nat := 425125467742896861492425

theorem tailTrace_7451360 : CollatzResearch.WordTrace tailWord_7451360 prefixEnd_7451360 425125467742896861492425 := by
  unfold tailWord_7451360
  simp only [CollatzResearch.WordTrace]
  refine ⟨135886713142501392908483767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181182284190001857211311689 135886713142501392908483767)
  ·
    refine ⟨203830069713752089362725651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135886713142501392908483767 203830069713752089362725651)
    ·
      refine ⟨305745104570628134044088477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203830069713752089362725651 305745104570628134044088477)
      ·
        refine ⟨114654414213985550266533179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305745104570628134044088477 114654414213985550266533179)
        ·
          refine ⟨171981621320978325399799769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114654414213985550266533179 171981621320978325399799769)
          ·
            refine ⟨128986215990733744049849827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171981621320978325399799769 128986215990733744049849827)
            ·
              refine ⟨193479323986100616074774741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128986215990733744049849827 193479323986100616074774741)
              ·
                refine ⟨4534671655924233189252533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 193479323986100616074774741 4534671655924233189252533)
                ·
                  refine ⟨425125467742896861492425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4534671655924233189252533 425125467742896861492425)
                  ·
                    rfl

theorem cell23_7451360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7, 5].length) (baseStart_7451360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451360 prefixEnd_7451360 := by exact prefixLift 7451360
  have htrace : WordTrace (prefixWord ++ tailWord_7451360) baseStart_7451360 baseEnd_7451360 := by
    simpa [prefixWord, tailWord_7451360, baseEnd_7451360] using wordTrace_append hprefix tailTrace_7451360
  have hstable : (prefixWord ++ tailWord_7451360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451360).length < 2 ^ (prefixWord ++ tailWord_7451360).sum := by decide
  have hdescent : baseEnd_7451360 < baseStart_7451360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451370 : List Nat := [3, 1, 3, 1, 1, 1, 1, 4, 2, 3, 3]
def baseStart_7451370 : Nat := 118140960795 + 7451370 * 2 ^ 59
def prefixEnd_7451370 : Nat := 4983230072969 + 3 ^ 40 * 7451370 * 2
def baseEnd_7451370 : Nat := 3826134344492616714306779

theorem tailTrace_7451370 : CollatzResearch.WordTrace tailWord_7451370 prefixEnd_7451370 3826134344492616714306779 := by
  unfold tailWord_7451370
  simp only [CollatzResearch.WordTrace]
  refine ⟨67943447753741639381207891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181182527343311038349887709 67943447753741639381207891)
  ·
    refine ⟨101915171630612459071811837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67943447753741639381207891 101915171630612459071811837)
    ·
      refine ⟨38218189361479672151929439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101915171630612459071811837 38218189361479672151929439)
      ·
        refine ⟨57327284042219508227894159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38218189361479672151929439 57327284042219508227894159)
        ·
          refine ⟨85990926063329262341841239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57327284042219508227894159 85990926063329262341841239)
          ·
            refine ⟨128986389094993893512761859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85990926063329262341841239 128986389094993893512761859)
            ·
              refine ⟨193479583642490840269142789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128986389094993893512761859 193479583642490840269142789)
              ·
                refine ⟨36277421932967032550464273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193479583642490840269142789 36277421932967032550464273)
                ·
                  refine ⟨27208066449725274412848205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36277421932967032550464273 27208066449725274412848205)
                  ·
                    refine ⟨10203024918646977904818077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27208066449725274412848205 10203024918646977904818077)
                    ·
                      refine ⟨3826134344492616714306779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10203024918646977904818077 3826134344492616714306779)
                      ·
                        rfl

theorem cell23_7451370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_7451370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451370 prefixEnd_7451370 := by exact prefixLift 7451370
  have htrace : WordTrace (prefixWord ++ tailWord_7451370) baseStart_7451370 baseEnd_7451370 := by
    simpa [prefixWord, tailWord_7451370, baseEnd_7451370] using wordTrace_append hprefix tailTrace_7451370
  have hstable : (prefixWord ++ tailWord_7451370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451370).length < 2 ^ (prefixWord ++ tailWord_7451370).sum := by decide
  have hdescent : baseEnd_7451370 < baseStart_7451370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451433 : List Nat := [1, 2, 1, 1, 1, 1, 1, 7, 8]
def baseStart_7451433 : Nat := 118140960795 + 7451433 * 2 ^ 59
def prefixEnd_7451433 : Nat := 4983230072969 + 3 ^ 40 * 7451433 * 2
def baseEnd_7451433 : Nat := 425129632641538885313221

theorem tailTrace_7451433 : CollatzResearch.WordTrace tailWord_7451433 prefixEnd_7451433 425129632641538885313221 := by
  unfold tailWord_7451433
  simp only [CollatzResearch.WordTrace]
  refine ⟨271776088813738319284374953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181184059209158879522916635 271776088813738319284374953)
  ·
    refine ⟨203832066610303739463281215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271776088813738319284374953 203832066610303739463281215)
    ·
      refine ⟨305748099915455609194921823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203832066610303739463281215 305748099915455609194921823)
      ·
        refine ⟨458622149873183413792382735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305748099915455609194921823 458622149873183413792382735)
        ·
          refine ⟨687933224809775120688574103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458622149873183413792382735 687933224809775120688574103)
          ·
            refine ⟨1031899837214662681032861155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687933224809775120688574103 1031899837214662681032861155)
            ·
              refine ⟨1547849755821994021549291733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1031899837214662681032861155 1547849755821994021549291733)
              ·
                refine ⟨36277728652077984880061525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1547849755821994021549291733 36277728652077984880061525)
                ·
                  refine ⟨425129632641538885313221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36277728652077984880061525 425129632641538885313221)
                  ·
                    rfl

theorem cell23_7451433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 8].length) (baseStart_7451433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451433 prefixEnd_7451433 := by exact prefixLift 7451433
  have htrace : WordTrace (prefixWord ++ tailWord_7451433) baseStart_7451433 baseEnd_7451433 := by
    simpa [prefixWord, tailWord_7451433, baseEnd_7451433] using wordTrace_append hprefix tailTrace_7451433
  have hstable : (prefixWord ++ tailWord_7451433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451433).length < 2 ^ (prefixWord ++ tailWord_7451433).sum := by decide
  have hdescent : baseEnd_7451433 < baseStart_7451433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451517 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 2, 6, 2]
def baseStart_7451517 : Nat := 118140960795 + 7451517 * 2 ^ 59
def prefixEnd_7451517 : Nat := 4983230072969 + 3 ^ 40 * 7451517 * 2
def baseEnd_7451517 : Nat := 3826209826148827639168603

theorem tailTrace_7451517 : CollatzResearch.WordTrace tailWord_7451517 prefixEnd_7451517 3826209826148827639168603 := by
  unfold tailWord_7451517
  simp only [CollatzResearch.WordTrace]
  refine ⟨271779152545434001630432805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181186101696956001086955203 271779152545434001630432805)
  ·
    refine ⟨50958591102268875305706151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271779152545434001630432805 50958591102268875305706151)
    ·
      refine ⟨76437886653403312958559227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50958591102268875305706151 76437886653403312958559227)
      ·
        refine ⟨114656829980104969437838841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76437886653403312958559227 114656829980104969437838841)
        ·
          refine ⟨85992622485078727078379131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114656829980104969437838841 85992622485078727078379131)
          ·
            refine ⟨128988933727618090617568697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85992622485078727078379131 128988933727618090617568697)
            ·
              refine ⟨96741700295713567963176523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128988933727618090617568697 96741700295713567963176523)
              ·
                refine ⟨145112550443570351944764785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96741700295713567963176523 145112550443570351944764785)
                ·
                  refine ⟨108834412832677763958573589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145112550443570351944764785 108834412832677763958573589)
                  ·
                    refine ⟨5101613101531770185558137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108834412832677763958573589 5101613101531770185558137)
                    ·
                      refine ⟨3826209826148827639168603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5101613101531770185558137 3826209826148827639168603)
                      ·
                        rfl

theorem cell23_7451517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 6, 2].length) (baseStart_7451517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451517 prefixEnd_7451517 := by exact prefixLift 7451517
  have htrace : WordTrace (prefixWord ++ tailWord_7451517) baseStart_7451517 baseEnd_7451517 := by
    simpa [prefixWord, tailWord_7451517, baseEnd_7451517] using wordTrace_append hprefix tailTrace_7451517
  have hstable : (prefixWord ++ tailWord_7451517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451517).length < 2 ^ (prefixWord ++ tailWord_7451517).sum := by decide
  have hdescent : baseEnd_7451517 < baseStart_7451517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451527 : List Nat := [1, 1, 4, 2, 3, 2, 1, 2, 1, 6]
def baseStart_7451527 : Nat := 118140960795 + 7451527 * 2 ^ 59
def prefixEnd_7451527 : Nat := 4983230072969 + 3 ^ 40 * 7451527 * 2
def baseEnd_7451527 : Nat := 1275404986985124200014519

theorem tailTrace_7451527 : CollatzResearch.WordTrace tailWord_7451527 prefixEnd_7451527 1275404986985124200014519 := by
  unfold tailWord_7451527
  simp only [CollatzResearch.WordTrace]
  refine ⟨271779517275397773338296835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181186344850265182225531223 271779517275397773338296835)
  ·
    refine ⟨407669275913096660007445253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271779517275397773338296835 407669275913096660007445253)
    ·
      refine ⟨76437989233705623751395985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 407669275913096660007445253 76437989233705623751395985)
      ·
        refine ⟨57328491925279217813546989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76437989233705623751395985 57328491925279217813546989)
        ·
          refine ⟨21498184471979706680080121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57328491925279217813546989 21498184471979706680080121)
          ·
            refine ⟨16123638353984780010060091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21498184471979706680080121 16123638353984780010060091)
            ·
              refine ⟨24185457530977170015090137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16123638353984780010060091 24185457530977170015090137)
              ·
                refine ⟨18139093148232877511317603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24185457530977170015090137 18139093148232877511317603)
                ·
                  refine ⟨27208639722349316266976405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18139093148232877511317603 27208639722349316266976405)
                  ·
                    refine ⟨1275404986985124200014519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27208639722349316266976405 1275404986985124200014519)
                    ·
                      rfl

theorem cell23_7451527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_7451527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451527 prefixEnd_7451527 := by exact prefixLift 7451527
  have htrace : WordTrace (prefixWord ++ tailWord_7451527) baseStart_7451527 baseEnd_7451527 := by
    simpa [prefixWord, tailWord_7451527, baseEnd_7451527] using wordTrace_append hprefix tailTrace_7451527
  have hstable : (prefixWord ++ tailWord_7451527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451527).length < 2 ^ (prefixWord ++ tailWord_7451527).sum := by decide
  have hdescent : baseEnd_7451527 < baseStart_7451527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451554 : List Nat := [3, 3, 1, 2, 2, 1, 1, 2, 3, 2, 3]
def baseStart_7451554 : Nat := 118140960795 + 7451554 * 2 ^ 59
def prefixEnd_7451554 : Nat := 4983230072969 + 3 ^ 40 * 7451554 * 2
def baseEnd_7451554 : Nat := 3826228824933043994405933

theorem tailTrace_7451554 : CollatzResearch.WordTrace tailWord_7451554 prefixEnd_7451554 3826228824933043994405933 := by
  unfold tailWord_7451554
  simp only [CollatzResearch.WordTrace]
  refine ⟨67945125511574989237382429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181187001364199971299686477 67945125511574989237382429)
  ·
    refine ⟨25479422066840620964018411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67945125511574989237382429 25479422066840620964018411)
    ·
      refine ⟨38219133100260931446027617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25479422066840620964018411 38219133100260931446027617)
      ·
        refine ⟨28664349825195698584520713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38219133100260931446027617 28664349825195698584520713)
        ·
          refine ⟨21498262368896773938390535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28664349825195698584520713 21498262368896773938390535)
          ·
            refine ⟨32247393553345160907585803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21498262368896773938390535 32247393553345160907585803)
            ·
              refine ⟨48371090330017741361378705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32247393553345160907585803 48371090330017741361378705)
              ·
                refine ⟨36278317747513306021034029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48371090330017741361378705 36278317747513306021034029)
                ·
                  refine ⟨13604369155317489757887761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36278317747513306021034029 13604369155317489757887761)
                  ·
                    refine ⟨10203276866488117318415821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13604369155317489757887761 10203276866488117318415821)
                    ·
                      refine ⟨3826228824933043994405933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10203276866488117318415821 3826228824933043994405933)
                      ·
                        rfl

theorem cell23_7451554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_7451554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451554 prefixEnd_7451554 := by exact prefixLift 7451554
  have htrace : WordTrace (prefixWord ++ tailWord_7451554) baseStart_7451554 baseEnd_7451554 := by
    simpa [prefixWord, tailWord_7451554, baseEnd_7451554] using wordTrace_append hprefix tailTrace_7451554
  have hstable : (prefixWord ++ tailWord_7451554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451554).length < 2 ^ (prefixWord ++ tailWord_7451554).sum := by decide
  have hdescent : baseEnd_7451554 < baseStart_7451554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451588 : List Nat := [2, 3, 3, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_7451588 : Nat := 118140960795 + 7451588 * 2 ^ 59
def prefixEnd_7451588 : Nat := 4983230072969 + 3 ^ 40 * 7451588 * 2
def baseEnd_7451588 : Nat := 3826246283275296861380777

theorem tailTrace_7451588 : CollatzResearch.WordTrace tailWord_7451588 prefixEnd_7451588 3826246283275296861380777 := by
  unfold tailWord_7451588
  simp only [CollatzResearch.WordTrace]
  refine ⟨135890871064088390378133709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181187828085451187170844945 135890871064088390378133709)
  ·
    refine ⟨50959076649033146391800141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135890871064088390378133709 50959076649033146391800141)
    ·
      refine ⟨19109653743387429896925053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50959076649033146391800141 19109653743387429896925053)
      ·
        refine ⟨7166120153770286211346895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19109653743387429896925053 7166120153770286211346895)
        ·
          refine ⟨10749180230655429317020343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7166120153770286211346895 10749180230655429317020343)
          ·
            refine ⟨16123770345983143975530515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10749180230655429317020343 16123770345983143975530515)
            ·
              refine ⟨24185655518974715963295773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16123770345983143975530515 24185655518974715963295773)
              ·
                refine ⟨9069620819615518486235915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24185655518974715963295773 9069620819615518486235915)
                ·
                  refine ⟨13604431229423277729353873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9069620819615518486235915 13604431229423277729353873)
                  ·
                    refine ⟨10203323422067458297015405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13604431229423277729353873 10203323422067458297015405)
                    ·
                      refine ⟨3826246283275296861380777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10203323422067458297015405 3826246283275296861380777)
                      ·
                        rfl

theorem cell23_7451588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_7451588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451588 prefixEnd_7451588 := by exact prefixLift 7451588
  have htrace : WordTrace (prefixWord ++ tailWord_7451588) baseStart_7451588 baseEnd_7451588 := by
    simpa [prefixWord, tailWord_7451588, baseEnd_7451588] using wordTrace_append hprefix tailTrace_7451588
  have hstable : (prefixWord ++ tailWord_7451588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451588).length < 2 ^ (prefixWord ++ tailWord_7451588).sum := by decide
  have hdescent : baseEnd_7451588 < baseStart_7451588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451618 : List Nat := [3, 3, 3, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_7451618 : Nat := 118140960795 + 7451618 * 2 ^ 59
def prefixEnd_7451618 : Nat := 4983230072969 + 3 ^ 40 * 7451618 * 2
def baseEnd_7451618 : Nat := 3826261687694931744005639

theorem tailTrace_7451618 : CollatzResearch.WordTrace tailWord_7451618 prefixEnd_7451618 3826261687694931744005639 := by
  unfold tailWord_7451618
  simp only [CollatzResearch.WordTrace]
  refine ⟨67945709079517023969964877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181188557545378730586573005 67945709079517023969964877)
  ·
    refine ⟨25479640904818883988736829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67945709079517023969964877 25479640904818883988736829)
    ·
      refine ⟨9554865339307081495776311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25479640904818883988736829 9554865339307081495776311)
      ·
        refine ⟨14332298008960622243664467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9554865339307081495776311 14332298008960622243664467)
        ·
          refine ⟨21498447013440933365496701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14332298008960622243664467 21498447013440933365496701)
          ·
            refine ⟨8061917630040350012061263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21498447013440933365496701 8061917630040350012061263)
            ·
              refine ⟨12092876445060525018091895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8061917630040350012061263 12092876445060525018091895)
              ·
                refine ⟨18139314667590787527137843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12092876445060525018091895 18139314667590787527137843)
                ·
                  refine ⟨27208972001386181290706765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18139314667590787527137843 27208972001386181290706765)
                  ·
                    refine ⟨10203364500519817984015037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27208972001386181290706765 10203364500519817984015037)
                    ·
                      refine ⟨3826261687694931744005639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10203364500519817984015037 3826261687694931744005639)
                      ·
                        rfl

theorem cell23_7451618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_7451618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451618 prefixEnd_7451618 := by exact prefixLift 7451618
  have htrace : WordTrace (prefixWord ++ tailWord_7451618) baseStart_7451618 baseEnd_7451618 := by
    simpa [prefixWord, tailWord_7451618, baseEnd_7451618] using wordTrace_append hprefix tailTrace_7451618
  have hstable : (prefixWord ++ tailWord_7451618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451618).length < 2 ^ (prefixWord ++ tailWord_7451618).sum := by decide
  have hdescent : baseEnd_7451618 < baseStart_7451618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451657 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 4, 3, 3]
def baseStart_7451657 : Nat := 118140960795 + 7451657 * 2 ^ 59
def prefixEnd_7451657 : Nat := 4983230072969 + 3 ^ 40 * 7451657 * 2
def baseEnd_7451657 : Nat := 3826281713440457091417959

theorem tailTrace_7451657 : CollatzResearch.WordTrace tailWord_7451657 prefixEnd_7451657 3826281713440457091417959 := by
  unfold tailWord_7451657
  simp only [CollatzResearch.WordTrace]
  refine ⟨271784258764926805540529225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181189505843284537027019483 271784258764926805540529225)
  ·
    refine ⟨203838194073695104155396919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271784258764926805540529225 203838194073695104155396919)
    ·
      refine ⟨305757291110542656233095379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203838194073695104155396919 305757291110542656233095379)
      ·
        refine ⟨458635936665813984349643069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305757291110542656233095379 458635936665813984349643069)
        ·
          refine ⟨171988476249680244131116151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 458635936665813984349643069 171988476249680244131116151)
          ·
            refine ⟨257982714374520366196674227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171988476249680244131116151 257982714374520366196674227)
            ·
              refine ⟨386974071561780549295011341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257982714374520366196674227 386974071561780549295011341)
              ·
                refine ⟨145115276835667705985629253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386974071561780549295011341 145115276835667705985629253)
                ·
                  refine ⟨27209114406687694872305485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145115276835667705985629253 27209114406687694872305485)
                  ·
                    refine ⟨10203417902507885577114557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27209114406687694872305485 10203417902507885577114557)
                    ·
                      refine ⟨3826281713440457091417959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10203417902507885577114557 3826281713440457091417959)
                      ·
                        rfl

theorem cell23_7451657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 3, 3].length) (baseStart_7451657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451657 prefixEnd_7451657 := by exact prefixLift 7451657
  have htrace : WordTrace (prefixWord ++ tailWord_7451657) baseStart_7451657 baseEnd_7451657 := by
    simpa [prefixWord, tailWord_7451657, baseEnd_7451657] using wordTrace_append hprefix tailTrace_7451657
  have hstable : (prefixWord ++ tailWord_7451657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451657).length < 2 ^ (prefixWord ++ tailWord_7451657).sum := by decide
  have hdescent : baseEnd_7451657 < baseStart_7451657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451718 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2]
def baseStart_7451718 : Nat := 118140960795 + 7451718 * 2 ^ 59
def prefixEnd_7451718 : Nat := 4983230072969 + 3 ^ 40 * 7451718 * 2
def baseEnd_7451718 : Nat := 3826313035760381352755179

theorem tailTrace_7451718 : CollatzResearch.WordTrace tailWord_7451718 prefixEnd_7451718 3826313035760381352755179 := by
  unfold tailWord_7451718
  simp only [CollatzResearch.WordTrace]
  refine ⟨8493327613053306654953119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 181190989078470541972333205 8493327613053306654953119)
  ·
    refine ⟨12739991419579959982429679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8493327613053306654953119 12739991419579959982429679)
    ·
      refine ⟨19109987129369939973644519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12739991419579959982429679 19109987129369939973644519)
      ·
        refine ⟨28664980694054909960466779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19109987129369939973644519 28664980694054909960466779)
        ·
          refine ⟨42997471041082364940700169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28664980694054909960466779 42997471041082364940700169)
          ·
            refine ⟨32248103280811773705525127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42997471041082364940700169 32248103280811773705525127)
            ·
              refine ⟨48372154921217660558287691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32248103280811773705525127 48372154921217660558287691)
              ·
                refine ⟨72558232381826490837431537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48372154921217660558287691 72558232381826490837431537)
                ·
                  refine ⟨54418674286369868128073653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72558232381826490837431537 54418674286369868128073653)
                  ·
                    refine ⟨5101750714347175137006905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54418674286369868128073653 5101750714347175137006905)
                    ·
                      refine ⟨3826313035760381352755179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5101750714347175137006905 3826313035760381352755179)
                      ·
                        rfl

theorem cell23_7451718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_7451718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451718 prefixEnd_7451718 := by exact prefixLift 7451718
  have htrace : WordTrace (prefixWord ++ tailWord_7451718) baseStart_7451718 baseEnd_7451718 := by
    simpa [prefixWord, tailWord_7451718, baseEnd_7451718] using wordTrace_append hprefix tailTrace_7451718
  have hstable : (prefixWord ++ tailWord_7451718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451718).length < 2 ^ (prefixWord ++ tailWord_7451718).sum := by decide
  have hdescent : baseEnd_7451718 < baseStart_7451718 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451724 : List Nat := [2, 2, 1, 3, 1, 1, 1, 5, 3, 4]
def baseStart_7451724 : Nat := 118140960795 + 7451724 * 2 ^ 59
def prefixEnd_7451724 : Nat := 4983230072969 + 3 ^ 40 * 7451724 * 2
def baseEnd_7451724 : Nat := 1275438705548102776426717

theorem tailTrace_7451724 : CollatzResearch.WordTrace tailWord_7451724 prefixEnd_7451724 1275438705548102776426717 := by
  unfold tailWord_7451724
  simp only [CollatzResearch.WordTrace]
  refine ⟨135893351227842037991609113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181191134970456050655478817 135893351227842037991609113)
  ·
    refine ⟨101920013420881528493706835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135893351227842037991609113 101920013420881528493706835)
    ·
      refine ⟨152880020131322292740560253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101920013420881528493706835 152880020131322292740560253)
      ·
        refine ⟨57330007549245859777710095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152880020131322292740560253 57330007549245859777710095)
        ·
          refine ⟨85995011323868789666565143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57330007549245859777710095 85995011323868789666565143)
          ·
            refine ⟨128992516985803184499847715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85995011323868789666565143 128992516985803184499847715)
            ·
              refine ⟨193488775478704776749771573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128992516985803184499847715 193488775478704776749771573)
              ·
                refine ⟨18139572701128572820291085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 193488775478704776749771573 18139572701128572820291085)
                ·
                  refine ⟨6802339762923214807609157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18139572701128572820291085 6802339762923214807609157)
                  ·
                    refine ⟨1275438705548102776426717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6802339762923214807609157 1275438705548102776426717)
                    ·
                      rfl

theorem cell23_7451724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 3, 4].length) (baseStart_7451724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451724 prefixEnd_7451724 := by exact prefixLift 7451724
  have htrace : WordTrace (prefixWord ++ tailWord_7451724) baseStart_7451724 baseEnd_7451724 := by
    simpa [prefixWord, tailWord_7451724, baseEnd_7451724] using wordTrace_append hprefix tailTrace_7451724
  have hstable : (prefixWord ++ tailWord_7451724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451724).length < 2 ^ (prefixWord ++ tailWord_7451724).sum := by decide
  have hdescent : baseEnd_7451724 < baseStart_7451724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451751 : List Nat := [1, 1, 5, 1, 1, 3, 3, 1, 2, 2, 3]
def baseStart_7451751 : Nat := 118140960795 + 7451751 * 2 ^ 59
def prefixEnd_7451751 : Nat := 4983230072969 + 3 ^ 40 * 7451751 * 2
def baseEnd_7451751 : Nat := 3826329980621979723642527

theorem tailTrace_7451751 : CollatzResearch.WordTrace tailWord_7451751 prefixEnd_7451751 3826329980621979723642527 := by
  unfold tailWord_7451751
  simp only [CollatzResearch.WordTrace]
  refine ⟨271787687226586259594451107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181191791484390839729634071 271787687226586259594451107)
  ·
    refine ⟨407681530839879389391676661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271787687226586259594451107 407681530839879389391676661)
    ·
      refine ⟨38220143516238692755469687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 407681530839879389391676661 38220143516238692755469687)
      ·
        refine ⟨57330215274358039133204531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38220143516238692755469687 57330215274358039133204531)
        ·
          refine ⟨85995322911537058699806797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57330215274358039133204531 85995322911537058699806797)
          ·
            refine ⟨32248246091826397012427549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85995322911537058699806797 32248246091826397012427549)
            ·
              refine ⟨12093092284434898879660331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32248246091826397012427549 12093092284434898879660331)
              ·
                refine ⟨18139638426652348319490497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12093092284434898879660331 18139638426652348319490497)
                ·
                  refine ⟨13604728819989261239617873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18139638426652348319490497 13604728819989261239617873)
                  ·
                    refine ⟨10203546614991945929713405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13604728819989261239617873 10203546614991945929713405)
                    ·
                      refine ⟨3826329980621979723642527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10203546614991945929713405 3826329980621979723642527)
                      ·
                        rfl

theorem cell23_7451751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_7451751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451751 prefixEnd_7451751 := by exact prefixLift 7451751
  have htrace : WordTrace (prefixWord ++ tailWord_7451751) baseStart_7451751 baseEnd_7451751 := by
    simpa [prefixWord, tailWord_7451751, baseEnd_7451751] using wordTrace_append hprefix tailTrace_7451751
  have hstable : (prefixWord ++ tailWord_7451751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451751).length < 2 ^ (prefixWord ++ tailWord_7451751).sum := by decide
  have hdescent : baseEnd_7451751 < baseStart_7451751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451758 : List Nat := [4, 1, 2, 2, 1, 2, 1, 5, 1, 4]
def baseStart_7451758 : Nat := 118140960795 + 7451758 * 2 ^ 59
def prefixEnd_7451758 : Nat := 4983230072969 + 3 ^ 40 * 7451758 * 2
def baseEnd_7451758 : Nat := 1275444524995520398751665

theorem tailTrace_7451758 : CollatzResearch.WordTrace tailWord_7451758 prefixEnd_7451758 1275444524995520398751665 := by
  unfold tailWord_7451758
  simp only [CollatzResearch.WordTrace]
  refine ⟨33973492817195112473744491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181191961691707266526637285 33973492817195112473744491)
  ·
    refine ⟨50960239225792668710616737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33973492817195112473744491 50960239225792668710616737)
    ·
      refine ⟨38220179419344501532962553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50960239225792668710616737 38220179419344501532962553)
      ·
        refine ⟨28665134564508376149721915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38220179419344501532962553 28665134564508376149721915)
        ·
          refine ⟨42997701846762564224582873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28665134564508376149721915 42997701846762564224582873)
          ·
            refine ⟨32248276385071923168437155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42997701846762564224582873 32248276385071923168437155)
            ·
              refine ⟨48372414577607884752655733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32248276385071923168437155 48372414577607884752655733)
              ·
                refine ⟨4534913866650739195561475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48372414577607884752655733 4534913866650739195561475)
                ·
                  refine ⟨6802370799976108793342213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4534913866650739195561475 6802370799976108793342213)
                  ·
                    refine ⟨1275444524995520398751665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6802370799976108793342213 1275444524995520398751665)
                    ·
                      rfl

theorem cell23_7451758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_7451758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451758 prefixEnd_7451758 := by exact prefixLift 7451758
  have htrace : WordTrace (prefixWord ++ tailWord_7451758) baseStart_7451758 baseEnd_7451758 := by
    simpa [prefixWord, tailWord_7451758, baseEnd_7451758] using wordTrace_append hprefix tailTrace_7451758
  have hstable : (prefixWord ++ tailWord_7451758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451758).length < 2 ^ (prefixWord ++ tailWord_7451758).sum := by decide
  have hdescent : baseEnd_7451758 < baseStart_7451758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451817 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 2, 5, 6]
def baseStart_7451817 : Nat := 118140960795 + 7451817 * 2 ^ 59
def prefixEnd_7451817 : Nat := 4983230072969 + 3 ^ 40 * 7451817 * 2
def baseEnd_7451817 : Nat := 3826363870345176465417223

theorem tailTrace_7451817 : CollatzResearch.WordTrace tailWord_7451817 prefixEnd_7451817 3826363870345176465417223 := by
  unfold tailWord_7451817
  simp only [CollatzResearch.WordTrace]
  refine ⟨271790094444347152866353705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181193396296231435244235803 271790094444347152866353705)
  ·
    refine ⟨203842570833260364649765279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271790094444347152866353705 203842570833260364649765279)
    ·
      refine ⟨305763856249890546974647919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203842570833260364649765279 305763856249890546974647919)
      ·
        refine ⟨458645784374835820461971879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305763856249890546974647919 458645784374835820461971879)
        ·
          refine ⟨687968676562253730692957819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458645784374835820461971879 687968676562253730692957819)
          ·
            refine ⟨1031953014843380596039436729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687968676562253730692957819 1031953014843380596039436729)
            ·
              refine ⟨773964761132535447029577547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1031953014843380596039436729 773964761132535447029577547)
              ·
                refine ⟨1160947141698803170544366321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 773964761132535447029577547 1160947141698803170544366321)
                ·
                  refine ⟨870710356274102377908274741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1160947141698803170544366321 870710356274102377908274741)
                  ·
                    refine ⟨81629095900697097928900757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 870710356274102377908274741 81629095900697097928900757)
                    ·
                      refine ⟨3826363870345176465417223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81629095900697097928900757 3826363870345176465417223)
                      ·
                        rfl

theorem cell23_7451817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 5, 6].length) (baseStart_7451817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451817 prefixEnd_7451817 := by exact prefixLift 7451817
  have htrace : WordTrace (prefixWord ++ tailWord_7451817) baseStart_7451817 baseEnd_7451817 := by
    simpa [prefixWord, tailWord_7451817, baseEnd_7451817] using wordTrace_append hprefix tailTrace_7451817
  have hstable : (prefixWord ++ tailWord_7451817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451817).length < 2 ^ (prefixWord ++ tailWord_7451817).sum := by decide
  have hdescent : baseEnd_7451817 < baseStart_7451817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451818 : List Nat := [3, 1, 5, 1, 1, 1, 2, 3, 1, 5]
def baseStart_7451818 : Nat := 118140960795 + 7451818 * 2 ^ 59
def prefixEnd_7451818 : Nat := 4983230072969 + 3 ^ 40 * 7451818 * 2
def baseEnd_7451818 : Nat := 1275454794608610320501573

theorem tailTrace_7451818 : CollatzResearch.WordTrace tailWord_7451818 prefixEnd_7451818 1275454794608610320501573 := by
  unfold tailWord_7451818
  simp only [CollatzResearch.WordTrace]
  refine ⟨67947532729335882509285027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181193420611562353358093405 67947532729335882509285027)
  ·
    refine ⟨101921299094003823763927541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67947532729335882509285027 101921299094003823763927541)
    ·
      refine ⟨9555121790062858477868207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101921299094003823763927541 9555121790062858477868207)
      ·
        refine ⟨14332682685094287716802311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9555121790062858477868207 14332682685094287716802311)
        ·
          refine ⟨21499024027641431575203467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14332682685094287716802311 21499024027641431575203467)
          ·
            refine ⟨32248536041462147362805201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21499024027641431575203467 32248536041462147362805201)
            ·
              refine ⟨24186402031096610522103901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32248536041462147362805201 24186402031096610522103901)
              ·
                refine ⟨9069900761661228945788963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24186402031096610522103901 9069900761661228945788963)
                ·
                  refine ⟨13604851142491843418683445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9069900761661228945788963 13604851142491843418683445)
                  ·
                    refine ⟨1275454794608610320501573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13604851142491843418683445 1275454794608610320501573)
                    ·
                      rfl

theorem cell23_7451818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_7451818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451818 prefixEnd_7451818 := by exact prefixLift 7451818
  have htrace : WordTrace (prefixWord ++ tailWord_7451818) baseStart_7451818 baseEnd_7451818 := by
    simpa [prefixWord, tailWord_7451818, baseEnd_7451818] using wordTrace_append hprefix tailTrace_7451818
  have hstable : (prefixWord ++ tailWord_7451818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451818).length < 2 ^ (prefixWord ++ tailWord_7451818).sum := by decide
  have hdescent : baseEnd_7451818 < baseStart_7451818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451827 : List Nat := [1, 1, 1, 2, 3, 2, 13]
def baseStart_7451827 : Nat := 118140960795 + 7451827 * 2 ^ 59
def prefixEnd_7451827 : Nat := 4983230072969 + 3 ^ 40 * 7451827 * 2
def baseEnd_7451827 : Nat := 47239123520391622546817

theorem tailTrace_7451827 : CollatzResearch.WordTrace tailWord_7451827 prefixEnd_7451827 47239123520391622546817 := by
  unfold tailWord_7451827
  simp only [CollatzResearch.WordTrace]
  refine ⟨271790459174310924574217735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181193639449540616382811823 271790459174310924574217735)
  ·
    refine ⟨407685688761466386861326603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271790459174310924574217735 407685688761466386861326603)
    ·
      refine ⟨611528533142199580291989905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407685688761466386861326603 611528533142199580291989905)
      ·
        refine ⟨458646399856649685218992429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 611528533142199580291989905 458646399856649685218992429)
        ·
          refine ⟨171992399946243631957122161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 458646399856649685218992429 171992399946243631957122161)
          ·
            refine ⟨128994299959682723967841621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171992399946243631957122161 128994299959682723967841621)
            ·
              refine ⟨47239123520391622546817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 128994299959682723967841621 47239123520391622546817)
              ·
                rfl

theorem cell23_7451827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 13].length) (baseStart_7451827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451827 prefixEnd_7451827 := by exact prefixLift 7451827
  have htrace : WordTrace (prefixWord ++ tailWord_7451827) baseStart_7451827 baseEnd_7451827 := by
    simpa [prefixWord, tailWord_7451827, baseEnd_7451827] using wordTrace_append hprefix tailTrace_7451827
  have hstable : (prefixWord ++ tailWord_7451827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451827).length < 2 ^ (prefixWord ++ tailWord_7451827).sum := by decide
  have hdescent : baseEnd_7451827 < baseStart_7451827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451831 : List Nat := [1, 1, 3, 1, 4, 1, 2, 4, 2, 4]
def baseStart_7451831 : Nat := 118140960795 + 7451831 * 2 ^ 59
def prefixEnd_7451831 : Nat := 4983230072969 + 3 ^ 40 * 7451831 * 2
def baseEnd_7451831 : Nat := 1275457019691446470214053

theorem tailTrace_7451831 : CollatzResearch.WordTrace tailWord_7451831 prefixEnd_7451831 1275457019691446470214053 := by
  unfold tailWord_7451831
  simp only [CollatzResearch.WordTrace]
  refine ⟨271790605066296433257363347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181193736710864288838242231 271790605066296433257363347)
  ·
    refine ⟨407685907599444649886045021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271790605066296433257363347 407685907599444649886045021)
    ·
      refine ⟨152882215349791743707266883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407685907599444649886045021 152882215349791743707266883)
      ·
        refine ⟨229323323024687615560900325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152882215349791743707266883 229323323024687615560900325)
        ·
          refine ⟨42998123067128927917668811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229323323024687615560900325 42998123067128927917668811)
          ·
            refine ⟨64497184600693391876503217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42998123067128927917668811 64497184600693391876503217)
            ·
              refine ⟨48372888450520043907377413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64497184600693391876503217 48372888450520043907377413)
              ·
                refine ⟨9069916584472508232633265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48372888450520043907377413 9069916584472508232633265)
                ·
                  refine ⟨6802437438354381174474949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9069916584472508232633265 6802437438354381174474949)
                  ·
                    refine ⟨1275457019691446470214053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6802437438354381174474949 1275457019691446470214053)
                    ·
                      rfl

theorem cell23_7451831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2, 4].length) (baseStart_7451831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451831 prefixEnd_7451831 := by exact prefixLift 7451831
  have htrace : WordTrace (prefixWord ++ tailWord_7451831) baseStart_7451831 baseEnd_7451831 := by
    simpa [prefixWord, tailWord_7451831, baseEnd_7451831] using wordTrace_append hprefix tailTrace_7451831
  have hstable : (prefixWord ++ tailWord_7451831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451831).length < 2 ^ (prefixWord ++ tailWord_7451831).sum := by decide
  have hdescent : baseEnd_7451831 < baseStart_7451831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451848 : List Nat := [2, 1, 3, 1, 2, 1, 6, 1, 2, 4]
def baseStart_7451848 : Nat := 118140960795 + 7451848 * 2 ^ 59
def prefixEnd_7451848 : Nat := 4983230072969 + 3 ^ 40 * 7451848 * 2
def baseEnd_7451848 : Nat := 1275459929415155281376527

theorem tailTrace_7451848 : CollatzResearch.WordTrace tailWord_7451848 prefixEnd_7451848 1275459929415155281376527 := by
  unfold tailWord_7451848
  simp only [CollatzResearch.WordTrace]
  refine ⟨135895612553617422580366099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181194150071489896773821465 135895612553617422580366099)
  ·
    refine ⟨203843418830426133870549149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135895612553617422580366099 203843418830426133870549149)
    ·
      refine ⟨76441282061409800201455931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203843418830426133870549149 76441282061409800201455931)
      ·
        refine ⟨114661923092114700302183897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76441282061409800201455931 114661923092114700302183897)
        ·
          refine ⟨85996442319086025226637923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114661923092114700302183897 85996442319086025226637923)
          ·
            refine ⟨128994663478629037839956885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85996442319086025226637923 128994663478629037839956885)
            ·
              refine ⟨6046624850560736148747979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 128994663478629037839956885 6046624850560736148747979)
              ·
                refine ⟨9069937275841104223121969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6046624850560736148747979 9069937275841104223121969)
                ·
                  refine ⟨6802452956880828167341477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9069937275841104223121969 6802452956880828167341477)
                  ·
                    refine ⟨1275459929415155281376527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6802452956880828167341477 1275459929415155281376527)
                    ·
                      rfl

theorem cell23_7451848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_7451848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451848 prefixEnd_7451848 := by exact prefixLift 7451848
  have htrace : WordTrace (prefixWord ++ tailWord_7451848) baseStart_7451848 baseEnd_7451848 := by
    simpa [prefixWord, tailWord_7451848, baseEnd_7451848] using wordTrace_append hprefix tailTrace_7451848
  have hstable : (prefixWord ++ tailWord_7451848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451848).length < 2 ^ (prefixWord ++ tailWord_7451848).sum := by decide
  have hdescent : baseEnd_7451848 < baseStart_7451848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451871 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 6, 1, 3]
def baseStart_7451871 : Nat := 118140960795 + 7451871 * 2 ^ 59
def prefixEnd_7451871 : Nat := 4983230072969 + 3 ^ 40 * 7451871 * 2
def baseEnd_7451871 : Nat := 3826391598300519254141975

theorem tailTrace_7451871 : CollatzResearch.WordTrace tailWord_7451871 prefixEnd_7451871 3826391598300519254141975 := by
  unfold tailWord_7451871
  simp only [CollatzResearch.WordTrace]
  refine ⟨271792063986151520088819467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181194709324101013392546311 271792063986151520088819467)
  ·
    refine ⟨407688095979227280133229201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271792063986151520088819467 407688095979227280133229201)
    ·
      refine ⟨305766071984420460099921901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407688095979227280133229201 305766071984420460099921901)
      ·
        refine ⟨114662276994157672537470713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305766071984420460099921901 114662276994157672537470713)
        ·
          refine ⟨85996707745618254403103035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114662276994157672537470713 85996707745618254403103035)
          ·
            refine ⟨128995061618427381604654553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85996707745618254403103035 128995061618427381604654553)
            ·
              refine ⟨96746296213820536203490915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128995061618427381604654553 96746296213820536203490915)
              ·
                refine ⟨145119444320730804305236373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96746296213820536203490915 145119444320730804305236373)
                ·
                  refine ⟨6802473952534256451807955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 145119444320730804305236373 6802473952534256451807955)
                  ·
                    refine ⟨10203710928801384677711933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6802473952534256451807955 10203710928801384677711933)
                    ·
                      refine ⟨3826391598300519254141975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10203710928801384677711933 3826391598300519254141975)
                      ·
                        rfl

theorem cell23_7451871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_7451871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451871 prefixEnd_7451871 := by exact prefixLift 7451871
  have htrace : WordTrace (prefixWord ++ tailWord_7451871) baseStart_7451871 baseEnd_7451871 := by
    simpa [prefixWord, tailWord_7451871, baseEnd_7451871] using wordTrace_append hprefix tailTrace_7451871
  have hstable : (prefixWord ++ tailWord_7451871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451871).length < 2 ^ (prefixWord ++ tailWord_7451871).sum := by decide
  have hdescent : baseEnd_7451871 < baseStart_7451871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451881 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 7, 3, 2]
def baseStart_7451881 : Nat := 118140960795 + 7451881 * 2 ^ 59
def prefixEnd_7451881 : Nat := 4983230072969 + 3 ^ 40 * 7451881 * 2
def baseEnd_7451881 : Nat := 3826396733107064215016929

theorem tailTrace_7451881 : CollatzResearch.WordTrace tailWord_7451881 prefixEnd_7451881 3826396733107064215016929 := by
  unfold tailWord_7451881
  simp only [CollatzResearch.WordTrace]
  refine ⟨271792428716115291796683497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181194952477410194531122331 271792428716115291796683497)
  ·
    refine ⟨203844321537086468847512623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271792428716115291796683497 203844321537086468847512623)
    ·
      refine ⟨305766482305629703271268935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203844321537086468847512623 305766482305629703271268935)
      ·
        refine ⟨458649723458444554906903403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305766482305629703271268935 458649723458444554906903403)
        ·
          refine ⟨687974585187666832360355105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458649723458444554906903403 687974585187666832360355105)
          ·
            refine ⟨515980938890750124270266329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 687974585187666832360355105 515980938890750124270266329)
            ·
              refine ⟨386985704168062593202699747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 515980938890750124270266329 386985704168062593202699747)
              ·
                refine ⟨580478556252093889804049621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386985704168062593202699747 580478556252093889804049621)
                ·
                  refine ⟨13604966162158450542282413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 580478556252093889804049621 13604966162158450542282413)
                  ·
                    refine ⟨5101862310809418953355905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13604966162158450542282413 5101862310809418953355905)
                    ·
                      refine ⟨3826396733107064215016929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5101862310809418953355905 3826396733107064215016929)
                      ·
                        rfl

theorem cell23_7451881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 3, 2].length) (baseStart_7451881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451881 prefixEnd_7451881 := by exact prefixLift 7451881
  have htrace : WordTrace (prefixWord ++ tailWord_7451881) baseStart_7451881 baseEnd_7451881 := by
    simpa [prefixWord, tailWord_7451881, baseEnd_7451881] using wordTrace_append hprefix tailTrace_7451881
  have hstable : (prefixWord ++ tailWord_7451881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451881).length < 2 ^ (prefixWord ++ tailWord_7451881).sum := by decide
  have hdescent : baseEnd_7451881 < baseStart_7451881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451928 : List Nat := [2, 1, 2, 3, 1, 3, 2, 2, 1, 4, 2]
def baseStart_7451928 : Nat := 118140960795 + 7451928 * 2 ^ 59
def prefixEnd_7451928 : Nat := 4983230072969 + 3 ^ 40 * 7451928 * 2
def baseEnd_7451928 : Nat := 3826420866697825531129213

theorem tailTrace_7451928 : CollatzResearch.WordTrace tailWord_7451928 prefixEnd_7451928 3826420866697825531129213 := by
  unfold tailWord_7451928
  simp only [CollatzResearch.WordTrace]
  refine ⟨135897071473472509411822219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181196095297963345882429625 135897071473472509411822219)
  ·
    refine ⟨203845607210208764117733329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135897071473472509411822219 203845607210208764117733329)
    ·
      refine ⟨152884205407656573088299997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203845607210208764117733329 152884205407656573088299997)
      ·
        refine ⟨57331577027871214908112499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152884205407656573088299997 57331577027871214908112499)
        ·
          refine ⟨85997365541806822362168749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57331577027871214908112499 85997365541806822362168749)
          ·
            refine ⟨32249012078177558385813281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85997365541806822362168749 32249012078177558385813281)
            ·
              refine ⟨24186759058633168789359961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32249012078177558385813281 24186759058633168789359961)
              ·
                refine ⟨18140069293974876592019971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24186759058633168789359961 18140069293974876592019971)
                ·
                  refine ⟨27210103940962314888029957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18140069293974876592019971 27210103940962314888029957)
                  ·
                    refine ⟨5101894488930434041505617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27210103940962314888029957 5101894488930434041505617)
                    ·
                      refine ⟨3826420866697825531129213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5101894488930434041505617 3826420866697825531129213)
                      ·
                        rfl

theorem cell23_7451928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_7451928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451928 prefixEnd_7451928 := by exact prefixLift 7451928
  have htrace : WordTrace (prefixWord ++ tailWord_7451928) baseStart_7451928 baseEnd_7451928 := by
    simpa [prefixWord, tailWord_7451928, baseEnd_7451928] using wordTrace_append hprefix tailTrace_7451928
  have hstable : (prefixWord ++ tailWord_7451928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451928).length < 2 ^ (prefixWord ++ tailWord_7451928).sum := by decide
  have hdescent : baseEnd_7451928 < baseStart_7451928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451941 : List Nat := [1, 3, 1, 2, 4, 1, 1, 2, 2, 2, 4]
def baseStart_7451941 : Nat := 118140960795 + 7451941 * 2 ^ 59
def prefixEnd_7451941 : Nat := 4983230072969 + 3 ^ 40 * 7451941 * 2
def baseEnd_7451941 : Nat := 3826427541946333980266653

theorem tailTrace_7451941 : CollatzResearch.WordTrace tailWord_7451941 prefixEnd_7451941 3826427541946333980266653 := by
  unfold tailWord_7451941
  simp only [CollatzResearch.WordTrace]
  refine ⟨271794617095897922043867677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181196411397265281362578451 271794617095897922043867677)
  ·
    refine ⟨101922981410961720766450379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271794617095897922043867677 101922981410961720766450379)
    ·
      refine ⟨152884472116442581149675569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101922981410961720766450379 152884472116442581149675569)
      ·
        refine ⟨114663354087331935862256677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152884472116442581149675569 114663354087331935862256677)
        ·
          refine ⟨21499378891374737974173127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114663354087331935862256677 21499378891374737974173127)
          ·
            refine ⟨32249068337062106961259691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21499378891374737974173127 32249068337062106961259691)
            ·
              refine ⟨48373602505593160441889537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32249068337062106961259691 48373602505593160441889537)
              ·
                refine ⟨36280201879194870331417153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48373602505593160441889537 36280201879194870331417153)
                ·
                  refine ⟨27210151409396152748562865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36280201879194870331417153 27210151409396152748562865)
                  ·
                    refine ⟨20407613557047114561422149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27210151409396152748562865 20407613557047114561422149)
                    ·
                      refine ⟨3826427541946333980266653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20407613557047114561422149 3826427541946333980266653)
                      ·
                        rfl

theorem cell23_7451941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_7451941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451941 prefixEnd_7451941 := by exact prefixLift 7451941
  have htrace : WordTrace (prefixWord ++ tailWord_7451941) baseStart_7451941 baseEnd_7451941 := by
    simpa [prefixWord, tailWord_7451941, baseEnd_7451941] using wordTrace_append hprefix tailTrace_7451941
  have hstable : (prefixWord ++ tailWord_7451941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451941).length < 2 ^ (prefixWord ++ tailWord_7451941).sum := by decide
  have hdescent : baseEnd_7451941 < baseStart_7451941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7451962 : List Nat := [3, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2]
def baseStart_7451962 : Nat := 118140960795 + 7451962 * 2 ^ 59
def prefixEnd_7451962 : Nat := 4983230072969 + 3 ^ 40 * 7451962 * 2
def baseEnd_7451962 : Nat := 3826438325040078398104057

theorem tailTrace_7451962 : CollatzResearch.WordTrace tailWord_7451962 prefixEnd_7451962 3826438325040078398104057 := by
  unfold tailWord_7451962
  simp only [CollatzResearch.WordTrace]
  refine ⟨67948845757205460657595535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181196922019214561753588093 67948845757205460657595535)
  ·
    refine ⟨101923268635808190986393303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67948845757205460657595535 101923268635808190986393303)
    ·
      refine ⟨152884902953712286479589955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101923268635808190986393303 152884902953712286479589955)
      ·
        refine ⟨229327354430568429719384933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152884902953712286479589955 229327354430568429719384933)
        ·
          refine ⟨42998878955731580572384675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229327354430568429719384933 42998878955731580572384675)
          ·
            refine ⟨64498318433597370858577013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42998878955731580572384675 64498318433597370858577013)
            ·
              refine ⟨6046717353149753517991595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64498318433597370858577013 6046717353149753517991595)
              ·
                refine ⟨9070076029724630276987393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6046717353149753517991595 9070076029724630276987393)
                ·
                  refine ⟨6802557022293472707740545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9070076029724630276987393 6802557022293472707740545)
                  ·
                    refine ⟨5101917766720104530805409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6802557022293472707740545 5101917766720104530805409)
                    ·
                      refine ⟨3826438325040078398104057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5101917766720104530805409 3826438325040078398104057)
                      ·
                        rfl

theorem cell23_7451962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2].length) (baseStart_7451962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7451962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7451962 prefixEnd_7451962 := by exact prefixLift 7451962
  have htrace : WordTrace (prefixWord ++ tailWord_7451962) baseStart_7451962 baseEnd_7451962 := by
    simpa [prefixWord, tailWord_7451962, baseEnd_7451962] using wordTrace_append hprefix tailTrace_7451962
  have hstable : (prefixWord ++ tailWord_7451962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7451962).length < 2 ^ (prefixWord ++ tailWord_7451962).sum := by decide
  have hdescent : baseEnd_7451962 < baseStart_7451962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7451962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452008 : List Nat := [2, 1, 4, 2, 3, 1, 1, 1, 1, 2, 5]
def baseStart_7452008 : Nat := 118140960795 + 7452008 * 2 ^ 59
def prefixEnd_7452008 : Nat := 4983230072969 + 3 ^ 40 * 7452008 * 2
def baseEnd_7452008 : Nat := 3826461945150185218128845

theorem tailTrace_7452008 : CollatzResearch.WordTrace tailWord_7452008 prefixEnd_7452008 3826461945150185218128845 := by
  unfold tailWord_7452008
  simp only [CollatzResearch.WordTrace]
  refine ⟨135898530393327596243278339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181198040524436794991037785 135898530393327596243278339)
  ·
    refine ⟨203847795589991394364917509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135898530393327596243278339 203847795589991394364917509)
    ·
      refine ⟨38221461673123386443422033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203847795589991394364917509 38221461673123386443422033)
      ·
        refine ⟨28666096254842539832566525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38221461673123386443422033 28666096254842539832566525)
        ·
          refine ⟨10749786095565952437212447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28666096254842539832566525 10749786095565952437212447)
          ·
            refine ⟨16124679143348928655818671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10749786095565952437212447 16124679143348928655818671)
            ·
              refine ⟨24187018715023392983728007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16124679143348928655818671 24187018715023392983728007)
              ·
                refine ⟨36280528072535089475592011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24187018715023392983728007 36280528072535089475592011)
                ·
                  refine ⟨54420792108802634213388017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36280528072535089475592011 54420792108802634213388017)
                  ·
                    refine ⟨40815594081601975660041013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54420792108802634213388017 40815594081601975660041013)
                    ·
                      refine ⟨3826461945150185218128845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40815594081601975660041013 3826461945150185218128845)
                      ·
                        rfl

theorem cell23_7452008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_7452008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452008 prefixEnd_7452008 := by exact prefixLift 7452008
  have htrace : WordTrace (prefixWord ++ tailWord_7452008) baseStart_7452008 baseEnd_7452008 := by
    simpa [prefixWord, tailWord_7452008, baseEnd_7452008] using wordTrace_append hprefix tailTrace_7452008
  have hstable : (prefixWord ++ tailWord_7452008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452008).length < 2 ^ (prefixWord ++ tailWord_7452008).sum := by decide
  have hdescent : baseEnd_7452008 < baseStart_7452008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452018 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 1, 6, 2]
def baseStart_7452018 : Nat := 118140960795 + 7452018 * 2 ^ 59
def prefixEnd_7452018 : Nat := 4983230072969 + 3 ^ 40 * 7452018 * 2
def baseEnd_7452018 : Nat := 3826467079956730179003799

theorem tailTrace_7452018 : CollatzResearch.WordTrace tailWord_7452018 prefixEnd_7452018 3826467079956730179003799 := by
  unfold tailWord_7452018
  simp only [CollatzResearch.WordTrace]
  refine ⟨67949356379154741048605177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181198283677745976129613805 67949356379154741048605177)
  ·
    refine ⟨50962017284366055786453883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67949356379154741048605177 50962017284366055786453883)
    ·
      refine ⟨76443025926549083679680825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50962017284366055786453883 76443025926549083679680825)
      ·
        refine ⟨57332269444911812759760619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76443025926549083679680825 57332269444911812759760619)
        ·
          refine ⟨85998404167367719139640929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57332269444911812759760619 85998404167367719139640929)
          ·
            refine ⟨64498803125525789354730697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85998404167367719139640929 64498803125525789354730697)
            ·
              refine ⟨48374102344144342016048023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64498803125525789354730697 48374102344144342016048023)
              ·
                refine ⟨72561153516216513024072035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48374102344144342016048023 72561153516216513024072035)
                ·
                  refine ⟨108841730274324769536108053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72561153516216513024072035 108841730274324769536108053)
                  ·
                    refine ⟨5101956106608973572005065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108841730274324769536108053 5101956106608973572005065)
                    ·
                      refine ⟨3826467079956730179003799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5101956106608973572005065 3826467079956730179003799)
                      ·
                        rfl

theorem cell23_7452018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_7452018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452018 prefixEnd_7452018 := by exact prefixLift 7452018
  have htrace : WordTrace (prefixWord ++ tailWord_7452018) baseStart_7452018 baseEnd_7452018 := by
    simpa [prefixWord, tailWord_7452018, baseEnd_7452018] using wordTrace_append hprefix tailTrace_7452018
  have hstable : (prefixWord ++ tailWord_7452018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452018).length < 2 ^ (prefixWord ++ tailWord_7452018).sum := by decide
  have hdescent : baseEnd_7452018 < baseStart_7452018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452058 : List Nat := [3, 1, 1, 4, 1, 1, 4, 2, 6]
def baseStart_7452058 : Nat := 118140960795 + 7452058 * 2 ^ 59
def prefixEnd_7452058 : Nat := 4983230072969 + 3 ^ 40 * 7452058 * 2
def baseEnd_7452058 : Nat := 425165291020323335833735

theorem tailTrace_7452058 : CollatzResearch.WordTrace tailWord_7452058 prefixEnd_7452058 425165291020323335833735 := by
  unfold tailWord_7452058
  simp only [CollatzResearch.WordTrace]
  refine ⟨67949721109118512756469207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181199256290982700683917885 67949721109118512756469207)
  ·
    refine ⟨101924581663677769134703811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67949721109118512756469207 101924581663677769134703811)
    ·
      refine ⟨152886872495516653702055717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101924581663677769134703811 152886872495516653702055717)
      ·
        refine ⟨28666288592909372569135447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152886872495516653702055717 28666288592909372569135447)
        ·
          refine ⟨42999432889364058853703171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28666288592909372569135447 42999432889364058853703171)
          ·
            refine ⟨64499149334046088280554757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42999432889364058853703171 64499149334046088280554757)
            ·
              refine ⟨12093590500133641552604017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64499149334046088280554757 12093590500133641552604017)
              ·
                refine ⟨9070192875100231164453013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12093590500133641552604017 9070192875100231164453013)
                ·
                  refine ⟨425165291020323335833735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9070192875100231164453013 425165291020323335833735)
                  ·
                    rfl

theorem cell23_7452058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 6].length) (baseStart_7452058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452058 prefixEnd_7452058 := by exact prefixLift 7452058
  have htrace : WordTrace (prefixWord ++ tailWord_7452058) baseStart_7452058 baseEnd_7452058 := by
    simpa [prefixWord, tailWord_7452058, baseEnd_7452058] using wordTrace_append hprefix tailTrace_7452058
  have hstable : (prefixWord ++ tailWord_7452058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452058).length < 2 ^ (prefixWord ++ tailWord_7452058).sum := by decide
  have hdescent : baseEnd_7452058 < baseStart_7452058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452081 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 2, 1, 7]
def baseStart_7452081 : Nat := 118140960795 + 7452081 * 2 ^ 59
def prefixEnd_7452081 : Nat := 4983230072969 + 3 ^ 40 * 7452081 * 2
def baseEnd_7452081 : Nat := 3826499429237963432516009

theorem tailTrace_7452081 : CollatzResearch.WordTrace tailWord_7452081 prefixEnd_7452081 3826499429237963432516009 := by
  unfold tailWord_7452081
  simp only [CollatzResearch.WordTrace]
  refine ⟨271799723315390725953964097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181199815543593817302642731 271799723315390725953964097)
  ·
    refine ⟨203849792486543044465473073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271799723315390725953964097 203849792486543044465473073)
    ·
      refine ⟨152887344364907283349104805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203849792486543044465473073 152887344364907283349104805)
      ·
        refine ⟨28666377068420115627957151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152887344364907283349104805 28666377068420115627957151)
        ·
          refine ⟨42999565602630173441935727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28666377068420115627957151 42999565602630173441935727)
          ·
            refine ⟨64499348403945260162903591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42999565602630173441935727 64499348403945260162903591)
            ·
              refine ⟨96749022605917890244355387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64499348403945260162903591 96749022605917890244355387)
              ·
                refine ⟨145123533908876835366533081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96749022605917890244355387 145123533908876835366533081)
                ·
                  refine ⟨108842650431657626524899811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145123533908876835366533081 108842650431657626524899811)
                  ·
                    refine ⟨163263975647486439787349717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108842650431657626524899811 163263975647486439787349717)
                    ·
                      refine ⟨3826499429237963432516009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163263975647486439787349717 3826499429237963432516009)
                      ·
                        rfl

theorem cell23_7452081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_7452081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452081 prefixEnd_7452081 := by exact prefixLift 7452081
  have htrace : WordTrace (prefixWord ++ tailWord_7452081) baseStart_7452081 baseEnd_7452081 := by
    simpa [prefixWord, tailWord_7452081, baseEnd_7452081] using wordTrace_append hprefix tailTrace_7452081
  have hstable : (prefixWord ++ tailWord_7452081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452081).length < 2 ^ (prefixWord ++ tailWord_7452081).sum := by decide
  have hdescent : baseEnd_7452081 < baseStart_7452081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452085 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 5, 1, 3]
def baseStart_7452085 : Nat := 118140960795 + 7452085 * 2 ^ 59
def prefixEnd_7452085 : Nat := 4983230072969 + 3 ^ 40 * 7452085 * 2
def baseEnd_7452085 : Nat := 3826501483160581416865991

theorem tailTrace_7452085 : CollatzResearch.WordTrace tailWord_7452085 prefixEnd_7452085 3826501483160581416865991 := by
  unfold tailWord_7452085
  simp only [CollatzResearch.WordTrace]
  refine ⟨271799869207376234637109709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181199912804917489758073139 271799869207376234637109709)
  ·
    refine ⟨101924950952766087988916141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271799869207376234637109709 101924950952766087988916141)
    ·
      refine ⟨38221856607287282995843553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101924950952766087988916141 38221856607287282995843553)
      ·
        refine ⟨28666392455465462246882665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38221856607287282995843553 28666392455465462246882665)
        ·
          refine ⟨21499794341599096685161999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28666392455465462246882665 21499794341599096685161999)
          ·
            refine ⟨32249691512398645027742999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21499794341599096685161999 32249691512398645027742999)
            ·
              refine ⟨48374537268597967541614499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32249691512398645027742999 48374537268597967541614499)
              ·
                refine ⟨72561805902896951312421749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48374537268597967541614499 72561805902896951312421749)
                ·
                  refine ⟨6802669303396589185539539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72561805902896951312421749 6802669303396589185539539)
                  ·
                    refine ⟨10204003955094883778309309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6802669303396589185539539 10204003955094883778309309)
                    ·
                      refine ⟨3826501483160581416865991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10204003955094883778309309 3826501483160581416865991)
                      ·
                        rfl

theorem cell23_7452085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_7452085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452085 prefixEnd_7452085 := by exact prefixLift 7452085
  have htrace : WordTrace (prefixWord ++ tailWord_7452085) baseStart_7452085 baseEnd_7452085 := by
    simpa [prefixWord, tailWord_7452085, baseEnd_7452085] using wordTrace_append hprefix tailTrace_7452085
  have hstable : (prefixWord ++ tailWord_7452085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452085).length < 2 ^ (prefixWord ++ tailWord_7452085).sum := by decide
  have hdescent : baseEnd_7452085 < baseStart_7452085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452128 : List Nat := [2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 3]
def baseStart_7452128 : Nat := 118140960795 + 7452128 * 2 ^ 59
def prefixEnd_7452128 : Nat := 4983230072969 + 3 ^ 40 * 7452128 * 2
def baseEnd_7452128 : Nat := 3826523562828724748628293

theorem tailTrace_7452128 : CollatzResearch.WordTrace tailWord_7452128 prefixEnd_7452128 3826523562828724748628293 := by
  unfold tailWord_7452128
  simp only [CollatzResearch.WordTrace]
  refine ⟨135900718773110226490462519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181200958364146968653950025 135900718773110226490462519)
  ·
    refine ⟨203851078159665339735693779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135900718773110226490462519 203851078159665339735693779)
    ·
      refine ⟨305776617239498009603540669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203851078159665339735693779 305776617239498009603540669)
      ·
        refine ⟨114666231464811753601327751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305776617239498009603540669 114666231464811753601327751)
        ·
          refine ⟨171999347197217630401991627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114666231464811753601327751 171999347197217630401991627)
          ·
            refine ⟨257999020795826445602987441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171999347197217630401991627 257999020795826445602987441)
            ·
              refine ⟨193499265596869834202240581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257999020795826445602987441 193499265596869834202240581)
              ·
                refine ⟨36281112299413093912920109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193499265596869834202240581 36281112299413093912920109)
                ·
                  refine ⟨13605417112279910217345041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36281112299413093912920109 13605417112279910217345041)
                  ·
                    refine ⟨10204062834209932663008781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13605417112279910217345041 10204062834209932663008781)
                    ·
                      refine ⟨3826523562828724748628293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10204062834209932663008781 3826523562828724748628293)
                      ·
                        rfl

theorem cell23_7452128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_7452128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452128 prefixEnd_7452128 := by exact prefixLift 7452128
  have htrace : WordTrace (prefixWord ++ tailWord_7452128) baseStart_7452128 baseEnd_7452128 := by
    simpa [prefixWord, tailWord_7452128, baseEnd_7452128] using wordTrace_append hprefix tailTrace_7452128
  have hstable : (prefixWord ++ tailWord_7452128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452128).length < 2 ^ (prefixWord ++ tailWord_7452128).sum := by decide
  have hdescent : baseEnd_7452128 < baseStart_7452128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452135 : List Nat := [1, 1, 5, 2, 1, 4, 1, 1, 1, 6]
def baseStart_7452135 : Nat := 118140960795 + 7452135 * 2 ^ 59
def prefixEnd_7452135 : Nat := 4983230072969 + 3 ^ 40 * 7452135 * 2
def baseEnd_7452135 : Nat := 1275509052397768740413587

theorem tailTrace_7452135 : CollatzResearch.WordTrace tailWord_7452135 prefixEnd_7452135 1275509052397768740413587 := by
  unfold tailWord_7452135
  simp only [CollatzResearch.WordTrace]
  refine ⟨271801692857195093176429859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181201128571463395450953239 271801692857195093176429859)
  ·
    refine ⟨407702539285792639764644789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271801692857195093176429859 407702539285792639764644789)
    ·
      refine ⟨38222113058043059977935449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 407702539285792639764644789 38222113058043059977935449)
      ·
        refine ⟨28666584793532294983451587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38222113058043059977935449 28666584793532294983451587)
        ·
          refine ⟨42999877190298442475177381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28666584793532294983451587 42999877190298442475177381)
          ·
            refine ⟨8062476973180957964095759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42999877190298442475177381 8062476973180957964095759)
            ·
              refine ⟨12093715459771436946143639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8062476973180957964095759 12093715459771436946143639)
              ·
                refine ⟨18140573189657155419215459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12093715459771436946143639 18140573189657155419215459)
                ·
                  refine ⟨27210859784485733128823189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18140573189657155419215459 27210859784485733128823189)
                  ·
                    refine ⟨1275509052397768740413587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27210859784485733128823189 1275509052397768740413587)
                    ·
                      rfl

theorem cell23_7452135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_7452135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452135 prefixEnd_7452135 := by exact prefixLift 7452135
  have htrace : WordTrace (prefixWord ++ tailWord_7452135) baseStart_7452135 baseEnd_7452135 := by
    simpa [prefixWord, tailWord_7452135, baseEnd_7452135] using wordTrace_append hprefix tailTrace_7452135
  have hstable : (prefixWord ++ tailWord_7452135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452135).length < 2 ^ (prefixWord ++ tailWord_7452135).sum := by decide
  have hdescent : baseEnd_7452135 < baseStart_7452135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452142 : List Nat := [4, 1, 2, 1, 2, 1, 1, 4, 3, 2, 2]
def baseStart_7452142 : Nat := 118140960795 + 7452142 * 2 ^ 59
def prefixEnd_7452142 : Nat := 4983230072969 + 3 ^ 40 * 7452142 * 2
def baseEnd_7452142 : Nat := 3826530751557887693853229

theorem tailTrace_7452142 : CollatzResearch.WordTrace tailWord_7452142 prefixEnd_7452142 3826530751557887693853229 := by
  unfold tailWord_7452142
  simp only [CollatzResearch.WordTrace]
  refine ⟨33975243521021216671491835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181201298778779822247956453 33975243521021216671491835)
  ·
    refine ⟨50962865281531825007237753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33975243521021216671491835 50962865281531825007237753)
    ·
      refine ⟨38222148961148868755428315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50962865281531825007237753 38222148961148868755428315)
      ·
        refine ⟨57333223441723303133142473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38222148961148868755428315 57333223441723303133142473)
        ·
          refine ⟨42999917581292477349856855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57333223441723303133142473 42999917581292477349856855)
          ·
            refine ⟨64499876371938716024785283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42999917581292477349856855 64499876371938716024785283)
            ·
              refine ⟨96749814557908074037177925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64499876371938716024785283 96749814557908074037177925)
              ·
                refine ⟨18140590229607763881970861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96749814557908074037177925 18140590229607763881970861)
                ·
                  refine ⟨6802721336102911455739073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18140590229607763881970861 6802721336102911455739073)
                  ·
                    refine ⟨5102041002077183591804305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6802721336102911455739073 5102041002077183591804305)
                    ·
                      refine ⟨3826530751557887693853229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5102041002077183591804305 3826530751557887693853229)
                      ·
                        rfl

theorem cell23_7452142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_7452142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452142 prefixEnd_7452142 := by exact prefixLift 7452142
  have htrace : WordTrace (prefixWord ++ tailWord_7452142) baseStart_7452142 baseEnd_7452142 := by
    simpa [prefixWord, tailWord_7452142, baseEnd_7452142] using wordTrace_append hprefix tailTrace_7452142
  have hstable : (prefixWord ++ tailWord_7452142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452142).length < 2 ^ (prefixWord ++ tailWord_7452142).sum := by decide
  have hdescent : baseEnd_7452142 < baseStart_7452142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452145 : List Nat := [1, 2, 2, 2, 3, 2, 1, 4, 1, 2, 3]
def baseStart_7452145 : Nat := 118140960795 + 7452145 * 2 ^ 59
def prefixEnd_7452145 : Nat := 4983230072969 + 3 ^ 40 * 7452145 * 2
def baseEnd_7452145 : Nat := 3826532291999851182115715

theorem tailTrace_7452145 : CollatzResearch.WordTrace tailWord_7452145 prefixEnd_7452145 3826532291999851182115715 := by
  unfold tailWord_7452145
  simp only [CollatzResearch.WordTrace]
  refine ⟨271802057587158864884293889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181201371724772576589529259 271802057587158864884293889)
  ·
    refine ⟨203851543190369148663220417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271802057587158864884293889 203851543190369148663220417)
    ·
      refine ⟨152888657392776861497415313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203851543190369148663220417 152888657392776861497415313)
      ·
        refine ⟨114666493044582646123061485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152888657392776861497415313 114666493044582646123061485)
        ·
          refine ⟨42999934891718492296148057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114666493044582646123061485 42999934891718492296148057)
          ·
            refine ⟨32249951168788869222111043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42999934891718492296148057 32249951168788869222111043)
            ·
              refine ⟨48374926753183303833166565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32249951168788869222111043 48374926753183303833166565)
              ·
                refine ⟨9070298766221869468718731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48374926753183303833166565 9070298766221869468718731)
                ·
                  refine ⟨13605448149332804203078097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9070298766221869468718731 13605448149332804203078097)
                  ·
                    refine ⟨10204086111999603152308573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13605448149332804203078097 10204086111999603152308573)
                    ·
                      refine ⟨3826532291999851182115715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10204086111999603152308573 3826532291999851182115715)
                      ·
                        rfl

theorem cell23_7452145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_7452145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452145 prefixEnd_7452145 := by exact prefixLift 7452145
  have htrace : WordTrace (prefixWord ++ tailWord_7452145) baseStart_7452145 baseEnd_7452145 := by
    simpa [prefixWord, tailWord_7452145, baseEnd_7452145] using wordTrace_append hprefix tailTrace_7452145
  have hstable : (prefixWord ++ tailWord_7452145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452145).length < 2 ^ (prefixWord ++ tailWord_7452145).sum := by decide
  have hdescent : baseEnd_7452145 < baseStart_7452145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452162 : List Nat := [3, 4, 1, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_7452162 : Nat := 118140960795 + 7452162 * 2 ^ 59
def prefixEnd_7452162 : Nat := 4983230072969 + 3 ^ 40 * 7452162 * 2
def baseEnd_7452162 : Nat := 3826541021170977615603137

theorem tailTrace_7452162 : CollatzResearch.WordTrace tailWord_7452162 prefixEnd_7452162 3826541021170977615603137 := by
  unfold tailWord_7452162
  simp only [CollatzResearch.WordTrace]
  refine ⟨67950669407024319196915685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181201785085398184525108493 67950669407024319196915685)
  ·
    refine ⟨12740750513817059849421691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67950669407024319196915685 12740750513817059849421691)
    ·
      refine ⟨19111125770725589774132537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12740750513817059849421691 19111125770725589774132537)
      ·
        refine ⟨14333344328044192330599403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19111125770725589774132537 14333344328044192330599403)
        ·
          refine ⟨21500016492066288495899105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14333344328044192330599403 21500016492066288495899105)
          ·
            refine ⟨16125012369049716371924329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21500016492066288495899105 16125012369049716371924329)
            ·
              refine ⟨12093759276787287278943247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16125012369049716371924329 12093759276787287278943247)
              ·
                refine ⟨18140638915180930918414871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12093759276787287278943247 18140638915180930918414871)
                ·
                  refine ⟨27210958372771396377622307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18140638915180930918414871 27210958372771396377622307)
                  ·
                    refine ⟨40816437559157094566433461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27210958372771396377622307 40816437559157094566433461)
                    ·
                      refine ⟨3826541021170977615603137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40816437559157094566433461 3826541021170977615603137)
                      ·
                        rfl

theorem cell23_7452162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_7452162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452162 prefixEnd_7452162 := by exact prefixLift 7452162
  have htrace : WordTrace (prefixWord ++ tailWord_7452162) baseStart_7452162 baseEnd_7452162 := by
    simpa [prefixWord, tailWord_7452162, baseEnd_7452162] using wordTrace_append hprefix tailTrace_7452162
  have hstable : (prefixWord ++ tailWord_7452162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452162).length < 2 ^ (prefixWord ++ tailWord_7452162).sum := by decide
  have hdescent : baseEnd_7452162 < baseStart_7452162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452201 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 9]
def baseStart_7452201 : Nat := 118140960795 + 7452201 * 2 ^ 59
def prefixEnd_7452201 : Nat := 4983230072969 + 3 ^ 40 * 7452201 * 2
def baseEnd_7452201 : Nat := 3826561046916502963015457

theorem tailTrace_7452201 : CollatzResearch.WordTrace tailWord_7452201 prefixEnd_7452201 3826561046916502963015457 := by
  unfold tailWord_7452201
  simp only [CollatzResearch.WordTrace]
  refine ⟨271804100074955986448332457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181202733383303990965554971 271804100074955986448332457)
  ·
    refine ⟨203853075056216989836249343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271804100074955986448332457 203853075056216989836249343)
    ·
      refine ⟨305779612584325484754374015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203853075056216989836249343 305779612584325484754374015)
      ·
        refine ⟨458669418876488227131561023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305779612584325484754374015 458669418876488227131561023)
        ·
          refine ⟨688004128314732340697341535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458669418876488227131561023 688004128314732340697341535)
          ·
            refine ⟨1032006192472098511046012303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688004128314732340697341535 1032006192472098511046012303)
            ·
              refine ⟨1548009288708147766569018455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1032006192472098511046012303 1548009288708147766569018455)
              ·
                refine ⟨2322013933062221649853527683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1548009288708147766569018455 2322013933062221649853527683)
                ·
                  refine ⟨3483020899593332474780291525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2322013933062221649853527683 3483020899593332474780291525)
                  ·
                    refine ⟨653066418673749839021304661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3483020899593332474780291525 653066418673749839021304661)
                    ·
                      refine ⟨3826561046916502963015457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 653066418673749839021304661 3826561046916502963015457)
                      ·
                        rfl

theorem cell23_7452201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_7452201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452201 prefixEnd_7452201 := by exact prefixLift 7452201
  have htrace : WordTrace (prefixWord ++ tailWord_7452201) baseStart_7452201 baseEnd_7452201 := by
    simpa [prefixWord, tailWord_7452201, baseEnd_7452201] using wordTrace_append hprefix tailTrace_7452201
  have hstable : (prefixWord ++ tailWord_7452201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452201).length < 2 ^ (prefixWord ++ tailWord_7452201).sum := by decide
  have hdescent : baseEnd_7452201 < baseStart_7452201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452202 : List Nat := [3, 1, 4, 1, 1, 1, 3, 1, 3, 3, 2]
def baseStart_7452202 : Nat := 118140960795 + 7452202 * 2 ^ 59
def prefixEnd_7452202 : Nat := 4983230072969 + 3 ^ 40 * 7452202 * 2
def baseEnd_7452202 : Nat := 3826561560397157459102953

theorem tailTrace_7452202 : CollatzResearch.WordTrace tailWord_7452202 prefixEnd_7452202 3826561560397157459102953 := by
  unfold tailWord_7452202
  simp only [CollatzResearch.WordTrace]
  refine ⟨67951034136988090904779715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181202757698634909079412573 67951034136988090904779715)
  ·
    refine ⟨101926551205482136357169573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67951034136988090904779715 101926551205482136357169573)
    ·
      refine ⟨19111228351027900566969295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101926551205482136357169573 19111228351027900566969295)
      ·
        refine ⟨28666842526541850850453943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19111228351027900566969295 28666842526541850850453943)
        ·
          refine ⟨43000263789812776275680915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28666842526541850850453943 43000263789812776275680915)
          ·
            refine ⟨64500395684719164413521373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43000263789812776275680915 64500395684719164413521373)
            ·
              refine ⟨24187648381769686655070515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64500395684719164413521373 24187648381769686655070515)
              ·
                refine ⟨36281472572654529982605773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24187648381769686655070515 36281472572654529982605773)
                ·
                  refine ⟨13605552214745448743477165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36281472572654529982605773 13605552214745448743477165)
                  ·
                    refine ⟨5102082080529543278803937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13605552214745448743477165 5102082080529543278803937)
                    ·
                      refine ⟨3826561560397157459102953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5102082080529543278803937 3826561560397157459102953)
                      ·
                        rfl

theorem cell23_7452202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_7452202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452202 prefixEnd_7452202 := by exact prefixLift 7452202
  have htrace : WordTrace (prefixWord ++ tailWord_7452202) baseStart_7452202 baseEnd_7452202 := by
    simpa [prefixWord, tailWord_7452202, baseEnd_7452202] using wordTrace_append hprefix tailTrace_7452202
  have hstable : (prefixWord ++ tailWord_7452202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452202).length < 2 ^ (prefixWord ++ tailWord_7452202).sum := by decide
  have hdescent : baseEnd_7452202 < baseStart_7452202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452215 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 3, 4, 2]
def baseStart_7452215 : Nat := 118140960795 + 7452215 * 2 ^ 59
def prefixEnd_7452215 : Nat := 4983230072969 + 3 ^ 40 * 7452215 * 2
def baseEnd_7452215 : Nat := 3826568235645665908240393

theorem tailTrace_7452215 : CollatzResearch.WordTrace tailWord_7452215 prefixEnd_7452215 3826568235645665908240393 := by
  unfold tailWord_7452215
  simp only [CollatzResearch.WordTrace]
  refine ⟨271804610696905266839342099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181203073797936844559561399 271804610696905266839342099)
  ·
    refine ⟨407706916045357900259013149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271804610696905266839342099 407706916045357900259013149)
    ·
      refine ⟨152890093517009212597129931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407706916045357900259013149 152890093517009212597129931)
      ·
        refine ⟨229335140275513818895694897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152890093517009212597129931 229335140275513818895694897)
        ·
          refine ⟨172001355206635364171771173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229335140275513818895694897 172001355206635364171771173)
          ·
            refine ⟨32250254101244130782207095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172001355206635364171771173 32250254101244130782207095)
            ·
              refine ⟨48375381151866196173310643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32250254101244130782207095 48375381151866196173310643)
              ·
                refine ⟨72563071727799294259965965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48375381151866196173310643 72563071727799294259965965)
                ·
                  refine ⟨27211151897924735347487237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72563071727799294259965965 27211151897924735347487237)
                  ·
                    refine ⟨5102090980860887877653857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27211151897924735347487237 5102090980860887877653857)
                    ·
                      refine ⟨3826568235645665908240393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5102090980860887877653857 3826568235645665908240393)
                      ·
                        rfl

theorem cell23_7452215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 4, 2].length) (baseStart_7452215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452215 prefixEnd_7452215 := by exact prefixLift 7452215
  have htrace : WordTrace (prefixWord ++ tailWord_7452215) baseStart_7452215 baseEnd_7452215 := by
    simpa [prefixWord, tailWord_7452215, baseEnd_7452215] using wordTrace_append hprefix tailTrace_7452215
  have hstable : (prefixWord ++ tailWord_7452215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452215).length < 2 ^ (prefixWord ++ tailWord_7452215).sum := by decide
  have hdescent : baseEnd_7452215 < baseStart_7452215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452218 : List Nat := [3, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5]
def baseStart_7452218 : Nat := 118140960795 + 7452218 * 2 ^ 59
def prefixEnd_7452218 : Nat := 4983230072969 + 3 ^ 40 * 7452218 * 2
def baseEnd_7452218 : Nat := 3826569776087629396502879

theorem tailTrace_7452218 : CollatzResearch.WordTrace tailWord_7452218 prefixEnd_7452218 3826569776087629396502879 := by
  unfold tailWord_7452218
  simp only [CollatzResearch.WordTrace]
  refine ⟨67951180028973599587925327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181203146743929598901134205 67951180028973599587925327)
  ·
    refine ⟨101926770043460399381887991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67951180028973599587925327 101926770043460399381887991)
    ·
      refine ⟨152890155065190599072831987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101926770043460399381887991 152890155065190599072831987)
      ·
        refine ⟨229335232597785898609247981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152890155065190599072831987 229335232597785898609247981)
        ·
          refine ⟨86000712224169711978467993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229335232597785898609247981 86000712224169711978467993)
          ·
            refine ⟨64500534168127283983850995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86000712224169711978467993 64500534168127283983850995)
            ·
              refine ⟨96750801252190925975776493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64500534168127283983850995 96750801252190925975776493)
              ·
                refine ⟨36281550469571597240916185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96750801252190925975776493 36281550469571597240916185)
                ·
                  refine ⟨27211162852178697930687139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36281550469571597240916185 27211162852178697930687139)
                  ·
                    refine ⟨40816744278268046896030709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27211162852178697930687139 40816744278268046896030709)
                    ·
                      refine ⟨3826569776087629396502879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40816744278268046896030709 3826569776087629396502879)
                      ·
                        rfl

theorem cell23_7452218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_7452218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452218 prefixEnd_7452218 := by exact prefixLift 7452218
  have htrace : WordTrace (prefixWord ++ tailWord_7452218) baseStart_7452218 baseEnd_7452218 := by
    simpa [prefixWord, tailWord_7452218, baseEnd_7452218] using wordTrace_append hprefix tailTrace_7452218
  have hstable : (prefixWord ++ tailWord_7452218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452218).length < 2 ^ (prefixWord ++ tailWord_7452218).sum := by decide
  have hdescent : baseEnd_7452218 < baseStart_7452218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452238 : List Nat := [4, 1, 1, 1, 1, 2, 1, 5, 7]
def baseStart_7452238 : Nat := 118140960795 + 7452238 * 2 ^ 59
def prefixEnd_7452238 : Nat := 4983230072969 + 3 ^ 40 * 7452238 * 2
def baseEnd_7452238 : Nat := 425175560633413257583643

theorem tailTrace_7452238 : CollatzResearch.WordTrace tailWord_7452238 prefixEnd_7452238 425175560633413257583643 := by
  unfold tailWord_7452238
  simp only [CollatzResearch.WordTrace]
  refine ⟨33975681196977742720928671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181203633050547961178286245 33975681196977742720928671)
  ·
    refine ⟨50963521795466614081393007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33975681196977742720928671 50963521795466614081393007)
    ·
      refine ⟨76445282693199921122089511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50963521795466614081393007 76445282693199921122089511)
      ·
        refine ⟨114667924039799881683134267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76445282693199921122089511 114667924039799881683134267)
        ·
          refine ⟨172001886059699822524701401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114667924039799881683134267 172001886059699822524701401)
          ·
            refine ⟨129001414544774866893526051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172001886059699822524701401 129001414544774866893526051)
            ·
              refine ⟨193502121817162300340289077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129001414544774866893526051 193502121817162300340289077)
              ·
                refine ⟨18140823920358965656902101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 193502121817162300340289077 18140823920358965656902101)
                ·
                  refine ⟨425175560633413257583643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18140823920358965656902101 425175560633413257583643)
                  ·
                    rfl

theorem cell23_7452238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_7452238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452238 prefixEnd_7452238 := by exact prefixLift 7452238
  have htrace : WordTrace (prefixWord ++ tailWord_7452238) baseStart_7452238 baseEnd_7452238 := by
    simpa [prefixWord, tailWord_7452238, baseEnd_7452238] using wordTrace_append hprefix tailTrace_7452238
  have hstable : (prefixWord ++ tailWord_7452238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452238).length < 2 ^ (prefixWord ++ tailWord_7452238).sum := by decide
  have hdescent : baseEnd_7452238 < baseStart_7452238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452272 : List Nat := [2, 1, 1, 1, 6, 2, 2, 3, 5]
def baseStart_7452272 : Nat := 118140960795 + 7452272 * 2 ^ 59
def prefixEnd_7452272 : Nat := 4983230072969 + 3 ^ 40 * 7452272 * 2
def baseEnd_7452272 : Nat := 425177500449219131691959

theorem tailTrace_7452272 : CollatzResearch.WordTrace tailWord_7452272 prefixEnd_7452272 425177500449219131691959 := by
  unfold tailWord_7452272
  simp only [CollatzResearch.WordTrace]
  refine ⟨135903344828849382787083535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181204459771799177049444713 135903344828849382787083535)
  ·
    refine ⟨203855017243274074180625303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135903344828849382787083535 203855017243274074180625303)
    ·
      refine ⟨305782525864911111270937955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203855017243274074180625303 305782525864911111270937955)
      ·
        refine ⟨458673788797366666906406933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305782525864911111270937955 458673788797366666906406933)
        ·
          refine ⟨21500333849876562511237825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 458673788797366666906406933 21500333849876562511237825)
          ·
            refine ⟨16125250387407421883428369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21500333849876562511237825 16125250387407421883428369)
            ·
              refine ⟨12093937790555566412571277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16125250387407421883428369 12093937790555566412571277)
              ·
                refine ⟨4535226671458337404714229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12093937790555566412571277 4535226671458337404714229)
                ·
                  refine ⟨425177500449219131691959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4535226671458337404714229 425177500449219131691959)
                  ·
                    rfl

theorem cell23_7452272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3, 5].length) (baseStart_7452272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452272 prefixEnd_7452272 := by exact prefixLift 7452272
  have htrace : WordTrace (prefixWord ++ tailWord_7452272) baseStart_7452272 baseEnd_7452272 := by
    simpa [prefixWord, tailWord_7452272, baseEnd_7452272] using wordTrace_append hprefix tailTrace_7452272
  have hstable : (prefixWord ++ tailWord_7452272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452272).length < 2 ^ (prefixWord ++ tailWord_7452272).sum := by decide
  have hdescent : baseEnd_7452272 < baseStart_7452272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452305 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 1, 6, 2]
def baseStart_7452305 : Nat := 118140960795 + 7452305 * 2 ^ 59
def prefixEnd_7452305 : Nat := 4983230072969 + 3 ^ 40 * 7452305 * 2
def baseEnd_7452305 : Nat := 3826614448904570556114979

theorem tailTrace_7452305 : CollatzResearch.WordTrace tailWord_7452305 prefixEnd_7452305 3826614448904570556114979 := by
  unfold tailWord_7452305
  simp only [CollatzResearch.WordTrace]
  refine ⟨271807893266579212210118369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181205262177719474806745579 271807893266579212210118369)
  ·
    refine ⟨203855919949934409157588777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271807893266579212210118369 203855919949934409157588777)
    ·
      refine ⟨152891939962450806868191583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203855919949934409157588777 152891939962450806868191583)
      ·
        refine ⟨229337909943676210302287375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152891939962450806868191583 229337909943676210302287375)
        ·
          refine ⟨344006864915514315453431063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229337909943676210302287375 344006864915514315453431063)
          ·
            refine ⟨516010297373271473180146595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344006864915514315453431063 516010297373271473180146595)
            ·
              refine ⟨774015446059907209770219893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516010297373271473180146595 774015446059907209770219893)
              ·
                refine ⟨72563948068116300915958115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 774015446059907209770219893 72563948068116300915958115)
                ·
                  refine ⟨108845922102174451373937173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72563948068116300915958115 108845922102174451373937173)
                  ·
                    refine ⟨5102152598539427408153305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108845922102174451373937173 5102152598539427408153305)
                    ·
                      refine ⟨3826614448904570556114979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5102152598539427408153305 3826614448904570556114979)
                      ·
                        rfl

theorem cell23_7452305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 6, 2].length) (baseStart_7452305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452305 prefixEnd_7452305 := by exact prefixLift 7452305
  have htrace : WordTrace (prefixWord ++ tailWord_7452305) baseStart_7452305 baseEnd_7452305 := by
    simpa [prefixWord, tailWord_7452305, baseEnd_7452305] using wordTrace_append hprefix tailTrace_7452305
  have hstable : (prefixWord ++ tailWord_7452305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452305).length < 2 ^ (prefixWord ++ tailWord_7452305).sum := by decide
  have hdescent : baseEnd_7452305 < baseStart_7452305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452325 : List Nat := [1, 3, 1, 2, 1, 2, 4, 1, 1, 4, 3]
def baseStart_7452325 : Nat := 118140960795 + 7452325 * 2 ^ 59
def prefixEnd_7452325 : Nat := 4983230072969 + 3 ^ 40 * 7452325 * 2
def baseEnd_7452325 : Nat := 3826624718517660477864887

theorem tailTrace_7452325 : CollatzResearch.WordTrace tailWord_7452325 prefixEnd_7452325 3826624718517660477864887 := by
  unfold tailWord_7452325
  simp only [CollatzResearch.WordTrace]
  refine ⟨271808622726506755625846429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181205748484337837083897619 271808622726506755625846429)
  ·
    refine ⟨101928233522440033359692411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271808622726506755625846429 101928233522440033359692411)
    ·
      refine ⟨152892350283660050039538617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101928233522440033359692411 152892350283660050039538617)
      ·
        refine ⟨114669262712745037529653963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152892350283660050039538617 114669262712745037529653963)
        ·
          refine ⟨172003894069117556294480945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114669262712745037529653963 172003894069117556294480945)
          ·
            refine ⟨129002920551838167220860709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172003894069117556294480945 129002920551838167220860709)
            ·
              refine ⟨24188047603469656353911383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129002920551838167220860709 24188047603469656353911383)
              ·
                refine ⟨36282071405204484530867075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24188047603469656353911383 36282071405204484530867075)
                ·
                  refine ⟨54423107107806726796300613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36282071405204484530867075 54423107107806726796300613)
                  ·
                    refine ⟨10204332582713761274306365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54423107107806726796300613 10204332582713761274306365)
                    ·
                      refine ⟨3826624718517660477864887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10204332582713761274306365 3826624718517660477864887)
                      ·
                        rfl

theorem cell23_7452325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_7452325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452325 prefixEnd_7452325 := by exact prefixLift 7452325
  have htrace : WordTrace (prefixWord ++ tailWord_7452325) baseStart_7452325 baseEnd_7452325 := by
    simpa [prefixWord, tailWord_7452325, baseEnd_7452325] using wordTrace_append hprefix tailTrace_7452325
  have hstable : (prefixWord ++ tailWord_7452325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452325).length < 2 ^ (prefixWord ++ tailWord_7452325).sum := by decide
  have hdescent : baseEnd_7452325 < baseStart_7452325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452362 : List Nat := [3, 1, 2, 1, 5, 1, 1, 3, 6]
def baseStart_7452362 : Nat := 118140960795 + 7452362 * 2 ^ 59
def prefixEnd_7452362 : Nat := 4983230072969 + 3 ^ 40 * 7452362 * 2
def baseEnd_7452362 : Nat := 425182635255764092566913

theorem tailTrace_7452362 : CollatzResearch.WordTrace tailWord_7452362 prefixEnd_7452362 425182635255764092566913 := by
  unfold tailWord_7452362
  simp only [CollatzResearch.WordTrace]
  refine ⟨67952493056843177736235835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181206648151581807296628893 67952493056843177736235835)
  ·
    refine ⟨101928739585264766604353753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67952493056843177736235835 101928739585264766604353753)
    ·
      refine ⟨76446554688948574953265315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101928739585264766604353753 76446554688948574953265315)
      ·
        refine ⟨114669832033422862429897973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76446554688948574953265315 114669832033422862429897973)
        ·
          refine ⟨10750296753133393352802935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114669832033422862429897973 10750296753133393352802935)
          ·
            refine ⟨16125445129700090029204403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10750296753133393352802935 16125445129700090029204403)
            ·
              refine ⟨24188167694550135043806605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16125445129700090029204403 24188167694550135043806605)
              ·
                refine ⟨9070562885456300641427477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24188167694550135043806605 9070562885456300641427477)
                ·
                  refine ⟨425182635255764092566913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9070562885456300641427477 425182635255764092566913)
                  ·
                    rfl

theorem cell23_7452362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 6].length) (baseStart_7452362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452362 prefixEnd_7452362 := by exact prefixLift 7452362
  have htrace : WordTrace (prefixWord ++ tailWord_7452362) baseStart_7452362 baseEnd_7452362 := by
    simpa [prefixWord, tailWord_7452362, baseEnd_7452362] using wordTrace_append hprefix tailTrace_7452362
  have hstable : (prefixWord ++ tailWord_7452362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452362).length < 2 ^ (prefixWord ++ tailWord_7452362).sum := by decide
  have hdescent : baseEnd_7452362 < baseStart_7452362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452368 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 7]
def baseStart_7452368 : Nat := 118140960795 + 7452368 * 2 ^ 59
def prefixEnd_7452368 : Nat := 4983230072969 + 3 ^ 40 * 7452368 * 2
def baseEnd_7452368 : Nat := 3826646798185803809627189

theorem tailTrace_7452368 : CollatzResearch.WordTrace tailWord_7452368 prefixEnd_7452368 3826646798185803809627189 := by
  unfold tailWord_7452368
  simp only [CollatzResearch.WordTrace]
  refine ⟨135905095532675486984830879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181206794043567315979774505 135905095532675486984830879)
  ·
    refine ⟨203857643299013230477246319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135905095532675486984830879 203857643299013230477246319)
    ·
      refine ⟨305786464948519845715869479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203857643299013230477246319 305786464948519845715869479)
      ·
        refine ⟨458679697422779768573804219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305786464948519845715869479 458679697422779768573804219)
        ·
          refine ⟨688019546134169652860706329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458679697422779768573804219 688019546134169652860706329)
          ·
            refine ⟨516014659600627239645529747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 688019546134169652860706329 516014659600627239645529747)
            ·
              refine ⟨774021989400940859468294621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516014659600627239645529747 774021989400940859468294621)
              ·
                refine ⟨290258246025352822300610483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 774021989400940859468294621 290258246025352822300610483)
                ·
                  refine ⟨435387369038029233450915725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 290258246025352822300610483 435387369038029233450915725)
                  ·
                    refine ⟨163270263389260962544093397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 435387369038029233450915725 163270263389260962544093397)
                    ·
                      refine ⟨3826646798185803809627189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163270263389260962544093397 3826646798185803809627189)
                      ·
                        rfl

theorem cell23_7452368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_7452368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452368 prefixEnd_7452368 := by exact prefixLift 7452368
  have htrace : WordTrace (prefixWord ++ tailWord_7452368) baseStart_7452368 baseEnd_7452368 := by
    simpa [prefixWord, tailWord_7452368, baseEnd_7452368] using wordTrace_append hprefix tailTrace_7452368
  have hstable : (prefixWord ++ tailWord_7452368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452368).length < 2 ^ (prefixWord ++ tailWord_7452368).sum := by decide
  have hdescent : baseEnd_7452368 < baseStart_7452368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452375 : List Nat := [1, 1, 3, 2, 1, 3, 3, 1, 3, 5]
def baseStart_7452375 : Nat := 118140960795 + 7452375 * 2 ^ 59
def prefixEnd_7452375 : Nat := 4983230072969 + 3 ^ 40 * 7452375 * 2
def baseEnd_7452375 : Nat := 1275550130850128427413219

theorem tailTrace_7452375 : CollatzResearch.WordTrace tailWord_7452375 prefixEnd_7452375 1275550130850128427413219 := by
  unfold tailWord_7452375
  simp only [CollatzResearch.WordTrace]
  refine ⟨271810446376325614165166579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181206964250883742776777719 271810446376325614165166579)
  ·
    refine ⟨407715669564488421247749869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271810446376325614165166579 407715669564488421247749869)
    ·
      refine ⟨152893376086683157967906201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407715669564488421247749869 152893376086683157967906201)
      ·
        refine ⟨114670032065012368475929651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152893376086683157967906201 114670032065012368475929651)
        ·
          refine ⟨172005048097518552713894477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114670032065012368475929651 172005048097518552713894477)
          ·
            refine ⟨64501893036569457267710429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172005048097518552713894477 64501893036569457267710429)
            ·
              refine ⟨24188209888713546475391411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64501893036569457267710429 24188209888713546475391411)
              ·
                refine ⟨36282314833070319713087117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24188209888713546475391411 36282314833070319713087117)
                ·
                  refine ⟨13605868062401369892407669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36282314833070319713087117 13605868062401369892407669)
                  ·
                    refine ⟨1275550130850128427413219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13605868062401369892407669 1275550130850128427413219)
                    ·
                      rfl

theorem cell23_7452375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 5].length) (baseStart_7452375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452375 prefixEnd_7452375 := by exact prefixLift 7452375
  have htrace : WordTrace (prefixWord ++ tailWord_7452375) baseStart_7452375 baseEnd_7452375 := by
    simpa [prefixWord, tailWord_7452375, baseEnd_7452375] using wordTrace_append hprefix tailTrace_7452375
  have hstable : (prefixWord ++ tailWord_7452375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452375).length < 2 ^ (prefixWord ++ tailWord_7452375).sum := by decide
  have hdescent : baseEnd_7452375 < baseStart_7452375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452415 : List Nat := [1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 5]
def baseStart_7452415 : Nat := 118140960795 + 7452415 * 2 ^ 59
def prefixEnd_7452415 : Nat := 4983230072969 + 3 ^ 40 * 7452415 * 2
def baseEnd_7452415 : Nat := 3826670931776565125739473

theorem tailTrace_7452415 : CollatzResearch.WordTrace tailWord_7452415 prefixEnd_7452415 3826670931776565125739473 := by
  unfold tailWord_7452415
  simp only [CollatzResearch.WordTrace]
  refine ⟨271811905296180700996622699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181207936864120467331081799 271811905296180700996622699)
  ·
    refine ⟨407717857944271051494934049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271811905296180700996622699 407717857944271051494934049)
    ·
      refine ⟨305788393458203288621200537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407717857944271051494934049 305788393458203288621200537)
      ·
        refine ⟨229341295093652466465900403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305788393458203288621200537 229341295093652466465900403)
        ·
          refine ⟨344011942640478699698850605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229341295093652466465900403 344011942640478699698850605)
          ·
            refine ⟨129004478490179512387068977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344011942640478699698850605 129004478490179512387068977)
            ·
              refine ⟨96753358867634634290301733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129004478490179512387068977 96753358867634634290301733)
              ·
                refine ⟨18141254787681493929431575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96753358867634634290301733 18141254787681493929431575)
                ·
                  refine ⟨27211882181522240894147363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18141254787681493929431575 27211882181522240894147363)
                  ·
                    refine ⟨40817823272283361341221045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27211882181522240894147363 40817823272283361341221045)
                    ·
                      refine ⟨3826670931776565125739473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40817823272283361341221045 3826670931776565125739473)
                      ·
                        rfl

theorem cell23_7452415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_7452415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452415 prefixEnd_7452415 := by exact prefixLift 7452415
  have htrace : WordTrace (prefixWord ++ tailWord_7452415) baseStart_7452415 baseEnd_7452415 := by
    simpa [prefixWord, tailWord_7452415, baseEnd_7452415] using wordTrace_append hprefix tailTrace_7452415
  have hstable : (prefixWord ++ tailWord_7452415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452415).length < 2 ^ (prefixWord ++ tailWord_7452415).sum := by decide
  have hdescent : baseEnd_7452415 < baseStart_7452415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452442 : List Nat := [3, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4]
def baseStart_7452442 : Nat := 118140960795 + 7452442 * 2 ^ 59
def prefixEnd_7452442 : Nat := 4983230072969 + 3 ^ 40 * 7452442 * 2
def baseEnd_7452442 : Nat := 3826684795754236520101849

theorem tailTrace_7452442 : CollatzResearch.WordTrace tailWord_7452442 prefixEnd_7452442 3826684795754236520101849 := by
  unfold tailWord_7452442
  simp only [CollatzResearch.WordTrace]
  refine ⟨67953222516770721151963895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181208593378055256405237053 67953222516770721151963895)
  ·
    refine ⟨101929833775156081727945843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67953222516770721151963895 101929833775156081727945843)
    ·
      refine ⟨152894750662734122591918765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101929833775156081727945843 152894750662734122591918765)
      ·
        refine ⟨57335531498525295971969537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152894750662734122591918765 57335531498525295971969537)
        ·
          refine ⟨43001648623893971978977153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57335531498525295971969537 43001648623893971978977153)
          ·
            refine ⟨32251236467920478984232865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43001648623893971978977153 32251236467920478984232865)
            ·
              refine ⟨24188427350940359238174649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32251236467920478984232865 24188427350940359238174649)
              ·
                refine ⟨18141320513205269428630987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24188427350940359238174649 18141320513205269428630987)
                ·
                  refine ⟨27211980769807904142946481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18141320513205269428630987 27211980769807904142946481)
                  ·
                    refine ⟨20408985577355928107209861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27211980769807904142946481 20408985577355928107209861)
                    ·
                      refine ⟨3826684795754236520101849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20408985577355928107209861 3826684795754236520101849)
                      ·
                        rfl

theorem cell23_7452442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_7452442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452442 prefixEnd_7452442 := by exact prefixLift 7452442
  have htrace : WordTrace (prefixWord ++ tailWord_7452442) baseStart_7452442 baseEnd_7452442 := by
    simpa [prefixWord, tailWord_7452442, baseEnd_7452442] using wordTrace_append hprefix tailTrace_7452442
  have hstable : (prefixWord ++ tailWord_7452442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452442).length < 2 ^ (prefixWord ++ tailWord_7452442).sum := by decide
  have hdescent : baseEnd_7452442 < baseStart_7452442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452449 : List Nat := [1, 2, 3, 2, 1, 4, 1, 3, 1, 2, 3]
def baseStart_7452449 : Nat := 118140960795 + 7452449 * 2 ^ 59
def prefixEnd_7452449 : Nat := 4983230072969 + 3 ^ 40 * 7452449 * 2
def baseEnd_7452449 : Nat := 3826688390118817992714317

theorem tailTrace_7452449 : CollatzResearch.WordTrace tailWord_7452449 prefixEnd_7452449 3826688390118817992714317 := by
  unfold tailWord_7452449
  simp only [CollatzResearch.WordTrace]
  refine ⟨271813145378057524803360401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181208763585371683202240267 271813145378057524803360401)
  ·
    refine ⟨203859859033543143602520301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271813145378057524803360401 203859859033543143602520301)
    ·
      refine ⟨76447447137578678850945113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203859859033543143602520301 76447447137578678850945113)
      ·
        refine ⟨57335585353184009138208835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76447447137578678850945113 57335585353184009138208835)
        ·
          refine ⟨86003378029776013707313253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57335585353184009138208835 86003378029776013707313253)
          ·
            refine ⟨16125633380583002570121235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86003378029776013707313253 16125633380583002570121235)
            ·
              refine ⟨24188450070874503855181853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16125633380583002570121235 24188450070874503855181853)
              ·
                refine ⟨9070668776577938945693195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24188450070874503855181853 9070668776577938945693195)
                ·
                  refine ⟨13606003164866908418539793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9070668776577938945693195 13606003164866908418539793)
                  ·
                    refine ⟨10204502373650181313904845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13606003164866908418539793 10204502373650181313904845)
                    ·
                      refine ⟨3826688390118817992714317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10204502373650181313904845 3826688390118817992714317)
                      ·
                        rfl

theorem cell23_7452449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_7452449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452449 prefixEnd_7452449 := by exact prefixLift 7452449
  have htrace : WordTrace (prefixWord ++ tailWord_7452449) baseStart_7452449 baseEnd_7452449 := by
    simpa [prefixWord, tailWord_7452449, baseEnd_7452449] using wordTrace_append hprefix tailTrace_7452449
  have hstable : (prefixWord ++ tailWord_7452449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452449).length < 2 ^ (prefixWord ++ tailWord_7452449).sum := by decide
  have hdescent : baseEnd_7452449 < baseStart_7452449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452456 : List Nat := [2, 1, 5, 1, 1, 4, 1, 2, 2, 4]
def baseStart_7452456 : Nat := 118140960795 + 7452456 * 2 ^ 59
def prefixEnd_7452456 : Nat := 4983230072969 + 3 ^ 40 * 7452456 * 2
def baseEnd_7452456 : Nat := 1275563994827799821775595

theorem tailTrace_7452456 : CollatzResearch.WordTrace tailWord_7452456 prefixEnd_7452456 1275563994827799821775595 := by
  unfold tailWord_7452456
  simp only [CollatzResearch.WordTrace]
  refine ⟨135906700344516082499432611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181208933792688109999243481 135906700344516082499432611)
  ·
    refine ⟨203860050516774123749148917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135906700344516082499432611 203860050516774123749148917)
    ·
      refine ⟨19111879735947574101482711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 203860050516774123749148917 19111879735947574101482711)
      ·
        refine ⟨28667819603921361152224067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19111879735947574101482711 28667819603921361152224067)
        ·
          refine ⟨43001729405882041728336101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28667819603921361152224067 43001729405882041728336101)
          ·
            refine ⟨8062824263602882824063019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43001729405882041728336101 8062824263602882824063019)
            ·
              refine ⟨12094236395404324236094529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8062824263602882824063019 12094236395404324236094529)
              ·
                refine ⟨9070677296553243177070897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12094236395404324236094529 9070677296553243177070897)
                ·
                  refine ⟨6803007972414932382803173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9070677296553243177070897 6803007972414932382803173)
                  ·
                    refine ⟨1275563994827799821775595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6803007972414932382803173 1275563994827799821775595)
                    ·
                      rfl

theorem cell23_7452456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_7452456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452456 prefixEnd_7452456 := by exact prefixLift 7452456
  have htrace : WordTrace (prefixWord ++ tailWord_7452456) baseStart_7452456 baseEnd_7452456 := by
    simpa [prefixWord, tailWord_7452456, baseEnd_7452456] using wordTrace_append hprefix tailTrace_7452456
  have hstable : (prefixWord ++ tailWord_7452456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452456).length < 2 ^ (prefixWord ++ tailWord_7452456).sum := by decide
  have hdescent : baseEnd_7452456 < baseStart_7452456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452473 : List Nat := [1, 2, 1, 7, 1, 1, 3, 1, 2, 4]
def baseStart_7452473 : Nat := 118140960795 + 7452473 * 2 ^ 59
def prefixEnd_7452473 : Nat := 4983230072969 + 3 ^ 40 * 7452473 * 2
def baseEnd_7452473 : Nat := 1275566904551508632938069

theorem tailTrace_7452473 : CollatzResearch.WordTrace tailWord_7452473 prefixEnd_7452473 1275566904551508632938069 := by
  unfold tailWord_7452473
  simp only [CollatzResearch.WordTrace]
  refine ⟨271814020729970576902234073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181209347153313717934822715 271814020729970576902234073)
  ·
    refine ⟨203860515547477932676675555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271814020729970576902234073 203860515547477932676675555)
    ·
      refine ⟨305790773321216899015013333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203860515547477932676675555 305790773321216899015013333)
      ·
        refine ⟨7166971249716021070664375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 305790773321216899015013333 7166971249716021070664375)
        ·
          refine ⟨10750456874574031605996563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7166971249716021070664375 10750456874574031605996563)
          ·
            refine ⟨16125685311861047408994845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10750456874574031605996563 16125685311861047408994845)
            ·
              refine ⟨6047131991947892778373067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16125685311861047408994845 6047131991947892778373067)
              ·
                refine ⟨9070697987921839167559601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6047131991947892778373067 9070697987921839167559601)
                ·
                  refine ⟨6803023490941379375669701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9070697987921839167559601 6803023490941379375669701)
                  ·
                    refine ⟨1275566904551508632938069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6803023490941379375669701 1275566904551508632938069)
                    ·
                      rfl

theorem cell23_7452473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 2, 4].length) (baseStart_7452473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452473 prefixEnd_7452473 := by exact prefixLift 7452473
  have htrace : WordTrace (prefixWord ++ tailWord_7452473) baseStart_7452473 baseEnd_7452473 := by
    simpa [prefixWord, tailWord_7452473, baseEnd_7452473] using wordTrace_append hprefix tailTrace_7452473
  have hstable : (prefixWord ++ tailWord_7452473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452473).length < 2 ^ (prefixWord ++ tailWord_7452473).sum := by decide
  have hdescent : baseEnd_7452473 < baseStart_7452473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452486 : List Nat := [6, 1, 1, 2, 1, 1, 4, 7]
def baseStart_7452486 : Nat := 118140960795 + 7452486 * 2 ^ 59
def prefixEnd_7452486 : Nat := 4983230072969 + 3 ^ 40 * 7452486 * 2
def baseEnd_7452486 : Nat := 141729903292704975850061

theorem tailTrace_7452486 : CollatzResearch.WordTrace tailWord_7452486 prefixEnd_7452486 141729903292704975850061 := by
  unfold tailWord_7452486
  simp only [CollatzResearch.WordTrace]
  refine ⟨8494202964966358753826791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 181209663252615653414971541 8494202964966358753826791)
  ·
    refine ⟨12741304447449538130740187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8494202964966358753826791 12741304447449538130740187)
    ·
      refine ⟨19111956671174307196110281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12741304447449538130740187 19111956671174307196110281)
      ·
        refine ⟨14333967503380730397082711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19111956671174307196110281 14333967503380730397082711)
        ·
          refine ⟨21500951255071095595624067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14333967503380730397082711 21500951255071095595624067)
          ·
            refine ⟨32251426882606643393436101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21500951255071095595624067 32251426882606643393436101)
            ·
              refine ⟨6047142540488745636269269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32251426882606643393436101 6047142540488745636269269)
              ·
                refine ⟨141729903292704975850061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6047142540488745636269269 141729903292704975850061)
                ·
                  rfl

theorem cell23_7452486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_7452486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452486 prefixEnd_7452486 := by exact prefixLift 7452486
  have htrace : WordTrace (prefixWord ++ tailWord_7452486) baseStart_7452486 baseEnd_7452486 := by
    simpa [prefixWord, tailWord_7452486, baseEnd_7452486] using wordTrace_append hprefix tailTrace_7452486
  have hstable : (prefixWord ++ tailWord_7452486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452486).length < 2 ^ (prefixWord ++ tailWord_7452486).sum := by decide
  have hdescent : baseEnd_7452486 < baseStart_7452486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452606 : List Nat := [4, 2, 1, 1, 1, 5, 1, 1, 2, 5]
def baseStart_7452606 : Nat := 118140960795 + 7452606 * 2 ^ 59
def prefixEnd_7452606 : Nat := 4983230072969 + 3 ^ 40 * 7452606 * 2
def baseEnd_7452606 : Nat := 1275589668860524626150365

theorem tailTrace_7452606 : CollatzResearch.WordTrace tailWord_7452606 prefixEnd_7452606 1275589668860524626150365 := by
  unfold tailWord_7452606
  simp only [CollatzResearch.WordTrace]
  refine ⟨33977358954811092577103209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181212581092325827077883781 33977358954811092577103209)
  ·
    refine ⟨25483019216108319432827407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33977358954811092577103209 25483019216108319432827407)
    ·
      refine ⟨38224528824162479149241111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25483019216108319432827407 38224528824162479149241111)
      ·
        refine ⟨57336793236243718723861667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38224528824162479149241111 57336793236243718723861667)
        ·
          refine ⟨86005189854365578085792501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57336793236243718723861667 86005189854365578085792501)
          ·
            refine ⟨8062986548846772945543047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86005189854365578085792501 8062986548846772945543047)
            ·
              refine ⟨12094479823270159418314571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8062986548846772945543047 12094479823270159418314571)
              ·
                refine ⟨18141719734905239127471857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12094479823270159418314571 18141719734905239127471857)
                ·
                  refine ⟨13606289801178929345603893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18141719734905239127471857 13606289801178929345603893)
                  ·
                    refine ⟨1275589668860524626150365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13606289801178929345603893 1275589668860524626150365)
                    ·
                      rfl

theorem cell23_7452606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_7452606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452606 prefixEnd_7452606 := by exact prefixLift 7452606
  have htrace : WordTrace (prefixWord ++ tailWord_7452606) baseStart_7452606 baseEnd_7452606 := by
    simpa [prefixWord, tailWord_7452606, baseEnd_7452606] using wordTrace_append hprefix tailTrace_7452606
  have hstable : (prefixWord ++ tailWord_7452606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452606).length < 2 ^ (prefixWord ++ tailWord_7452606).sum := by decide
  have hdescent : baseEnd_7452606 < baseStart_7452606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452622 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6]
def baseStart_7452622 : Nat := 118140960795 + 7452622 * 2 ^ 59
def prefixEnd_7452622 : Nat := 4983230072969 + 3 ^ 40 * 7452622 * 2
def baseEnd_7452622 : Nat := 3826777222272045815851021

theorem tailTrace_7452622 : CollatzResearch.WordTrace tailWord_7452622 prefixEnd_7452622 3826777222272045815851021 := by
  unfold tailWord_7452622
  simp only [CollatzResearch.WordTrace]
  refine ⟨33977431900803846918676015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181212970137620516899605413 33977431900803846918676015)
  ·
    refine ⟨50966147851205770378014023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33977431900803846918676015 50966147851205770378014023)
    ·
      refine ⟨76449221776808655567021035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50966147851205770378014023 76449221776808655567021035)
      ·
        refine ⟨114673832665212983350531553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76449221776808655567021035 114673832665212983350531553)
        ·
          refine ⟨86005374498909737512898665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114673832665212983350531553 86005374498909737512898665)
          ·
            refine ⟨64504030874182303134673999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86005374498909737512898665 64504030874182303134673999)
            ·
              refine ⟨96756046311273454702010999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64504030874182303134673999 96756046311273454702010999)
              ·
                refine ⟨145134069466910182053016499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96756046311273454702010999 145134069466910182053016499)
                ·
                  refine ⟨217701104200365273079524749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145134069466910182053016499 217701104200365273079524749)
                  ·
                    refine ⟨81637914075136977404821781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 217701104200365273079524749 81637914075136977404821781)
                    ·
                      refine ⟨3826777222272045815851021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81637914075136977404821781 3826777222272045815851021)
                      ·
                        rfl

theorem cell23_7452622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_7452622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452622 prefixEnd_7452622 := by exact prefixLift 7452622
  have htrace : WordTrace (prefixWord ++ tailWord_7452622) baseStart_7452622 baseEnd_7452622 := by
    simpa [prefixWord, tailWord_7452622, baseEnd_7452622] using wordTrace_append hprefix tailTrace_7452622
  have hstable : (prefixWord ++ tailWord_7452622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452622).length < 2 ^ (prefixWord ++ tailWord_7452622).sum := by decide
  have hdescent : baseEnd_7452622 < baseStart_7452622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452632 : List Nat := [2, 1, 2, 2, 2, 2, 3, 1, 8]
def baseStart_7452632 : Nat := 118140960795 + 7452632 * 2 ^ 59
def prefixEnd_7452632 : Nat := 4983230072969 + 3 ^ 40 * 7452632 * 2
def baseEnd_7452632 : Nat := 425198039675398975191775

theorem tailTrace_7452632 : CollatzResearch.WordTrace tailWord_7452632 prefixEnd_7452632 425198039675398975191775 := by
  unfold tailWord_7452632
  simp only [CollatzResearch.WordTrace]
  refine ⟨135909909968197273528636075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181213213290929698038181433 135909909968197273528636075)
  ·
    refine ⟨203864864952295910292954113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135909909968197273528636075 203864864952295910292954113)
    ·
      refine ⟨152898648714221932719715585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203864864952295910292954113 152898648714221932719715585)
      ·
        refine ⟨114673986535666449539786689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152898648714221932719715585 114673986535666449539786689)
        ·
          refine ⟨86005489901749837154840017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114673986535666449539786689 86005489901749837154840017)
          ·
            refine ⟨64504117426312377866130013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86005489901749837154840017 64504117426312377866130013)
            ·
              refine ⟨24189044034867141699798755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64504117426312377866130013 24189044034867141699798755)
              ·
                refine ⟨36283566052300712549698133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24189044034867141699798755 36283566052300712549698133)
                ·
                  refine ⟨425198039675398975191775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36283566052300712549698133 425198039675398975191775)
                  ·
                    rfl

theorem cell23_7452632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 8].length) (baseStart_7452632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452632 prefixEnd_7452632 := by exact prefixLift 7452632
  have htrace : WordTrace (prefixWord ++ tailWord_7452632) baseStart_7452632 baseEnd_7452632 := by
    simpa [prefixWord, tailWord_7452632, baseEnd_7452632] using wordTrace_append hprefix tailTrace_7452632
  have hstable : (prefixWord ++ tailWord_7452632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452632).length < 2 ^ (prefixWord ++ tailWord_7452632).sum := by decide
  have hdescent : baseEnd_7452632 < baseStart_7452632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452670 : List Nat := [4, 2, 2, 2, 1, 1, 3, 3, 1, 4]
def baseStart_7452670 : Nat := 118140960795 + 7452670 * 2 ^ 59
def prefixEnd_7452670 : Nat := 4983230072969 + 3 ^ 40 * 7452670 * 2
def baseEnd_7452670 : Nat := 1275600623114487209350267

theorem tailTrace_7452670 : CollatzResearch.WordTrace tailWord_7452670 prefixEnd_7452670 1275600623114487209350267 := by
  unfold tailWord_7452670
  simp only [CollatzResearch.WordTrace]
  refine ⟨33977650738782109943394433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181214137273504586364770309 33977650738782109943394433)
  ·
    refine ⟨25483238054086582457545825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33977650738782109943394433 25483238054086582457545825)
    ·
      refine ⟨19112428540564936843159369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25483238054086582457545825 19112428540564936843159369)
      ·
        refine ⟨14334321405423702632369527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19112428540564936843159369 14334321405423702632369527)
        ·
          refine ⟨21501482108135553948554291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14334321405423702632369527 21501482108135553948554291)
          ·
            refine ⟨32252223162203330922831437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21501482108135553948554291 32252223162203330922831437)
            ·
              refine ⟨12094583685826249096061789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32252223162203330922831437 12094583685826249096061789)
              ·
                refine ⟨4535468882184843411023171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12094583685826249096061789 4535468882184843411023171)
                ·
                  refine ⟨6803203323277265116534757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4535468882184843411023171 6803203323277265116534757)
                  ·
                    refine ⟨1275600623114487209350267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6803203323277265116534757 1275600623114487209350267)
                    ·
                      rfl

theorem cell23_7452670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_7452670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452670 prefixEnd_7452670 := by exact prefixLift 7452670
  have htrace : WordTrace (prefixWord ++ tailWord_7452670) baseStart_7452670 baseEnd_7452670 := by
    simpa [prefixWord, tailWord_7452670, baseEnd_7452670] using wordTrace_append hprefix tailTrace_7452670
  have hstable : (prefixWord ++ tailWord_7452670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452670).length < 2 ^ (prefixWord ++ tailWord_7452670).sum := by decide
  have hdescent : baseEnd_7452670 < baseStart_7452670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452699 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 2, 6, 2]
def baseStart_7452699 : Nat := 118140960795 + 7452699 * 2 ^ 59
def prefixEnd_7452699 : Nat := 4983230072969 + 3 ^ 40 * 7452699 * 2
def baseEnd_7452699 : Nat := 3826816760282442014588167

theorem tailTrace_7452699 : CollatzResearch.WordTrace tailWord_7452699 prefixEnd_7452699 3826816760282442014588167 := by
  unfold tailWord_7452699
  simp only [CollatzResearch.WordTrace]
  refine ⟨271822263627151817499961151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181214842418101211666640767 271822263627151817499961151)
  ·
    refine ⟨407733395440727726249941727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271822263627151817499961151 407733395440727726249941727)
    ·
      refine ⟨611600093161091589374912591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407733395440727726249941727 611600093161091589374912591)
      ·
        refine ⟨917400139741637384062368887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611600093161091589374912591 917400139741637384062368887)
        ·
          refine ⟨1376100209612456076093553331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 917400139741637384062368887 1376100209612456076093553331)
          ·
            refine ⟨2064150314418684114140329997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1376100209612456076093553331 2064150314418684114140329997)
            ·
              refine ⟨774056367907006542802623749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2064150314418684114140329997 774056367907006542802623749)
              ·
                refine ⟨145135568982563726775491953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 774056367907006542802623749 145135568982563726775491953)
                ·
                  refine ⟨108851676736922795081618965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145135568982563726775491953 108851676736922795081618965)
                  ·
                    refine ⟨5102422347043256019450889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108851676736922795081618965 5102422347043256019450889)
                    ·
                      refine ⟨3826816760282442014588167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5102422347043256019450889 3826816760282442014588167)
                      ·
                        rfl

theorem cell23_7452699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 6, 2].length) (baseStart_7452699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452699 prefixEnd_7452699 := by exact prefixLift 7452699
  have htrace : WordTrace (prefixWord ++ tailWord_7452699) baseStart_7452699 baseEnd_7452699 := by
    simpa [prefixWord, tailWord_7452699, baseEnd_7452699] using wordTrace_append hprefix tailTrace_7452699
  have hstable : (prefixWord ++ tailWord_7452699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452699).length < 2 ^ (prefixWord ++ tailWord_7452699).sum := by decide
  have hdescent : baseEnd_7452699 < baseStart_7452699 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452726 : List Nat := [5, 1, 2, 1, 1, 1, 3, 2, 1, 6]
def baseStart_7452726 : Nat := 118140960795 + 7452726 * 2 ^ 59
def prefixEnd_7452726 : Nat := 4983230072969 + 3 ^ 40 * 7452726 * 2
def baseEnd_7452726 : Nat := 1275610208086704469650181

theorem tailTrace_7452726 : CollatzResearch.WordTrace tailWord_7452726 prefixEnd_7452726 1275610208086704469650181 := by
  unfold tailWord_7452726
  simp only [CollatzResearch.WordTrace]
  refine ⟨16988953024878375069449627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181215498932036000740796021 16988953024878375069449627)
  ·
    refine ⟨25483429537317562604174441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16988953024878375069449627 25483429537317562604174441)
    ·
      refine ⟨19112572152988171953130831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25483429537317562604174441 19112572152988171953130831)
      ·
        refine ⟨28668858229482257929696247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19112572152988171953130831 28668858229482257929696247)
        ·
          refine ⟨43003287344223386894544371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28668858229482257929696247 43003287344223386894544371)
          ·
            refine ⟨64504931016335080341816557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43003287344223386894544371 64504931016335080341816557)
            ·
              refine ⟨24189349131125655128181209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64504931016335080341816557 24189349131125655128181209)
              ·
                refine ⟨18142011848344241346135907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24189349131125655128181209 18142011848344241346135907)
                ·
                  refine ⟨27213017772516362019203861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18142011848344241346135907 27213017772516362019203861)
                  ·
                    refine ⟨1275610208086704469650181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27213017772516362019203861 1275610208086704469650181)
                    ·
                      rfl

theorem cell23_7452726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_7452726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452726 prefixEnd_7452726 := by exact prefixLift 7452726
  have htrace : WordTrace (prefixWord ++ tailWord_7452726) baseStart_7452726 baseEnd_7452726 := by
    simpa [prefixWord, tailWord_7452726, baseEnd_7452726] using wordTrace_append hprefix tailTrace_7452726
  have hstable : (prefixWord ++ tailWord_7452726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452726).length < 2 ^ (prefixWord ++ tailWord_7452726).sum := by decide
  have hdescent : baseEnd_7452726 < baseStart_7452726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452733 : List Nat := [1, 4, 1, 3, 1, 1, 5, 1, 1, 1, 4]
def baseStart_7452733 : Nat := 118140960795 + 7452733 * 2 ^ 59
def prefixEnd_7452733 : Nat := 4983230072969 + 3 ^ 40 * 7452733 * 2
def baseEnd_7452733 : Nat := 3826834218624694881563011

theorem tailTrace_7452733 : CollatzResearch.WordTrace tailWord_7452733 prefixEnd_7452733 3826834218624694881563011 := by
  unfold tailWord_7452733
  simp only [CollatzResearch.WordTrace]
  refine ⟨271823503709028641306698853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181215669139352427537799235 271823503709028641306698853)
  ·
    refine ⟨50966906945442870245006035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271823503709028641306698853 50966906945442870245006035)
    ·
      refine ⟨76450360418164305367509053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50966906945442870245006035 76450360418164305367509053)
      ·
        refine ⟨28668885156811614512815895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76450360418164305367509053 28668885156811614512815895)
        ·
          refine ⟨43003327735217421769223843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28668885156811614512815895 43003327735217421769223843)
          ·
            refine ⟨64504991602826132653835765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43003327735217421769223843 64504991602826132653835765)
            ·
              refine ⟨6047342962764949936297103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64504991602826132653835765 6047342962764949936297103)
              ·
                refine ⟨9071014444147424904445655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6047342962764949936297103 9071014444147424904445655)
                ·
                  refine ⟨13606521666221137356668483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9071014444147424904445655 13606521666221137356668483)
                  ·
                    refine ⟨20409782499331706035002725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13606521666221137356668483 20409782499331706035002725)
                    ·
                      refine ⟨3826834218624694881563011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20409782499331706035002725 3826834218624694881563011)
                      ·
                        rfl

theorem cell23_7452733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_7452733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452733 prefixEnd_7452733 := by exact prefixLift 7452733
  have htrace : WordTrace (prefixWord ++ tailWord_7452733) baseStart_7452733 baseEnd_7452733 := by
    simpa [prefixWord, tailWord_7452733, baseEnd_7452733] using wordTrace_append hprefix tailTrace_7452733
  have hstable : (prefixWord ++ tailWord_7452733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452733).length < 2 ^ (prefixWord ++ tailWord_7452733).sum := by decide
  have hdescent : baseEnd_7452733 < baseStart_7452733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452736 : List Nat := [2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 5]
def baseStart_7452736 : Nat := 118140960795 + 7452736 * 2 ^ 59
def prefixEnd_7452736 : Nat := 4983230072969 + 3 ^ 40 * 7452736 * 2
def baseEnd_7452736 : Nat := 3826835759066658369825497

theorem tailTrace_7452736 : CollatzResearch.WordTrace tailWord_7452736 prefixEnd_7452736 3826835759066658369825497 := by
  unfold tailWord_7452736
  simp only [CollatzResearch.WordTrace]
  refine ⟨135911806564008886409529031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181215742085345181879372041 135911806564008886409529031)
  ·
    refine ⟨203867709846013329614293547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135911806564008886409529031 203867709846013329614293547)
    ·
      refine ⟨305801564769019994421440321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203867709846013329614293547 305801564769019994421440321)
      ·
        refine ⟨229351173576764995816080241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305801564769019994421440321 229351173576764995816080241)
        ·
          refine ⟨172013380182573746862060181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229351173576764995816080241 172013380182573746862060181)
          ·
            refine ⟨8063127196058144384159071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 172013380182573746862060181 8063127196058144384159071)
            ·
              refine ⟨12094690794087216576238607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8063127196058144384159071 12094690794087216576238607)
              ·
                refine ⟨18142036191130824864357911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12094690794087216576238607 18142036191130824864357911)
                ·
                  refine ⟨27213054286696237296536867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18142036191130824864357911 27213054286696237296536867)
                  ·
                    refine ⟨40819581430044355944805301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27213054286696237296536867 40819581430044355944805301)
                    ·
                      refine ⟨3826835759066658369825497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40819581430044355944805301 3826835759066658369825497)
                      ·
                        rfl

theorem cell23_7452736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 5].length) (baseStart_7452736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452736 prefixEnd_7452736 := by exact prefixLift 7452736
  have htrace : WordTrace (prefixWord ++ tailWord_7452736) baseStart_7452736 baseEnd_7452736 := by
    simpa [prefixWord, tailWord_7452736, baseEnd_7452736] using wordTrace_append hprefix tailTrace_7452736
  have hstable : (prefixWord ++ tailWord_7452736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452736).length < 2 ^ (prefixWord ++ tailWord_7452736).sum := by decide
  have hdescent : baseEnd_7452736 < baseStart_7452736 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452869 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 1, 1, 7]
def baseStart_7452869 : Nat := 118140960795 + 7452869 * 2 ^ 59
def prefixEnd_7452869 : Nat := 4983230072969 + 3 ^ 40 * 7452869 * 2
def baseEnd_7452869 : Nat := 3826904051993706349462385

theorem tailTrace_7452869 : CollatzResearch.WordTrace tailWord_7452869 prefixEnd_7452869 3826904051993706349462385 := by
  unfold tailWord_7452869
  simp only [CollatzResearch.WordTrace]
  refine ⟨271828464036535936533649661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181218976024357291022433107 271828464036535936533649661)
  ·
    refine ⟨101935674013700976200118623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271828464036535936533649661 101935674013700976200118623)
    ·
      refine ⟨152903511020551464300177935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101935674013700976200118623 152903511020551464300177935)
      ·
        refine ⟨229355266530827196450266903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152903511020551464300177935 229355266530827196450266903)
        ·
          refine ⟨344032899796240794675400355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229355266530827196450266903 344032899796240794675400355)
          ·
            refine ⟨516049349694361192013100533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344032899796240794675400355 516049349694361192013100533)
            ·
              refine ⟨48379626533846361751228175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 516049349694361192013100533 48379626533846361751228175)
              ·
                refine ⟨72569439800769542626842263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48379626533846361751228175 72569439800769542626842263)
                ·
                  refine ⟨108854159701154313940263395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72569439800769542626842263 108854159701154313940263395)
                  ·
                    refine ⟨163281239551731470910395093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108854159701154313940263395 163281239551731470910395093)
                    ·
                      refine ⟨3826904051993706349462385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163281239551731470910395093 3826904051993706349462385)
                      ·
                        rfl

theorem cell23_7452869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_7452869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452869 prefixEnd_7452869 := by exact prefixLift 7452869
  have htrace : WordTrace (prefixWord ++ tailWord_7452869) baseStart_7452869 baseEnd_7452869 := by
    simpa [prefixWord, tailWord_7452869, baseEnd_7452869] using wordTrace_append hprefix tailTrace_7452869
  have hstable : (prefixWord ++ tailWord_7452869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452869).length < 2 ^ (prefixWord ++ tailWord_7452869).sum := by decide
  have hdescent : baseEnd_7452869 < baseStart_7452869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452889 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 2, 8]
def baseStart_7452889 : Nat := 118140960795 + 7452889 * 2 ^ 59
def prefixEnd_7452889 : Nat := 4983230072969 + 3 ^ 40 * 7452889 * 2
def baseEnd_7452889 : Nat := 1275638107202265423737431

theorem tailTrace_7452889 : CollatzResearch.WordTrace tailWord_7452889 prefixEnd_7452889 1275638107202265423737431 := by
  unfold tailWord_7452889
  simp only [CollatzResearch.WordTrace]
  refine ⟨271829193496463479949377721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181219462330975653299585147 271829193496463479949377721)
  ·
    refine ⟨203871895122347609962033291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271829193496463479949377721 203871895122347609962033291)
    ·
      refine ⟨305807842683521414943049937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203871895122347609962033291 305807842683521414943049937)
      ·
        refine ⟨229355882012641061207287453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305807842683521414943049937 229355882012641061207287453)
        ·
          refine ⟨86008455754740397952732795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229355882012641061207287453 86008455754740397952732795)
          ·
            refine ⟨129012683632110596929099193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86008455754740397952732795 129012683632110596929099193)
            ·
              refine ⟨96759512724082947696824395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129012683632110596929099193 96759512724082947696824395)
              ·
                refine ⟨145139269086124421545236593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96759512724082947696824395 145139269086124421545236593)
                ·
                  refine ⟨108854451814593316158927445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145139269086124421545236593 108854451814593316158927445)
                  ·
                    refine ⟨1275638107202265423737431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108854451814593316158927445 1275638107202265423737431)
                    ·
                      rfl

theorem cell23_7452889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 8].length) (baseStart_7452889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452889 prefixEnd_7452889 := by exact prefixLift 7452889
  have htrace : WordTrace (prefixWord ++ tailWord_7452889) baseStart_7452889 baseEnd_7452889 := by
    simpa [prefixWord, tailWord_7452889, baseEnd_7452889] using wordTrace_append hprefix tailTrace_7452889
  have hstable : (prefixWord ++ tailWord_7452889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452889).length < 2 ^ (prefixWord ++ tailWord_7452889).sum := by decide
  have hdescent : baseEnd_7452889 < baseStart_7452889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452893 : List Nat := [1, 4, 3, 2, 1, 1, 1, 3, 2, 5]
def baseStart_7452893 : Nat := 118140960795 + 7452893 * 2 ^ 59
def prefixEnd_7452893 : Nat := 4983230072969 + 3 ^ 40 * 7452893 * 2
def baseEnd_7452893 : Nat := 1275638791843138085187425

theorem tailTrace_7452893 : CollatzResearch.WordTrace tailWord_7452893 prefixEnd_7452893 1275638791843138085187425 := by
  unfold tailWord_7452893
  simp only [CollatzResearch.WordTrace]
  refine ⟨271829339388448988632523333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181219559592299325755015555 271829339388448988632523333)
  ·
    refine ⟨50968001135334185368598125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271829339388448988632523333 50968001135334185368598125)
    ·
      refine ⟨19113000425750319513224297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50968001135334185368598125 19113000425750319513224297)
      ·
        refine ⟨14334750319312739634918223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19113000425750319513224297 14334750319312739634918223)
        ·
          refine ⟨21502125478969109452377335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14334750319312739634918223 21502125478969109452377335)
          ·
            refine ⟨32253188218453664178566003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21502125478969109452377335 32253188218453664178566003)
            ·
              refine ⟨48379782327680496267849005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32253188218453664178566003 48379782327680496267849005)
              ·
                refine ⟨18142418372880186100443377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48379782327680496267849005 18142418372880186100443377)
                ·
                  refine ⟨13606813779660139575332533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18142418372880186100443377 13606813779660139575332533)
                  ·
                    refine ⟨1275638791843138085187425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13606813779660139575332533 1275638791843138085187425)
                    ·
                      rfl

theorem cell23_7452893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_7452893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452893 prefixEnd_7452893 := by exact prefixLift 7452893
  have htrace : WordTrace (prefixWord ++ tailWord_7452893) baseStart_7452893 baseEnd_7452893 := by
    simpa [prefixWord, tailWord_7452893, baseEnd_7452893] using wordTrace_append hprefix tailTrace_7452893
  have hstable : (prefixWord ++ tailWord_7452893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452893).length < 2 ^ (prefixWord ++ tailWord_7452893).sum := by decide
  have hdescent : baseEnd_7452893 < baseStart_7452893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452930 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 1, 6, 2]
def baseStart_7452930 : Nat := 118140960795 + 7452930 * 2 ^ 59
def prefixEnd_7452930 : Nat := 4983230072969 + 3 ^ 40 * 7452930 * 2
def baseEnd_7452930 : Nat := 3826935374313630610799605

theorem tailTrace_7452930 : CollatzResearch.WordTrace tailWord_7452930 prefixEnd_7452930 3826935374313630610799605 := by
  unfold tailWord_7452930
  simp only [CollatzResearch.WordTrace]
  refine ⟨67957672222328735987905061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181220459259543295967746829 67957672222328735987905061)
  ·
    refine ⟨12742063541686637997732199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67957672222328735987905061 12742063541686637997732199)
    ·
      refine ⟨19113095312529956996598299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12742063541686637997732199 19113095312529956996598299)
      ·
        refine ⟨28669642968794935494897449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19113095312529956996598299 28669642968794935494897449)
        ·
          refine ⟨21502232226596201621173087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28669642968794935494897449 21502232226596201621173087)
          ·
            refine ⟨32253348339894302431759631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21502232226596201621173087 32253348339894302431759631)
            ·
              refine ⟨48380022509841453647639447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32253348339894302431759631 48380022509841453647639447)
              ·
                refine ⟨72570033764762180471459171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48380022509841453647639447 72570033764762180471459171)
                ·
                  refine ⟨108855050647143270707188757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72570033764762180471459171 108855050647143270707188757)
                  ·
                    refine ⟨5102580499084840814399473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108855050647143270707188757 5102580499084840814399473)
                    ·
                      refine ⟨3826935374313630610799605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5102580499084840814399473 3826935374313630610799605)
                      ·
                        rfl

theorem cell23_7452930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_7452930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452930 prefixEnd_7452930 := by exact prefixLift 7452930
  have htrace : WordTrace (prefixWord ++ tailWord_7452930) baseStart_7452930 baseEnd_7452930 := by
    simpa [prefixWord, tailWord_7452930, baseEnd_7452930] using wordTrace_append hprefix tailTrace_7452930
  have hstable : (prefixWord ++ tailWord_7452930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452930).length < 2 ^ (prefixWord ++ tailWord_7452930).sum := by decide
  have hdescent : baseEnd_7452930 < baseStart_7452930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452963 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 5, 1, 3]
def baseStart_7452963 : Nat := 118140960795 + 7452963 * 2 ^ 59
def prefixEnd_7452963 : Nat := 4983230072969 + 3 ^ 40 * 7452963 * 2
def baseEnd_7452963 : Nat := 3826952319175228981686953

theorem tailTrace_7452963 : CollatzResearch.WordTrace tailWord_7452963 prefixEnd_7452963 3826952319175228981686953 := by
  unfold tailWord_7452963
  simp only [CollatzResearch.WordTrace]
  refine ⟨271831892498195390587571543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181221261665463593725047695 271831892498195390587571543)
  ·
    refine ⟨407747838747293085881357315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271831892498195390587571543 407747838747293085881357315)
    ·
      refine ⟨611621758120939628822035973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407747838747293085881357315 611621758120939628822035973)
      ·
        refine ⟨114679079647676180404131745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 611621758120939628822035973 114679079647676180404131745)
        ·
          refine ⟨86009309735757135303098809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114679079647676180404131745 86009309735757135303098809)
          ·
            refine ⟨64506982301817851477324107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86009309735757135303098809 64506982301817851477324107)
            ·
              refine ⟨96760473452726777215986161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64506982301817851477324107 96760473452726777215986161)
              ·
                refine ⟨72570355089545082911989621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96760473452726777215986161 72570355089545082911989621)
                ·
                  refine ⟨6803470789644851522999027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72570355089545082911989621 6803470789644851522999027)
                  ·
                    refine ⟨10205206184467277284498541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6803470789644851522999027 10205206184467277284498541)
                    ·
                      refine ⟨3826952319175228981686953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10205206184467277284498541 3826952319175228981686953)
                      ·
                        rfl

theorem cell23_7452963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_7452963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452963 prefixEnd_7452963 := by exact prefixLift 7452963
  have htrace : WordTrace (prefixWord ++ tailWord_7452963) baseStart_7452963 baseEnd_7452963 := by
    simpa [prefixWord, tailWord_7452963, baseEnd_7452963] using wordTrace_append hprefix tailTrace_7452963
  have hstable : (prefixWord ++ tailWord_7452963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452963).length < 2 ^ (prefixWord ++ tailWord_7452963).sum := by decide
  have hdescent : baseEnd_7452963 < baseStart_7452963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7452990 : List Nat := [4, 2, 1, 2, 1, 2, 1, 2, 1, 5, 2]
def baseStart_7452990 : Nat := 118140960795 + 7452990 * 2 ^ 59
def prefixEnd_7452990 : Nat := 4983230072969 + 3 ^ 40 * 7452990 * 2
def baseEnd_7452990 : Nat := 3826966183152900376049329

theorem tailTrace_7452990 : CollatzResearch.WordTrace tailWord_7452990 prefixEnd_7452990 3826966183152900376049329 := by
  unfold tailWord_7452990
  simp only [CollatzResearch.WordTrace]
  refine ⟨33979109658637196774850553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181221918179398382799202949 33979109658637196774850553)
  ·
    refine ⟨25484332243977897581137915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33979109658637196774850553 25484332243977897581137915)
    ·
      refine ⟨38226498365966846371706873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25484332243977897581137915 38226498365966846371706873)
      ·
        refine ⟨28669873774475134778780155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38226498365966846371706873 28669873774475134778780155)
        ·
          refine ⟨43004810661712702168170233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28669873774475134778780155 43004810661712702168170233)
          ·
            refine ⟨32253607996284526626127675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43004810661712702168170233 32253607996284526626127675)
            ·
              refine ⟨48380411994426789939191513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32253607996284526626127675 48380411994426789939191513)
              ·
                refine ⟨36285308995820092454393635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48380411994426789939191513 36285308995820092454393635)
                ·
                  refine ⟨54427963493730138681590453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36285308995820092454393635 54427963493730138681590453)
                  ·
                    refine ⟨5102621577537200501399105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54427963493730138681590453 5102621577537200501399105)
                    ·
                      refine ⟨3826966183152900376049329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5102621577537200501399105 3826966183152900376049329)
                      ·
                        rfl

theorem cell23_7452990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_7452990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7452990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7452990 prefixEnd_7452990 := by exact prefixLift 7452990
  have htrace : WordTrace (prefixWord ++ tailWord_7452990) baseStart_7452990 baseEnd_7452990 := by
    simpa [prefixWord, tailWord_7452990, baseEnd_7452990] using wordTrace_append hprefix tailTrace_7452990
  have hstable : (prefixWord ++ tailWord_7452990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7452990).length < 2 ^ (prefixWord ++ tailWord_7452990).sum := by decide
  have hdescent : baseEnd_7452990 < baseStart_7452990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7452990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453057 : List Nat := [1, 2, 4, 3, 1, 1, 3, 2, 1, 2, 3]
def baseStart_7453057 : Nat := 118140960795 + 7453057 * 2 ^ 59
def prefixEnd_7453057 : Nat := 4983230072969 + 3 ^ 40 * 7453057 * 2
def baseEnd_7453057 : Nat := 3827000586356751613911521

theorem tailTrace_7453057 : CollatzResearch.WordTrace tailWord_7453057 prefixEnd_7453057 3827000586356751613911521 := by
  unfold tailWord_7453057
  simp only [CollatzResearch.WordTrace]
  refine ⟨271835320959854844641493425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181223547306569896427662283 271835320959854844641493425)
  ·
    refine ⟨203876490719891133481120069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271835320959854844641493425 203876490719891133481120069)
    ·
      refine ⟨38226842009979587527710013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203876490719891133481120069 38226842009979587527710013)
      ·
        refine ⟨14335065753742345322891255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38226842009979587527710013 14335065753742345322891255)
        ·
          refine ⟨21502598630613517984336883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14335065753742345322891255 21502598630613517984336883)
          ·
            refine ⟨32253897945920276976505325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21502598630613517984336883 32253897945920276976505325)
            ·
              refine ⟨12095211729720103866189497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32253897945920276976505325 12095211729720103866189497)
              ·
                refine ⟨9071408797290077899642123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12095211729720103866189497 9071408797290077899642123)
                ·
                  refine ⟨13607113195935116849463185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9071408797290077899642123 13607113195935116849463185)
                  ·
                    refine ⟨10205334896951337637097389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13607113195935116849463185 10205334896951337637097389)
                    ·
                      refine ⟨3827000586356751613911521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10205334896951337637097389 3827000586356751613911521)
                      ·
                        rfl

theorem cell23_7453057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_7453057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453057 prefixEnd_7453057 := by exact prefixLift 7453057
  have htrace : WordTrace (prefixWord ++ tailWord_7453057) baseStart_7453057 baseEnd_7453057 := by
    simpa [prefixWord, tailWord_7453057, baseEnd_7453057] using wordTrace_append hprefix tailTrace_7453057
  have hstable : (prefixWord ++ tailWord_7453057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453057).length < 2 ^ (prefixWord ++ tailWord_7453057).sum := by decide
  have hdescent : baseEnd_7453057 < baseStart_7453057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453070 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3]
def baseStart_7453070 : Nat := 118140960795 + 7453070 * 2 ^ 59
def prefixEnd_7453070 : Nat := 4983230072969 + 3 ^ 40 * 7453070 * 2
def baseEnd_7453070 : Nat := 3827007261605260063048961

theorem tailTrace_7453070 : CollatzResearch.WordTrace tailWord_7453070 prefixEnd_7453070 3827007261605260063048961 := by
  unfold tailWord_7453070
  simp only [CollatzResearch.WordTrace]
  refine ⟨33979474388600968482714583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181223863405871831907811109 33979474388600968482714583)
  ·
    refine ⟨50969211582901452724071875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33979474388600968482714583 50969211582901452724071875)
    ·
      refine ⟨76453817374352179086107813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50969211582901452724071875 76453817374352179086107813)
      ·
        refine ⟨14335090757691033578645215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76453817374352179086107813 14335090757691033578645215)
        ·
          refine ⟨21502636136536550367967823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14335090757691033578645215 21502636136536550367967823)
          ·
            refine ⟨32253954204804825551951735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21502636136536550367967823 32253954204804825551951735)
            ·
              refine ⟨48380931307207238327927603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32253954204804825551951735 48380931307207238327927603)
              ·
                refine ⟨72571396960810857491891405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48380931307207238327927603 72571396960810857491891405)
                ·
                  refine ⟨27214273860304071559459277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72571396960810857491891405 27214273860304071559459277)
                  ·
                    refine ⟨10205352697614026834797229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27214273860304071559459277 10205352697614026834797229)
                    ·
                      refine ⟨3827007261605260063048961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10205352697614026834797229 3827007261605260063048961)
                      ·
                        rfl

theorem cell23_7453070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_7453070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453070 prefixEnd_7453070 := by exact prefixLift 7453070
  have htrace : WordTrace (prefixWord ++ tailWord_7453070) baseStart_7453070 baseEnd_7453070 := by
    simpa [prefixWord, tailWord_7453070, baseEnd_7453070] using wordTrace_append hprefix tailTrace_7453070
  have hstable : (prefixWord ++ tailWord_7453070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453070).length < 2 ^ (prefixWord ++ tailWord_7453070).sum := by decide
  have hdescent : baseEnd_7453070 < baseStart_7453070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453087 : List Nat := [1, 1, 2, 5, 1, 1, 4, 2, 2, 1, 3]
def baseStart_7453087 : Nat := 118140960795 + 7453087 * 2 ^ 59
def prefixEnd_7453087 : Nat := 4983230072969 + 3 ^ 40 * 7453087 * 2
def baseEnd_7453087 : Nat := 3827015990776386496536383

theorem tailTrace_7453087 : CollatzResearch.WordTrace tailWord_7453087 prefixEnd_7453087 3827015990776386496536383 := by
  unfold tailWord_7453087
  simp only [CollatzResearch.WordTrace]
  refine ⟨271836415149746159765085515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181224276766497439843390343 271836415149746159765085515)
  ·
    refine ⟨407754622724619239647628273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271836415149746159765085515 407754622724619239647628273)
    ·
      refine ⟨305815967043464429735721205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407754622724619239647628273 305815967043464429735721205)
      ·
        refine ⟨28670246910324790287723863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 305815967043464429735721205 28670246910324790287723863)
        ·
          refine ⟨43005370365487185431585795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28670246910324790287723863 43005370365487185431585795)
          ·
            refine ⟨64508055548230778147378693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43005370365487185431585795 64508055548230778147378693)
            ·
              refine ⟨12095260415293270902633505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64508055548230778147378693 12095260415293270902633505)
              ·
                refine ⟨9071445311469953176975129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12095260415293270902633505 9071445311469953176975129)
                ·
                  refine ⟨6803583983602464882731347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9071445311469953176975129 6803583983602464882731347)
                  ·
                    refine ⟨10205375975403697324097021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6803583983602464882731347 10205375975403697324097021)
                    ·
                      refine ⟨3827015990776386496536383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10205375975403697324097021 3827015990776386496536383)
                      ·
                        rfl

theorem cell23_7453087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_7453087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453087 prefixEnd_7453087 := by exact prefixLift 7453087
  have htrace : WordTrace (prefixWord ++ tailWord_7453087) baseStart_7453087 baseEnd_7453087 := by
    simpa [prefixWord, tailWord_7453087, baseEnd_7453087] using wordTrace_append hprefix tailTrace_7453087
  have hstable : (prefixWord ++ tailWord_7453087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453087).length < 2 ^ (prefixWord ++ tailWord_7453087).sum := by decide
  have hdescent : baseEnd_7453087 < baseStart_7453087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453138 : List Nat := [3, 2, 2, 4, 2, 1, 1, 2, 2, 1, 3]
def baseStart_7453138 : Nat := 118140960795 + 7453138 * 2 ^ 59
def prefixEnd_7453138 : Nat := 4983230072969 + 3 ^ 40 * 7453138 * 2
def baseEnd_7453138 : Nat := 3827042178289765796998649

theorem tailTrace_7453138 : CollatzResearch.WordTrace tailWord_7453138 prefixEnd_7453138 3827042178289765796998649 := by
  unfold tailWord_7453138
  simp only [CollatzResearch.WordTrace]
  refine ⟨67959568818140348868798017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181225516848374263650128045 67959568818140348868798017)
  ·
    refine ⟨50969676613605261651598513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67959568818140348868798017 50969676613605261651598513)
    ·
      refine ⟨38227257460203946238698885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50969676613605261651598513 38227257460203946238698885)
      ·
        refine ⟨7167610773788239919756041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38227257460203946238698885 7167610773788239919756041)
        ·
          refine ⟨5375708080341179939817031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7167610773788239919756041 5375708080341179939817031)
          ·
            refine ⟨8063562120511769909725547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5375708080341179939817031 8063562120511769909725547)
            ·
              refine ⟨12095343180767654864588321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8063562120511769909725547 12095343180767654864588321)
              ·
                refine ⟨9071507385575741148441241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12095343180767654864588321 9071507385575741148441241)
                ·
                  refine ⟨6803630539181805861330931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9071507385575741148441241 6803630539181805861330931)
                  ·
                    refine ⟨10205445808772708791996397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6803630539181805861330931 10205445808772708791996397)
                    ·
                      refine ⟨3827042178289765796998649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10205445808772708791996397 3827042178289765796998649)
                      ·
                        rfl

theorem cell23_7453138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_7453138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453138 prefixEnd_7453138 := by exact prefixLift 7453138
  have htrace : WordTrace (prefixWord ++ tailWord_7453138) baseStart_7453138 baseEnd_7453138 := by
    simpa [prefixWord, tailWord_7453138, baseEnd_7453138] using wordTrace_append hprefix tailTrace_7453138
  have hstable : (prefixWord ++ tailWord_7453138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453138).length < 2 ^ (prefixWord ++ tailWord_7453138).sum := by decide
  have hdescent : baseEnd_7453138 < baseStart_7453138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453140 : List Nat := [2, 4, 1, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_7453140 : Nat := 118140960795 + 7453140 * 2 ^ 59
def prefixEnd_7453140 : Nat := 4983230072969 + 3 ^ 40 * 7453140 * 2
def baseEnd_7453140 : Nat := 3827043205251074789173639

theorem tailTrace_7453140 : CollatzResearch.WordTrace tailWord_7453140 prefixEnd_7453140 3827043205251074789173639 := by
  unfold tailWord_7453140
  simp only [CollatzResearch.WordTrace]
  refine ⟨135919174109277074908382437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181225565479036099877843249 135919174109277074908382437)
  ·
    refine ⟨25484845145489451545321707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135919174109277074908382437 25484845145489451545321707)
    ·
      refine ⟨38227267718234177317982561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25484845145489451545321707 38227267718234177317982561)
      ·
        refine ⟨28670450788675632988486921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38227267718234177317982561 28670450788675632988486921)
        ·
          refine ⟨21502838091506724741365191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28670450788675632988486921 21502838091506724741365191)
          ·
            refine ⟨32254257137260087112047787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21502838091506724741365191 32254257137260087112047787)
            ·
              refine ⟨48381385705890130668071681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32254257137260087112047787 48381385705890130668071681)
              ·
                refine ⟨36286039279417598001053761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48381385705890130668071681 36286039279417598001053761)
                ·
                  refine ⟨27214529459563198500790321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36286039279417598001053761 27214529459563198500790321)
                  ·
                    refine ⟨20410897094672398875592741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27214529459563198500790321 20410897094672398875592741)
                    ·
                      refine ⟨3827043205251074789173639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20410897094672398875592741 3827043205251074789173639)
                      ·
                        rfl

theorem cell23_7453140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_7453140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453140 prefixEnd_7453140 := by exact prefixLift 7453140
  have htrace : WordTrace (prefixWord ++ tailWord_7453140) baseStart_7453140 baseEnd_7453140 := by
    simpa [prefixWord, tailWord_7453140, baseEnd_7453140] using wordTrace_append hprefix tailTrace_7453140
  have hstable : (prefixWord ++ tailWord_7453140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453140).length < 2 ^ (prefixWord ++ tailWord_7453140).sum := by decide
  have hdescent : baseEnd_7453140 < baseStart_7453140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453160 : List Nat := [2, 1, 4, 1, 1, 3, 2, 1, 2, 3, 3]
def baseStart_7453160 : Nat := 118140960795 + 7453160 * 2 ^ 59
def prefixEnd_7453160 : Nat := 4983230072969 + 3 ^ 40 * 7453160 * 2
def baseEnd_7453160 : Nat := 3827053474864164710923547

theorem tailTrace_7453160 : CollatzResearch.WordTrace tailWord_7453160 prefixEnd_7453160 3827053474864164710923547 := by
  unfold tailWord_7453160
  simp only [CollatzResearch.WordTrace]
  refine ⟨135919538839240846616246467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181226051785654462154995289 135919538839240846616246467)
  ·
    refine ⟨203879308258861269924369701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135919538839240846616246467 203879308258861269924369701)
    ·
      refine ⟨38227370298536488110819319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203879308258861269924369701 38227370298536488110819319)
      ·
        refine ⟨57341055447804732166228979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38227370298536488110819319 57341055447804732166228979)
        ·
          refine ⟨86011583171707098249343469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57341055447804732166228979 86011583171707098249343469)
          ·
            refine ⟨32254343689390161843503801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86011583171707098249343469 32254343689390161843503801)
            ·
              refine ⟨24190757767042621382627851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32254343689390161843503801 24190757767042621382627851)
              ·
                refine ⟨36286136650563932073941777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24190757767042621382627851 36286136650563932073941777)
                ·
                  refine ⟨27214602487922949055456333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36286136650563932073941777 27214602487922949055456333)
                  ·
                    refine ⟨10205475932971105895796125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27214602487922949055456333 10205475932971105895796125)
                    ·
                      refine ⟨3827053474864164710923547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10205475932971105895796125 3827053474864164710923547)
                      ·
                        rfl

theorem cell23_7453160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_7453160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453160 prefixEnd_7453160 := by exact prefixLift 7453160
  have htrace : WordTrace (prefixWord ++ tailWord_7453160) baseStart_7453160 baseEnd_7453160 := by
    simpa [prefixWord, tailWord_7453160, baseEnd_7453160] using wordTrace_append hprefix tailTrace_7453160
  have hstable : (prefixWord ++ tailWord_7453160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453160).length < 2 ^ (prefixWord ++ tailWord_7453160).sum := by decide
  have hdescent : baseEnd_7453160 < baseStart_7453160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453183 : List Nat := [1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 4]
def baseStart_7453183 : Nat := 118140960795 + 7453183 * 2 ^ 59
def prefixEnd_7453183 : Nat := 4983230072969 + 3 ^ 40 * 7453183 * 2
def baseEnd_7453183 : Nat := 3827065284919218120935941

theorem tailTrace_7453183 : CollatzResearch.WordTrace tailWord_7453183 prefixEnd_7453183 3827065284919218120935941 := by
  unfold tailWord_7453183
  simp only [CollatzResearch.WordTrace]
  refine ⟨271839916557398368160580203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181226611038265578773720135 271839916557398368160580203)
  ·
    refine ⟨407759874836097552240870305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271839916557398368160580203 407759874836097552240870305)
    ·
      refine ⟨305819906127073164180652729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407759874836097552240870305 305819906127073164180652729)
      ·
        refine ⟨229364929595304873135489547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305819906127073164180652729 229364929595304873135489547)
        ·
          refine ⟨344047394392957309703234321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229364929595304873135489547 344047394392957309703234321)
          ·
            refine ⟨258035545794717982277425741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344047394392957309703234321 258035545794717982277425741)
            ·
              refine ⟨96763329673019243354034653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258035545794717982277425741 96763329673019243354034653)
              ·
                refine ⟨36286248627382216257762995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96763329673019243354034653 36286248627382216257762995)
                ·
                  refine ⟨54429372941073324386644493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36286248627382216257762995 54429372941073324386644493)
                  ·
                    refine ⟨20411014852902496644991685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54429372941073324386644493 20411014852902496644991685)
                    ·
                      refine ⟨3827065284919218120935941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20411014852902496644991685 3827065284919218120935941)
                      ·
                        rfl

theorem cell23_7453183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_7453183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453183 prefixEnd_7453183 := by exact prefixLift 7453183
  have htrace : WordTrace (prefixWord ++ tailWord_7453183) baseStart_7453183 baseEnd_7453183 := by
    simpa [prefixWord, tailWord_7453183, baseEnd_7453183] using wordTrace_append hprefix tailTrace_7453183
  have hstable : (prefixWord ++ tailWord_7453183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453183).length < 2 ^ (prefixWord ++ tailWord_7453183).sum := by decide
  have hdescent : baseEnd_7453183 < baseStart_7453183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453207 : List Nat := [1, 1, 3, 6, 1, 1, 1, 1, 1, 2, 5]
def baseStart_7453207 : Nat := 118140960795 + 7453207 * 2 ^ 59
def prefixEnd_7453207 : Nat := 4983230072969 + 3 ^ 40 * 7453207 * 2
def baseEnd_7453207 : Nat := 3827077608454926027035831

theorem tailTrace_7453207 : CollatzResearch.WordTrace tailWord_7453207 prefixEnd_7453207 3827077608454926027035831 := by
  unfold tailWord_7453207
  simp only [CollatzResearch.WordTrace]
  refine ⟨271840791909311420259453875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181227194606207613506302583 271840791909311420259453875)
  ·
    refine ⟨407761187863967130389180813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271840791909311420259453875 407761187863967130389180813)
    ·
      refine ⟨152910445448987673895942805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407761187863967130389180813 152910445448987673895942805)
      ·
        refine ⟨7167677130421297213872319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 152910445448987673895942805 7167677130421297213872319)
        ·
          refine ⟨10751515695631945820808479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7167677130421297213872319 10751515695631945820808479)
          ·
            refine ⟨16127273543447918731212719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10751515695631945820808479 16127273543447918731212719)
            ·
              refine ⟨24190910315171878096819079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16127273543447918731212719 24190910315171878096819079)
              ·
                refine ⟨36286365472757817145228619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24190910315171878096819079 36286365472757817145228619)
                ·
                  refine ⟨54429548209136725717842929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36286365472757817145228619 54429548209136725717842929)
                  ·
                    refine ⟨40822161156852544288382197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54429548209136725717842929 40822161156852544288382197)
                    ·
                      refine ⟨3827077608454926027035831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40822161156852544288382197 3827077608454926027035831)
                      ·
                        rfl

theorem cell23_7453207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_7453207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453207 prefixEnd_7453207 := by exact prefixLift 7453207
  have htrace : WordTrace (prefixWord ++ tailWord_7453207) baseStart_7453207 baseEnd_7453207 := by
    simpa [prefixWord, tailWord_7453207, baseEnd_7453207] using wordTrace_append hprefix tailTrace_7453207
  have hstable : (prefixWord ++ tailWord_7453207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453207).length < 2 ^ (prefixWord ++ tailWord_7453207).sum := by decide
  have hdescent : baseEnd_7453207 < baseStart_7453207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453237 : List Nat := [1, 3, 3, 1, 1, 2, 4, 1, 2, 2, 3]
def baseStart_7453237 : Nat := 118140960795 + 7453237 * 2 ^ 59
def prefixEnd_7453237 : Nat := 4983230072969 + 3 ^ 40 * 7453237 * 2
def baseEnd_7453237 : Nat := 3827093012874560909660693

theorem tailTrace_7453237 : CollatzResearch.WordTrace tailWord_7453237 prefixEnd_7453237 3827093012874560909660693 := by
  unfold tailWord_7453237
  simp only [CollatzResearch.WordTrace]
  refine ⟨271841886099202735383045965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181227924066135156922030643 271841886099202735383045965)
  ·
    refine ⟨101940707287201025768642237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271841886099202735383045965 101940707287201025768642237)
    ·
      refine ⟨38227765232700384663240839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101940707287201025768642237 38227765232700384663240839)
      ·
        refine ⟨57341647849050576994861259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38227765232700384663240839 57341647849050576994861259)
        ·
          refine ⟨86012471773575865492291889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57341647849050576994861259 86012471773575865492291889)
          ·
            refine ⟨64509353830181899119218917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86012471773575865492291889 64509353830181899119218917)
            ·
              refine ⟨12095503843159106084853547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64509353830181899119218917 12095503843159106084853547)
              ·
                refine ⟨18143255764738659127280321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12095503843159106084853547 18143255764738659127280321)
                ·
                  refine ⟨13607441823553994345460241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18143255764738659127280321 13607441823553994345460241)
                  ·
                    refine ⟨10205581367665495759095181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13607441823553994345460241 10205581367665495759095181)
                    ·
                      refine ⟨3827093012874560909660693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10205581367665495759095181 3827093012874560909660693)
                      ·
                        rfl

theorem cell23_7453237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_7453237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453237 prefixEnd_7453237 := by exact prefixLift 7453237
  have htrace : WordTrace (prefixWord ++ tailWord_7453237) baseStart_7453237 baseEnd_7453237 := by
    simpa [prefixWord, tailWord_7453237, baseEnd_7453237] using wordTrace_append hprefix tailTrace_7453237
  have hstable : (prefixWord ++ tailWord_7453237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453237).length < 2 ^ (prefixWord ++ tailWord_7453237).sum := by decide
  have hdescent : baseEnd_7453237 < baseStart_7453237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453261 : List Nat := [1, 6, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_7453261 : Nat := 118140960795 + 7453261 * 2 ^ 59
def prefixEnd_7453261 : Nat := 4983230072969 + 3 ^ 40 * 7453261 * 2
def baseEnd_7453261 : Nat := 1275701778803422938586861

theorem tailTrace_7453261 : CollatzResearch.WordTrace tailWord_7453261 prefixEnd_7453261 1275701778803422938586861 := by
  unfold tailWord_7453261
  simp only [CollatzResearch.WordTrace]
  refine ⟨271842761451115787481919637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181228507634077191654613091 271842761451115787481919637)
  ·
    refine ⟨12742629443021052538214983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 271842761451115787481919637 12742629443021052538214983)
    ·
      refine ⟨19113944164531578807322475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12742629443021052538214983 19113944164531578807322475)
      ·
        refine ⟨28670916246797368210983713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19113944164531578807322475 28670916246797368210983713)
        ·
          refine ⟨21503187185098026158237785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28670916246797368210983713 21503187185098026158237785)
          ·
            refine ⟨16127390388823519618678339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21503187185098026158237785 16127390388823519618678339)
            ·
              refine ⟨24191085583235279428017509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16127390388823519618678339 24191085583235279428017509)
              ·
                refine ⟨4535828546856614892753283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24191085583235279428017509 4535828546856614892753283)
                ·
                  refine ⟨6803742820284922339129925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4535828546856614892753283 6803742820284922339129925)
                  ·
                    refine ⟨1275701778803422938586861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6803742820284922339129925 1275701778803422938586861)
                    ·
                      rfl

theorem cell23_7453261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_7453261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453261 prefixEnd_7453261 := by exact prefixLift 7453261
  have htrace : WordTrace (prefixWord ++ tailWord_7453261) baseStart_7453261 baseEnd_7453261 := by
    simpa [prefixWord, tailWord_7453261, baseEnd_7453261] using wordTrace_append hprefix tailTrace_7453261
  have hstable : (prefixWord ++ tailWord_7453261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453261).length < 2 ^ (prefixWord ++ tailWord_7453261).sum := by decide
  have hdescent : baseEnd_7453261 < baseStart_7453261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453278 : List Nat := [4, 4, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_7453278 : Nat := 118140960795 + 7453278 * 2 ^ 59
def prefixEnd_7453278 : Nat := 4983230072969 + 3 ^ 40 * 7453278 * 2
def baseEnd_7453278 : Nat := 1275704688527131749749335

theorem tailTrace_7453278 : CollatzResearch.WordTrace tailWord_7453278 prefixEnd_7453278 1275704688527131749749335 := by
  unfold tailWord_7453278
  simp only [CollatzResearch.WordTrace]
  refine ⟨33980422686506774923161061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181228920994702799590192325 33980422686506774923161061)
  ·
    refine ⟨6371329253720020298092699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33980422686506774923161061 6371329253720020298092699)
    ·
      refine ⟨9556993880580030447139049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6371329253720020298092699 9556993880580030447139049)
      ·
        refine ⟨7167745410435022835354287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9556993880580030447139049 7167745410435022835354287)
        ·
          refine ⟨10751618115652534253031431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7167745410435022835354287 10751618115652534253031431)
          ·
            refine ⟨16127427173478801379547147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10751618115652534253031431 16127427173478801379547147)
            ·
              refine ⟨24191140760218202069320721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16127427173478801379547147 24191140760218202069320721)
              ·
                refine ⟨18143355570163651551990541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24191140760218202069320721 18143355570163651551990541)
                ·
                  refine ⟨6803758338811369331996453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18143355570163651551990541 6803758338811369331996453)
                  ·
                    refine ⟨1275704688527131749749335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6803758338811369331996453 1275704688527131749749335)
                    ·
                      rfl

theorem cell23_7453278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_7453278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453278 prefixEnd_7453278 := by exact prefixLift 7453278
  have htrace : WordTrace (prefixWord ++ tailWord_7453278) baseStart_7453278 baseEnd_7453278 := by
    simpa [prefixWord, tailWord_7453278, baseEnd_7453278] using wordTrace_append hprefix tailTrace_7453278
  have hstable : (prefixWord ++ tailWord_7453278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453278).length < 2 ^ (prefixWord ++ tailWord_7453278).sum := by decide
  have hdescent : baseEnd_7453278 < baseStart_7453278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453294 : List Nat := [4, 1, 2, 2, 2, 2, 1, 1, 1, 5, 2]
def baseStart_7453294 : Nat := 118140960795 + 7453294 * 2 ^ 59
def prefixEnd_7453294 : Nat := 4983230072969 + 3 ^ 40 * 7453294 * 2
def baseEnd_7453294 : Nat := 3827122281271867186647931

theorem tailTrace_7453294 : CollatzResearch.WordTrace tailWord_7453294 prefixEnd_7453294 3827122281271867186647931 := by
  unfold tailWord_7453294
  simp only [CollatzResearch.WordTrace]
  refine ⟨33980495632499529264733867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181229310039997489411913957 33980495632499529264733867)
  ·
    refine ⟨50970743448749293897100801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33980495632499529264733867 50970743448749293897100801)
    ·
      refine ⟨38228057586561970422825601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50970743448749293897100801 38228057586561970422825601)
      ·
        refine ⟨28671043189921477817119201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38228057586561970422825601 28671043189921477817119201)
        ·
          refine ⟨21503282392441108362839401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28671043189921477817119201 21503282392441108362839401)
          ·
            refine ⟨16127461794330831272129551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21503282392441108362839401 16127461794330831272129551)
            ·
              refine ⟨24191192691496246908194327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16127461794330831272129551 24191192691496246908194327)
              ·
                refine ⟨36286789037244370362291491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24191192691496246908194327 36286789037244370362291491)
                ·
                  refine ⟨54430183555866555543437237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36286789037244370362291491 54430183555866555543437237)
                  ·
                    refine ⟨5102829708362489582197241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54430183555866555543437237 5102829708362489582197241)
                    ·
                      refine ⟨3827122281271867186647931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5102829708362489582197241 3827122281271867186647931)
                      ·
                        rfl

theorem cell23_7453294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_7453294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453294 prefixEnd_7453294 := by exact prefixLift 7453294
  have htrace : WordTrace (prefixWord ++ tailWord_7453294) baseStart_7453294 baseEnd_7453294 := by
    simpa [prefixWord, tailWord_7453294, baseEnd_7453294] using wordTrace_append hprefix tailTrace_7453294
  have hstable : (prefixWord ++ tailWord_7453294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453294).length < 2 ^ (prefixWord ++ tailWord_7453294).sum := by decide
  have hdescent : baseEnd_7453294 < baseStart_7453294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453317 : List Nat := [1, 3, 1, 1, 4, 3, 1, 1, 4, 4]
def baseStart_7453317 : Nat := 118140960795 + 7453317 * 2 ^ 59
def prefixEnd_7453317 : Nat := 4983230072969 + 3 ^ 40 * 7453317 * 2
def baseEnd_7453317 : Nat := 1275711363775640198886775

theorem tailTrace_7453317 : CollatzResearch.WordTrace tailWord_7453317 prefixEnd_7453317 1275711363775640198886775 := by
  unfold tailWord_7453317
  simp only [CollatzResearch.WordTrace]
  refine ⟨271844803938912909045958205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181229869292608606030638803 271844803938912909045958205)
  ·
    refine ⟨101941801477092340892234327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271844803938912909045958205 101941801477092340892234327)
    ·
      refine ⟨152912702215638511338351491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101941801477092340892234327 152912702215638511338351491)
      ·
        refine ⟨229369053323457767007527237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152912702215638511338351491 229369053323457767007527237)
        ·
          refine ⟨43006697498148331313911357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229369053323457767007527237 43006697498148331313911357)
          ·
            refine ⟨16127511561805624242716759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43006697498148331313911357 16127511561805624242716759)
            ·
              refine ⟨24191267342708436364075139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16127511561805624242716759 24191267342708436364075139)
              ·
                refine ⟨36286901014062654546112709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24191267342708436364075139 36286901014062654546112709)
                ·
                  refine ⟨6803793940136747727396133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36286901014062654546112709 6803793940136747727396133)
                  ·
                    refine ⟨1275711363775640198886775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6803793940136747727396133 1275711363775640198886775)
                    ·
                      rfl

theorem cell23_7453317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4, 4].length) (baseStart_7453317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453317 prefixEnd_7453317 := by exact prefixLift 7453317
  have htrace : WordTrace (prefixWord ++ tailWord_7453317) baseStart_7453317 baseEnd_7453317 := by
    simpa [prefixWord, tailWord_7453317, baseEnd_7453317] using wordTrace_append hprefix tailTrace_7453317
  have hstable : (prefixWord ++ tailWord_7453317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453317).length < 2 ^ (prefixWord ++ tailWord_7453317).sum := by decide
  have hdescent : baseEnd_7453317 < baseStart_7453317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453370 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5]
def baseStart_7453370 : Nat := 118140960795 + 7453370 * 2 ^ 59
def prefixEnd_7453370 : Nat := 4983230072969 + 3 ^ 40 * 7453370 * 2
def baseEnd_7453370 : Nat := 3827161305801608889297581

theorem tailTrace_7453370 : CollatzResearch.WordTrace tailWord_7453370 prefixEnd_7453370 3827161305801608889297581 := by
  unfold tailWord_7453370
  simp only [CollatzResearch.WordTrace]
  refine ⟨67961684251930224774409391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181231158005147266065091709 67961684251930224774409391)
  ·
    refine ⟨101942526377895337161614087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67961684251930224774409391 101942526377895337161614087)
    ·
      refine ⟨152913789566843005742421131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101942526377895337161614087 152913789566843005742421131)
      ·
        refine ⟨229370684350264508613631697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152913789566843005742421131 229370684350264508613631697)
        ·
          refine ⟨172028013262698381460223773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229370684350264508613631697 172028013262698381460223773)
          ·
            refine ⟨64510504973511893047583915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172028013262698381460223773 64510504973511893047583915)
            ·
              refine ⟨96765757460267839571375873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64510504973511893047583915 96765757460267839571375873)
              ·
                refine ⟨72574318095200879678531905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96765757460267839571375873 72574318095200879678531905)
                ·
                  refine ⟨54430738571400659758898929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72574318095200879678531905 54430738571400659758898929)
                  ·
                    refine ⟨40823053928550494819174197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54430738571400659758898929 40823053928550494819174197)
                    ·
                      refine ⟨3827161305801608889297581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40823053928550494819174197 3827161305801608889297581)
                      ·
                        rfl

theorem cell23_7453370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_7453370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453370 prefixEnd_7453370 := by exact prefixLift 7453370
  have htrace : WordTrace (prefixWord ++ tailWord_7453370) baseStart_7453370 baseEnd_7453370 := by
    simpa [prefixWord, tailWord_7453370, baseEnd_7453370] using wordTrace_append hprefix tailTrace_7453370
  have hstable : (prefixWord ++ tailWord_7453370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453370).length < 2 ^ (prefixWord ++ tailWord_7453370).sum := by decide
  have hdescent : baseEnd_7453370 < baseStart_7453370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453374 : List Nat := [4, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3]
def baseStart_7453374 : Nat := 118140960795 + 7453374 * 2 ^ 59
def prefixEnd_7453374 : Nat := 4983230072969 + 3 ^ 40 * 7453374 * 2
def baseEnd_7453374 : Nat := 3827163359724226873647563

theorem tailTrace_7453374 : CollatzResearch.WordTrace tailWord_7453374 prefixEnd_7453374 3827163359724226873647563 := by
  unfold tailWord_7453374
  simp only [CollatzResearch.WordTrace]
  refine ⟨33980860362463300972597897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181231255266470938520522117 33980860362463300972597897)
  ·
    refine ⟨25485645271847475729448423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33980860362463300972597897 25485645271847475729448423)
    ·
      refine ⟨38228467907771213594172635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25485645271847475729448423 38228467907771213594172635)
      ·
        refine ⟨57342701861656820391258953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38228467907771213594172635 57342701861656820391258953)
        ·
          refine ⟨43007026396242615293444215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57342701861656820391258953 43007026396242615293444215)
          ·
            refine ⟨64510539594363922940166323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43007026396242615293444215 64510539594363922940166323)
            ·
              refine ⟨96765809391545884410249485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64510539594363922940166323 96765809391545884410249485)
              ·
                refine ⟨36287178521829706653843557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96765809391545884410249485 36287178521829706653843557)
                ·
                  refine ⟨6803845972843069997595667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36287178521829706653843557 6803845972843069997595667)
                  ·
                    refine ⟨10205768959264604996393501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6803845972843069997595667 10205768959264604996393501)
                    ·
                      refine ⟨3827163359724226873647563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10205768959264604996393501 3827163359724226873647563)
                      ·
                        rfl

theorem cell23_7453374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_7453374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453374 prefixEnd_7453374 := by exact prefixLift 7453374
  have htrace : WordTrace (prefixWord ++ tailWord_7453374) baseStart_7453374 baseEnd_7453374 := by
    simpa [prefixWord, tailWord_7453374, baseEnd_7453374] using wordTrace_append hprefix tailTrace_7453374
  have hstable : (prefixWord ++ tailWord_7453374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453374).length < 2 ^ (prefixWord ++ tailWord_7453374).sum := by decide
  have hdescent : baseEnd_7453374 < baseStart_7453374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453482 : List Nat := [3, 1, 4, 3, 1, 2, 1, 2, 2, 2, 2]
def baseStart_7453482 : Nat := 118140960795 + 7453482 * 2 ^ 59
def prefixEnd_7453482 : Nat := 4983230072969 + 3 ^ 40 * 7453482 * 2
def baseEnd_7453482 : Nat := 3827218815634912451097067

theorem tailTrace_7453482 : CollatzResearch.WordTrace tailWord_7453482 prefixEnd_7453482 3827218815634912451097067 := by
  unfold tailWord_7453482
  simp only [CollatzResearch.WordTrace]
  refine ⟨67962705495828785556428675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181233881322210094817143133 67962705495828785556428675)
  ·
    refine ⟨101944058243743178334643013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67962705495828785556428675 101944058243743178334643013)
    ·
      refine ⟨19114510920701845937745565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101944058243743178334643013 19114510920701845937745565)
      ·
        refine ⟨7167941595263192226654587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19114510920701845937745565 7167941595263192226654587)
        ·
          refine ⟨10751912392894788339981881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7167941595263192226654587 10751912392894788339981881)
          ·
            refine ⟨8063934294671091254986411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10751912392894788339981881 8063934294671091254986411)
            ·
              refine ⟨12095901442006636882479617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8063934294671091254986411 12095901442006636882479617)
              ·
                refine ⟨9071926081504977661859713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12095901442006636882479617 9071926081504977661859713)
                ·
                  refine ⟨6803944561128733246394785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9071926081504977661859713 6803944561128733246394785)
                  ·
                    refine ⟨5102958420846549934796089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6803944561128733246394785 5102958420846549934796089)
                    ·
                      refine ⟨3827218815634912451097067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5102958420846549934796089 3827218815634912451097067)
                      ·
                        rfl

theorem cell23_7453482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_7453482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453482 prefixEnd_7453482 := by exact prefixLift 7453482
  have htrace : WordTrace (prefixWord ++ tailWord_7453482) baseStart_7453482 baseEnd_7453482 := by
    simpa [prefixWord, tailWord_7453482, baseEnd_7453482] using wordTrace_append hprefix tailTrace_7453482
  have hstable : (prefixWord ++ tailWord_7453482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453482).length < 2 ^ (prefixWord ++ tailWord_7453482).sum := by decide
  have hdescent : baseEnd_7453482 < baseStart_7453482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453507 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 3, 4, 3]
def baseStart_7453507 : Nat := 118140960795 + 7453507 * 2 ^ 59
def prefixEnd_7453507 : Nat := 4983230072969 + 3 ^ 40 * 7453507 * 2
def baseEnd_7453507 : Nat := 3827231652651274853284451

theorem tailTrace_7453507 : CollatzResearch.WordTrace tailWord_7453507 prefixEnd_7453507 3827231652651274853284451 := by
  unfold tailWord_7453507
  simp only [CollatzResearch.WordTrace]
  refine ⟨271851733808224571495374775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181234489205483047663583183 271851733808224571495374775)
  ·
    refine ⟨407777600712336857243062163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271851733808224571495374775 407777600712336857243062163)
    ·
      refine ⟨611666401068505285864593245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407777600712336857243062163 611666401068505285864593245)
      ·
        refine ⟨229374900400689482199222467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 611666401068505285864593245 229374900400689482199222467)
        ·
          refine ⟨344062350601034223298833701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229374900400689482199222467 344062350601034223298833701)
          ·
            refine ⟨64511690737693916868531319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 344062350601034223298833701 64511690737693916868531319)
            ·
              refine ⟨96767536106540875302796979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64511690737693916868531319 96767536106540875302796979)
              ·
                refine ⟨145151304159811312954195469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96767536106540875302796979 145151304159811312954195469)
                ·
                  refine ⟨54431739059929242357823301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145151304159811312954195469 54431739059929242357823301)
                  ·
                    refine ⟨10205951073736732942091869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54431739059929242357823301 10205951073736732942091869)
                    ·
                      refine ⟨3827231652651274853284451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10205951073736732942091869 3827231652651274853284451)
                      ·
                        rfl

theorem cell23_7453507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4, 3].length) (baseStart_7453507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453507 prefixEnd_7453507 := by exact prefixLift 7453507
  have htrace : WordTrace (prefixWord ++ tailWord_7453507) baseStart_7453507 baseEnd_7453507 := by
    simpa [prefixWord, tailWord_7453507, baseEnd_7453507] using wordTrace_append hprefix tailTrace_7453507
  have hstable : (prefixWord ++ tailWord_7453507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453507).length < 2 ^ (prefixWord ++ tailWord_7453507).sum := by decide
  have hdescent : baseEnd_7453507 < baseStart_7453507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453527 : List Nat := [1, 1, 3, 2, 4, 1, 1, 2, 8]
def baseStart_7453527 : Nat := 118140960795 + 7453527 * 2 ^ 59
def prefixEnd_7453527 : Nat := 4983230072969 + 3 ^ 40 * 7453527 * 2
def baseEnd_7453527 : Nat := 425249102473818308337151

theorem tailTrace_7453527 : CollatzResearch.WordTrace tailWord_7453527 prefixEnd_7453527 425249102473818308337151 := by
  unfold tailWord_7453527
  simp only [CollatzResearch.WordTrace]
  refine ⟨271852463268152114911102835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181234975512101409940735223 271852463268152114911102835)
  ·
    refine ⟨407778694902228172366654253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271852463268152114911102835 407778694902228172366654253)
    ·
      refine ⟨152917010588335564637495345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407778694902228172366654253 152917010588335564637495345)
      ·
        refine ⟨114687757941251673478121509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152917010588335564637495345 114687757941251673478121509)
        ·
          refine ⟨21503954613984688777147783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114687757941251673478121509 21503954613984688777147783)
          ·
            refine ⟨32255931920977033165721675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21503954613984688777147783 32255931920977033165721675)
            ·
              refine ⟨48383897881465549748582513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32255931920977033165721675 48383897881465549748582513)
              ·
                refine ⟨36287923411099162311436885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48383897881465549748582513 36287923411099162311436885)
                ·
                  refine ⟨425249102473818308337151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36287923411099162311436885 425249102473818308337151)
                  ·
                    rfl

theorem cell23_7453527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 8].length) (baseStart_7453527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453527 prefixEnd_7453527 := by exact prefixLift 7453527
  have htrace : WordTrace (prefixWord ++ tailWord_7453527) baseStart_7453527 baseEnd_7453527 := by
    simpa [prefixWord, tailWord_7453527, baseEnd_7453527] using wordTrace_append hprefix tailTrace_7453527
  have hstable : (prefixWord ++ tailWord_7453527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453527).length < 2 ^ (prefixWord ++ tailWord_7453527).sum := by decide
  have hdescent : baseEnd_7453527 < baseStart_7453527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453548 : List Nat := [2, 2, 1, 1, 4, 1, 5, 2, 1, 4]
def baseStart_7453548 : Nat := 118140960795 + 7453548 * 2 ^ 59
def prefixEnd_7453548 : Nat := 4983230072969 + 3 ^ 40 * 7453548 * 2
def baseEnd_7453548 : Nat := 1275750901786036397623921

theorem tailTrace_7453548 : CollatzResearch.WordTrace tailWord_7453548 prefixEnd_7453548 1275750901786036397623921 := by
  unfold tailWord_7453548
  simp only [CollatzResearch.WordTrace]
  refine ⟨135926614600538017748808649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181235486134050690331744865 135926614600538017748808649)
  ·
    refine ⟨101944960950403513311606487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135926614600538017748808649 101944960950403513311606487)
    ·
      refine ⟨152917441425605269967409731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101944960950403513311606487 152917441425605269967409731)
      ·
        refine ⟨229376162138407904951114597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152917441425605269967409731 229376162138407904951114597)
        ·
          refine ⟨43008030400951482178333987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229376162138407904951114597 43008030400951482178333987)
          ·
            refine ⟨64512045601427223267500981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43008030400951482178333987 64512045601427223267500981)
            ·
              refine ⟨6048004275133802181328217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64512045601427223267500981 6048004275133802181328217)
              ·
                refine ⟨4536003206350351635996163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6048004275133802181328217 4536003206350351635996163)
                ·
                  refine ⟨6804004809525527453994245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4536003206350351635996163 6804004809525527453994245)
                  ·
                    refine ⟨1275750901786036397623921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6804004809525527453994245 1275750901786036397623921)
                    ·
                      rfl

theorem cell23_7453548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2, 1, 4].length) (baseStart_7453548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453548 prefixEnd_7453548 := by exact prefixLift 7453548
  have htrace : WordTrace (prefixWord ++ tailWord_7453548) baseStart_7453548 baseEnd_7453548 := by
    simpa [prefixWord, tailWord_7453548, baseEnd_7453548] using wordTrace_append hprefix tailTrace_7453548
  have hstable : (prefixWord ++ tailWord_7453548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453548).length < 2 ^ (prefixWord ++ tailWord_7453548).sum := by decide
  have hdescent : baseEnd_7453548 < baseStart_7453548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453561 : List Nat := [1, 2, 1, 3, 2, 5, 2, 1, 6]
def baseStart_7453561 : Nat := 118140960795 + 7453561 * 2 ^ 59
def prefixEnd_7453561 : Nat := 4983230072969 + 3 ^ 40 * 7453561 * 2
def baseEnd_7453561 : Nat := 425251042289624182445467

theorem tailTrace_7453561 : CollatzResearch.WordTrace tailWord_7453561 prefixEnd_7453561 425251042289624182445467 := by
  unfold tailWord_7453561
  simp only [CollatzResearch.WordTrace]
  refine ⟨271853703350028938717840537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181235802233352625811893691 271853703350028938717840537)
  ·
    refine ⟨203890277512521704038380403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271853703350028938717840537 203890277512521704038380403)
    ·
      refine ⟨305835416268782556057570605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203890277512521704038380403 305835416268782556057570605)
      ·
        refine ⟨114688281100793458521588977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305835416268782556057570605 114688281100793458521588977)
        ·
          refine ⟨86016210825595093891191733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114688281100793458521588977 86016210825595093891191733)
          ·
            refine ⟨8064019764899540052299225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86016210825595093891191733 8064019764899540052299225)
            ·
              refine ⟨6048014823674655039224419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8064019764899540052299225 6048014823674655039224419)
              ·
                refine ⟨9072022235511982558836629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6048014823674655039224419 9072022235511982558836629)
                ·
                  refine ⟨425251042289624182445467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9072022235511982558836629 425251042289624182445467)
                  ·
                    rfl

theorem cell23_7453561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 6].length) (baseStart_7453561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453561 prefixEnd_7453561 := by exact prefixLift 7453561
  have htrace : WordTrace (prefixWord ++ tailWord_7453561) baseStart_7453561 baseEnd_7453561 := by
    simpa [prefixWord, tailWord_7453561, baseEnd_7453561] using wordTrace_append hprefix tailTrace_7453561
  have hstable : (prefixWord ++ tailWord_7453561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453561).length < 2 ^ (prefixWord ++ tailWord_7453561).sum := by decide
  have hdescent : baseEnd_7453561 < baseStart_7453561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453564 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 3, 5, 2]
def baseStart_7453564 : Nat := 118140960795 + 7453564 * 2 ^ 59
def prefixEnd_7453564 : Nat := 4983230072969 + 3 ^ 40 * 7453564 * 2
def baseEnd_7453564 : Nat := 3827260921048581130271689

theorem tailTrace_7453564 : CollatzResearch.WordTrace tailWord_7453564 prefixEnd_7453564 3827260921048581130271689 := by
  unfold tailWord_7453564
  simp only [CollatzResearch.WordTrace]
  refine ⟨135926906384509035115099873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181235875179345380153466497 135926906384509035115099873)
  ·
    refine ⟨101945179788381776336324905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135926906384509035115099873 101945179788381776336324905)
    ·
      refine ⟨76458884841286332252243679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101945179788381776336324905 76458884841286332252243679)
      ·
        refine ⟨114688327261929498378365519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76458884841286332252243679 114688327261929498378365519)
        ·
          refine ⟨172032490892894247567548279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114688327261929498378365519 172032490892894247567548279)
          ·
            refine ⟨258048736339341371351322419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172032490892894247567548279 258048736339341371351322419)
            ·
              refine ⟨387073104509012057026983629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258048736339341371351322419 387073104509012057026983629)
              ·
                refine ⟨145152414190879521385118861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 387073104509012057026983629 145152414190879521385118861)
                ·
                  refine ⟨54432155321579820519419573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145152414190879521385118861 54432155321579820519419573)
                  ·
                    refine ⟨5103014561398108173695585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54432155321579820519419573 5103014561398108173695585)
                    ·
                      refine ⟨3827260921048581130271689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5103014561398108173695585 3827260921048581130271689)
                      ·
                        rfl

theorem cell23_7453564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 3, 5, 2].length) (baseStart_7453564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453564 prefixEnd_7453564 := by exact prefixLift 7453564
  have htrace : WordTrace (prefixWord ++ tailWord_7453564) baseStart_7453564 baseEnd_7453564 := by
    simpa [prefixWord, tailWord_7453564, baseEnd_7453564] using wordTrace_append hprefix tailTrace_7453564
  have hstable : (prefixWord ++ tailWord_7453564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453564).length < 2 ^ (prefixWord ++ tailWord_7453564).sum := by decide
  have hdescent : baseEnd_7453564 < baseStart_7453564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453591 : List Nat := [1, 1, 3, 3, 1, 2, 5, 1, 1, 5]
def baseStart_7453591 : Nat := 118140960795 + 7453591 * 2 ^ 59
def prefixEnd_7453591 : Nat := 4983230072969 + 3 ^ 40 * 7453591 * 2
def baseEnd_7453591 : Nat := 1275758261675417508211355

theorem tailTrace_7453591 : CollatzResearch.WordTrace tailWord_7453591 prefixEnd_7453591 1275758261675417508211355 := by
  unfold tailWord_7453591
  simp only [CollatzResearch.WordTrace]
  refine ⟨271854797539920253841432627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181236531693280169227621751 271854797539920253841432627)
  ·
    refine ⟨407782196309880380762148941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271854797539920253841432627 407782196309880380762148941)
    ·
      refine ⟨152918323616205142785805853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407782196309880380762148941 152918323616205142785805853)
      ·
        refine ⟨57344371356076928544677195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152918323616205142785805853 57344371356076928544677195)
        ·
          refine ⟨86016557034115392817015793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57344371356076928544677195 86016557034115392817015793)
          ·
            refine ⟨64512417775586544612761845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86016557034115392817015793 64512417775586544612761845)
            ·
              refine ⟨6048039166461238557446423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64512417775586544612761845 6048039166461238557446423)
              ·
                refine ⟨9072058749691857836169635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6048039166461238557446423 9072058749691857836169635)
                ·
                  refine ⟨13608088124537786754254453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9072058749691857836169635 13608088124537786754254453)
                  ·
                    refine ⟨1275758261675417508211355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13608088124537786754254453 1275758261675417508211355)
                    ·
                      rfl

theorem cell23_7453591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 1, 5].length) (baseStart_7453591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453591 prefixEnd_7453591 := by exact prefixLift 7453591
  have htrace : WordTrace (prefixWord ++ tailWord_7453591) baseStart_7453591 baseEnd_7453591 := by
    simpa [prefixWord, tailWord_7453591, baseEnd_7453591] using wordTrace_append hprefix tailTrace_7453591
  have hstable : (prefixWord ++ tailWord_7453591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453591).length < 2 ^ (prefixWord ++ tailWord_7453591).sum := by decide
  have hdescent : baseEnd_7453591 < baseStart_7453591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453621 : List Nat := [1, 3, 3, 2, 1, 1, 1, 5, 2, 4]
def baseStart_7453621 : Nat := 118140960795 + 7453621 * 2 ^ 59
def prefixEnd_7453621 : Nat := 4983230072969 + 3 ^ 40 * 7453621 * 2
def baseEnd_7453621 : Nat := 1275763396481962469086309

theorem tailTrace_7453621 : CollatzResearch.WordTrace tailWord_7453621 prefixEnd_7453621 1275763396481962469086309 := by
  unfold tailWord_7453621
  simp only [CollatzResearch.WordTrace]
  refine ⟨271855891729811568965024717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181237261153207712643349811 271855891729811568965024717)
  ·
    refine ⟨101945959398679338361884269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271855891729811568965024717 101945959398679338361884269)
    ·
      refine ⟨38229734774504751885706601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101945959398679338361884269 38229734774504751885706601)
      ·
        refine ⟨28672301080878563914279951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38229734774504751885706601 28672301080878563914279951)
        ·
          refine ⟨43008451621317845871419927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28672301080878563914279951 43008451621317845871419927)
          ·
            refine ⟨64512677431976768807129891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43008451621317845871419927 64512677431976768807129891)
            ·
              refine ⟨96769016147965153210694837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64512677431976768807129891 96769016147965153210694837)
              ·
                refine ⟨9072095263871733113502641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96769016147965153210694837 9072095263871733113502641)
                ·
                  refine ⟨6804071447903799835126981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9072095263871733113502641 6804071447903799835126981)
                  ·
                    refine ⟨1275763396481962469086309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6804071447903799835126981 1275763396481962469086309)
                    ·
                      rfl

theorem cell23_7453621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_7453621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453621 prefixEnd_7453621 := by exact prefixLift 7453621
  have htrace : WordTrace (prefixWord ++ tailWord_7453621) baseStart_7453621 baseEnd_7453621 := by
    simpa [prefixWord, tailWord_7453621, baseEnd_7453621] using wordTrace_append hprefix tailTrace_7453621
  have hstable : (prefixWord ++ tailWord_7453621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453621).length < 2 ^ (prefixWord ++ tailWord_7453621).sum := by decide
  have hdescent : baseEnd_7453621 < baseStart_7453621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453624 : List Nat := [2, 1, 2, 1, 2, 4, 1, 3, 1, 2, 4]
def baseStart_7453624 : Nat := 118140960795 + 7453624 * 2 ^ 59
def prefixEnd_7453624 : Nat := 4983230072969 + 3 ^ 40 * 7453624 * 2
def baseEnd_7453624 : Nat := 3827291729887850895521413

theorem tailTrace_7453624 : CollatzResearch.WordTrace tailWord_7453624 prefixEnd_7453624 3827291729887850895521413 := by
  unfold tailWord_7453624
  simp only [CollatzResearch.WordTrace]
  refine ⟨135928000574400350238691963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181237334099200466984922617 135928000574400350238691963)
  ·
    refine ⟨203892000861600525358037945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135928000574400350238691963 203892000861600525358037945)
    ·
      refine ⟨152919000646200394018528459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203892000861600525358037945 152919000646200394018528459)
      ·
        refine ⟨229378500969300591027792689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152919000646200394018528459 229378500969300591027792689)
        ·
          refine ⟨172033875726975443270844517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229378500969300591027792689 172033875726975443270844517)
          ·
            refine ⟨32256351698807895613283347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172033875726975443270844517 32256351698807895613283347)
            ·
              refine ⟨48384527548211843419925021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32256351698807895613283347 48384527548211843419925021)
              ·
                refine ⟨18144197830579441282471883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48384527548211843419925021 18144197830579441282471883)
                ·
                  refine ⟨27216296745869161923707825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18144197830579441282471883 27216296745869161923707825)
                  ·
                    refine ⟨20412222559401871442780869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27216296745869161923707825 20412222559401871442780869)
                    ·
                      refine ⟨3827291729887850895521413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20412222559401871442780869 3827291729887850895521413)
                      ·
                        rfl

theorem cell23_7453624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_7453624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453624 prefixEnd_7453624 := by exact prefixLift 7453624
  have htrace : WordTrace (prefixWord ++ tailWord_7453624) baseStart_7453624 baseEnd_7453624 := by
    simpa [prefixWord, tailWord_7453624, baseEnd_7453624] using wordTrace_append hprefix tailTrace_7453624
  have hstable : (prefixWord ++ tailWord_7453624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453624).length < 2 ^ (prefixWord ++ tailWord_7453624).sum := by decide
  have hdescent : baseEnd_7453624 < baseStart_7453624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453637 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 4, 2, 6]
def baseStart_7453637 : Nat := 118140960795 + 7453637 * 2 ^ 59
def prefixEnd_7453637 : Nat := 4983230072969 + 3 ^ 40 * 7453637 * 2
def baseEnd_7453637 : Nat := 3827298405136359344658853

theorem tailTrace_7453637 : CollatzResearch.WordTrace tailWord_7453637 prefixEnd_7453637 3827298405136359344658853 := by
  unfold tailWord_7453637
  simp only [CollatzResearch.WordTrace]
  refine ⟨271856475297753603697607165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181237650198502402465071443 271856475297753603697607165)
  ·
    refine ⟨101946178236657601386602687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271856475297753603697607165 101946178236657601386602687)
    ·
      refine ⟨152919267354986402079904031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101946178236657601386602687 152919267354986402079904031)
      ·
        refine ⟨229378901032479603119856047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152919267354986402079904031 229378901032479603119856047)
        ·
          refine ⟨344068351548719404679784071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229378901032479603119856047 344068351548719404679784071)
          ·
            refine ⟨516102527323079107019676107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344068351548719404679784071 516102527323079107019676107)
            ·
              refine ⟨774153790984618660529514161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516102527323079107019676107 774153790984618660529514161)
              ·
                refine ⟨580615343238463995397135621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 774153790984618660529514161 580615343238463995397135621)
                ·
                  refine ⟨108865376857211999136962929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 580615343238463995397135621 108865376857211999136962929)
                  ·
                    refine ⟨81649032642908999352722197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108865376857211999136962929 81649032642908999352722197)
                    ·
                      refine ⟨3827298405136359344658853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81649032642908999352722197 3827298405136359344658853)
                      ·
                        rfl

theorem cell23_7453637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_7453637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453637 prefixEnd_7453637 := by exact prefixLift 7453637
  have htrace : WordTrace (prefixWord ++ tailWord_7453637) baseStart_7453637 baseEnd_7453637 := by
    simpa [prefixWord, tailWord_7453637, baseEnd_7453637] using wordTrace_append hprefix tailTrace_7453637
  have hstable : (prefixWord ++ tailWord_7453637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453637).length < 2 ^ (prefixWord ++ tailWord_7453637).sum := by decide
  have hdescent : baseEnd_7453637 < baseStart_7453637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453685 : List Nat := [1, 3, 5, 2, 1, 2, 2, 7]
def baseStart_7453685 : Nat := 118140960795 + 7453685 * 2 ^ 59
def prefixEnd_7453685 : Nat := 4983230072969 + 3 ^ 40 * 7453685 * 2
def baseEnd_7453685 : Nat := 141752705637325005809579

theorem tailTrace_7453685 : CollatzResearch.WordTrace tailWord_7453685 prefixEnd_7453685 141752705637325005809579 := by
  unfold tailWord_7453685
  simp only [CollatzResearch.WordTrace]
  refine ⟨271858226001579707895354509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181238817334386471930236339 271858226001579707895354509)
  ·
    refine ⟨101946834750592390460757941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271858226001579707895354509 101946834750592390460757941)
    ·
      refine ⟨9557515757868036605696057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101946834750592390460757941 9557515757868036605696057)
      ·
        refine ⟨7168136818401027454272043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9557515757868036605696057 7168136818401027454272043)
        ·
          refine ⟨10752205227601541181408065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7168136818401027454272043 10752205227601541181408065)
          ·
            refine ⟨8064153920701155886056049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10752205227601541181408065 8064153920701155886056049)
            ·
              refine ⟨6048115440525866914542037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8064153920701155886056049 6048115440525866914542037)
              ·
                refine ⟨141752705637325005809579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6048115440525866914542037 141752705637325005809579)
                ·
                  rfl

theorem cell23_7453685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 7].length) (baseStart_7453685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453685 prefixEnd_7453685 := by exact prefixLift 7453685
  have htrace : WordTrace (prefixWord ++ tailWord_7453685) baseStart_7453685 baseEnd_7453685 := by
    simpa [prefixWord, tailWord_7453685, baseEnd_7453685] using wordTrace_append hprefix tailTrace_7453685
  have hstable : (prefixWord ++ tailWord_7453685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453685).length < 2 ^ (prefixWord ++ tailWord_7453685).sum := by decide
  have hdescent : baseEnd_7453685 < baseStart_7453685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453701 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 3, 4, 2]
def baseStart_7453701 : Nat := 118140960795 + 7453701 * 2 ^ 59
def prefixEnd_7453701 : Nat := 4983230072969 + 3 ^ 40 * 7453701 * 2
def baseEnd_7453701 : Nat := 3827331267898247094258559

theorem tailTrace_7453701 : CollatzResearch.WordTrace tailWord_7453701 prefixEnd_7453701 3827331267898247094258559 := by
  unfold tailWord_7453701
  simp only [CollatzResearch.WordTrace]
  refine ⟨271858809569521742627936957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181239206379681161751957971 271858809569521742627936957)
  ·
    refine ⟨101947053588570653485476359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271858809569521742627936957 101947053588570653485476359)
    ·
      refine ⟨152920580382855980228214539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101947053588570653485476359 152920580382855980228214539)
      ·
        refine ⟨229380870574283970342321809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152920580382855980228214539 229380870574283970342321809)
        ·
          refine ⟨172035652930712977756741357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229380870574283970342321809 172035652930712977756741357)
          ·
            refine ⟨64513369849017366658778009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172035652930712977756741357 64513369849017366658778009)
            ·
              refine ⟨48385027386763024994083507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64513369849017366658778009 48385027386763024994083507)
              ·
                refine ⟨72577541080144537491125261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48385027386763024994083507 72577541080144537491125261)
                ·
                  refine ⟨27216577905054201559171973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72577541080144537491125261 27216577905054201559171973)
                  ·
                    refine ⟨5103108357197662792344745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27216577905054201559171973 5103108357197662792344745)
                    ·
                      refine ⟨3827331267898247094258559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5103108357197662792344745 3827331267898247094258559)
                      ·
                        rfl

theorem cell23_7453701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 4, 2].length) (baseStart_7453701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453701 prefixEnd_7453701 := by exact prefixLift 7453701
  have htrace : WordTrace (prefixWord ++ tailWord_7453701) baseStart_7453701 baseEnd_7453701 := by
    simpa [prefixWord, tailWord_7453701, baseEnd_7453701] using wordTrace_append hprefix tailTrace_7453701
  have hstable : (prefixWord ++ tailWord_7453701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453701).length < 2 ^ (prefixWord ++ tailWord_7453701).sum := by decide
  have hdescent : baseEnd_7453701 < baseStart_7453701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453704 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 1, 3, 5]
def baseStart_7453704 : Nat := 118140960795 + 7453704 * 2 ^ 59
def prefixEnd_7453704 : Nat := 4983230072969 + 3 ^ 40 * 7453704 * 2
def baseEnd_7453704 : Nat := 3827332808340210582521045

theorem tailTrace_7453704 : CollatzResearch.WordTrace tailWord_7453704 prefixEnd_7453704 3827332808340210582521045 := by
  unfold tailWord_7453704
  simp only [CollatzResearch.WordTrace]
  refine ⟨135929459494255437070148083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181239279325673916093530777 135929459494255437070148083)
  ·
    refine ⟨203894189241383155605222125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135929459494255437070148083 203894189241383155605222125)
    ·
      refine ⟨76460320965518683351958297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203894189241383155605222125 76460320965518683351958297)
      ·
        refine ⟨57345240724139012513968723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76460320965518683351958297 57345240724139012513968723)
        ·
          refine ⟨86017861086208518770953085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57345240724139012513968723 86017861086208518770953085)
          ·
            refine ⟨32256697907328194539107407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86017861086208518770953085 32256697907328194539107407)
            ·
              refine ⟨48385046860992291808661111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32256697907328194539107407 48385046860992291808661111)
              ·
                refine ⟨72577570291488437712991667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48385046860992291808661111 72577570291488437712991667)
                ·
                  refine ⟨108866355437232656569487501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72577570291488437712991667 108866355437232656569487501)
                  ·
                    refine ⟨40824883288962246213557813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108866355437232656569487501 40824883288962246213557813)
                    ·
                      refine ⟨3827332808340210582521045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40824883288962246213557813 3827332808340210582521045)
                      ·
                        rfl

theorem cell23_7453704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_7453704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453704 prefixEnd_7453704 := by exact prefixLift 7453704
  have htrace : WordTrace (prefixWord ++ tailWord_7453704) baseStart_7453704 baseEnd_7453704 := by
    simpa [prefixWord, tailWord_7453704, baseEnd_7453704] using wordTrace_append hprefix tailTrace_7453704
  have hstable : (prefixWord ++ tailWord_7453704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453704).length < 2 ^ (prefixWord ++ tailWord_7453704).sum := by decide
  have hdescent : baseEnd_7453704 < baseStart_7453704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453754 : List Nat := [3, 1, 1, 1, 3, 1, 2, 3, 1, 7]
def baseStart_7453754 : Nat := 118140960795 + 7453754 * 2 ^ 59
def prefixEnd_7453754 : Nat := 4983230072969 + 3 ^ 40 * 7453754 * 2
def baseEnd_7453754 : Nat := 1275786160790978462298605

theorem tailTrace_7453754 : CollatzResearch.WordTrace tailWord_7453754 prefixEnd_7453754 1275786160790978462298605 := by
  unfold tailWord_7453754
  simp only [CollatzResearch.WordTrace]
  refine ⟨67965185659582433169904079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181240495092219821786410877 67965185659582433169904079)
  ·
    refine ⟨101947778489373649754856119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67965185659582433169904079 101947778489373649754856119)
    ·
      refine ⟨152921667734060474632284179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101947778489373649754856119 152921667734060474632284179)
      ·
        refine ⟨229382501601090711948426269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152921667734060474632284179 229382501601090711948426269)
        ·
          refine ⟨86018438100409016980659851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229382501601090711948426269 86018438100409016980659851)
          ·
            refine ⟨129027657150613525470989777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86018438100409016980659851 129027657150613525470989777)
            ·
              refine ⟨96770742862960144103242333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129027657150613525470989777 96770742862960144103242333)
              ·
                refine ⟨36289028573610054038715875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96770742862960144103242333 36289028573610054038715875)
                ·
                  refine ⟨54433542860415081058073813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36289028573610054038715875 54433542860415081058073813)
                  ·
                    refine ⟨1275786160790978462298605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54433542860415081058073813 1275786160790978462298605)
                    ·
                      rfl

theorem cell23_7453754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 1, 7].length) (baseStart_7453754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453754 prefixEnd_7453754 := by exact prefixLift 7453754
  have htrace : WordTrace (prefixWord ++ tailWord_7453754) baseStart_7453754 baseEnd_7453754 := by
    simpa [prefixWord, tailWord_7453754, baseEnd_7453754] using wordTrace_append hprefix tailTrace_7453754
  have hstable : (prefixWord ++ tailWord_7453754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453754).length < 2 ^ (prefixWord ++ tailWord_7453754).sum := by decide
  have hdescent : baseEnd_7453754 < baseStart_7453754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453778 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 2, 5, 2]
def baseStart_7453778 : Nat := 118140960795 + 7453778 * 2 ^ 59
def prefixEnd_7453778 : Nat := 4983230072969 + 3 ^ 40 * 7453778 * 2
def baseEnd_7453778 : Nat := 3827370805908643292995705

theorem tailTrace_7453778 : CollatzResearch.WordTrace tailWord_7453778 prefixEnd_7453778 3827370805908643292995705 := by
  unfold tailWord_7453778
  simp only [CollatzResearch.WordTrace]
  refine ⟨67965404497560696194622497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181241078660161856518993325 67965404497560696194622497)
  ·
    refine ⟨50974053373170522145966873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67965404497560696194622497 50974053373170522145966873)
    ·
      refine ⟨38230540029877891609475155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50974053373170522145966873 38230540029877891609475155)
      ·
        refine ⟨57345810044816837414212733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38230540029877891609475155 57345810044816837414212733)
        ·
          refine ⟨21504678766806314030329775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57345810044816837414212733 21504678766806314030329775)
          ·
            refine ⟨32257018150209471045494663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21504678766806314030329775 32257018150209471045494663)
            ·
              refine ⟨48385527225314206568241995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32257018150209471045494663 48385527225314206568241995)
              ·
                refine ⟨72578290837971309852362993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48385527225314206568241995 72578290837971309852362993)
                ·
                  refine ⟨54433718128478482389272245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72578290837971309852362993 54433718128478482389272245)
                  ·
                    refine ⟨5103161074544857723994273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54433718128478482389272245 5103161074544857723994273)
                    ·
                      refine ⟨3827370805908643292995705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5103161074544857723994273 3827370805908643292995705)
                      ·
                        rfl

theorem cell23_7453778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_7453778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453778 prefixEnd_7453778 := by exact prefixLift 7453778
  have htrace : WordTrace (prefixWord ++ tailWord_7453778) baseStart_7453778 baseEnd_7453778 := by
    simpa [prefixWord, tailWord_7453778, baseEnd_7453778] using wordTrace_append hprefix tailTrace_7453778
  have hstable : (prefixWord ++ tailWord_7453778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453778).length < 2 ^ (prefixWord ++ tailWord_7453778).sum := by decide
  have hdescent : baseEnd_7453778 < baseStart_7453778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453801 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 5, 4]
def baseStart_7453801 : Nat := 118140960795 + 7453801 * 2 ^ 59
def prefixEnd_7453801 : Nat := 4983230072969 + 3 ^ 40 * 7453801 * 2
def baseEnd_7453801 : Nat := 1275794205321232234336033

theorem tailTrace_7453801 : CollatzResearch.WordTrace tailWord_7453801 prefixEnd_7453801 1275794205321232234336033 := by
  unfold tailWord_7453801
  simp only [CollatzResearch.WordTrace]
  refine ⟨271862456869159459706577257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181241637912772973137718171 271862456869159459706577257)
  ·
    refine ⟨203896842651869594779932943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271862456869159459706577257 203896842651869594779932943)
    ·
      refine ⟨305845263977804392169899415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203896842651869594779932943 305845263977804392169899415)
      ·
        refine ⟨458767895966706588254849123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305845263977804392169899415 458767895966706588254849123)
        ·
          refine ⟨688151843950059882382273685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458767895966706588254849123 688151843950059882382273685)
          ·
            refine ⟨32257117685159056986669079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 688151843950059882382273685 32257117685159056986669079)
            ·
              refine ⟨48385676527738585480003619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32257117685159056986669079 48385676527738585480003619)
              ·
                refine ⟨72578514791607878220005429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48385676527738585480003619 72578514791607878220005429)
                ·
                  refine ⟨6804235761713238583125509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72578514791607878220005429 6804235761713238583125509)
                  ·
                    refine ⟨1275794205321232234336033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6804235761713238583125509 1275794205321232234336033)
                    ·
                      rfl

theorem cell23_7453801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5, 4].length) (baseStart_7453801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453801 prefixEnd_7453801 := by exact prefixLift 7453801
  have htrace : WordTrace (prefixWord ++ tailWord_7453801) baseStart_7453801 baseEnd_7453801 := by
    simpa [prefixWord, tailWord_7453801, baseEnd_7453801] using wordTrace_append hprefix tailTrace_7453801
  have hstable : (prefixWord ++ tailWord_7453801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453801).length < 2 ^ (prefixWord ++ tailWord_7453801).sum := by decide
  have hdescent : baseEnd_7453801 < baseStart_7453801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453869 : List Nat := [1, 5, 2, 1, 3, 2, 1, 3, 1, 4]
def baseStart_7453869 : Nat := 118140960795 + 7453869 * 2 ^ 59
def prefixEnd_7453869 : Nat := 4983230072969 + 3 ^ 40 * 7453869 * 2
def baseEnd_7453869 : Nat := 1275805844216067478985929

theorem tailTrace_7453869 : CollatzResearch.WordTrace tailWord_7453869 prefixEnd_7453869 1275805844216067478985929 := by
  unfold tailWord_7453869
  simp only [CollatzResearch.WordTrace]
  refine ⟨271864937032913107320052661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181243291355275404880035107 271864937032913107320052661)
  ·
    refine ⟨25487337846835603811254937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 271864937032913107320052661 25487337846835603811254937)
    ·
      refine ⟨19115503385126702858441203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25487337846835603811254937 19115503385126702858441203)
      ·
        refine ⟨28673255077690054287661805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19115503385126702858441203 28673255077690054287661805)
        ·
          refine ⟨10752470654133770357873177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28673255077690054287661805 10752470654133770357873177)
          ·
            refine ⟨8064352990600327768404883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10752470654133770357873177 8064352990600327768404883)
            ·
              refine ⟨12096529485900491652607325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8064352990600327768404883 12096529485900491652607325)
              ·
                refine ⟨4536198557212684369727747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12096529485900491652607325 4536198557212684369727747)
                ·
                  refine ⟨6804297835819026554591621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4536198557212684369727747 6804297835819026554591621)
                  ·
                    refine ⟨1275805844216067478985929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6804297835819026554591621 1275805844216067478985929)
                    ·
                      rfl

theorem cell23_7453869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_7453869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453869 prefixEnd_7453869 := by exact prefixLift 7453869
  have htrace : WordTrace (prefixWord ++ tailWord_7453869) baseStart_7453869 baseEnd_7453869 := by
    simpa [prefixWord, tailWord_7453869, baseEnd_7453869] using wordTrace_append hprefix tailTrace_7453869
  have hstable : (prefixWord ++ tailWord_7453869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453869).length < 2 ^ (prefixWord ++ tailWord_7453869).sum := by decide
  have hdescent : baseEnd_7453869 < baseStart_7453869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453911 : List Nat := [1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 6]
def baseStart_7453911 : Nat := 118140960795 + 7453911 * 2 ^ 59
def prefixEnd_7453911 : Nat := 4983230072969 + 3 ^ 40 * 7453911 * 2
def baseEnd_7453911 : Nat := 3827439098835691272632593

theorem tailTrace_7453911 : CollatzResearch.WordTrace tailWord_7453911 prefixEnd_7453911 3827439098835691272632593 := by
  unfold tailWord_7453911
  simp only [CollatzResearch.WordTrace]
  refine ⟨271866468898760948493081587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181244312599173965662054391 271866468898760948493081587)
  ·
    refine ⟨407799703348141422739622381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271866468898760948493081587 407799703348141422739622381)
    ·
      refine ⟨152924888755553033527358393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407799703348141422739622381 152924888755553033527358393)
      ·
        refine ⟨114693666566664775145518795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152924888755553033527358393 114693666566664775145518795)
        ·
          refine ⟨172040499849997162718278193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114693666566664775145518795 172040499849997162718278193)
          ·
            refine ⟨129030374887497872038708645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172040499849997162718278193 129030374887497872038708645)
            ·
              refine ⟨24193195291405851007257871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129030374887497872038708645 24193195291405851007257871)
              ·
                refine ⟨36289792937108776510886807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24193195291405851007257871 36289792937108776510886807)
                ·
                  refine ⟨54434689405663164766330211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36289792937108776510886807 54434689405663164766330211)
                  ·
                    refine ⟨81652034108494747149495317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54434689405663164766330211 81652034108494747149495317)
                    ·
                      refine ⟨3827439098835691272632593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81652034108494747149495317 3827439098835691272632593)
                      ·
                        rfl

theorem cell23_7453911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_7453911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453911 prefixEnd_7453911 := by exact prefixLift 7453911
  have htrace : WordTrace (prefixWord ++ tailWord_7453911) baseStart_7453911 baseEnd_7453911 := by
    simpa [prefixWord, tailWord_7453911, baseEnd_7453911] using wordTrace_append hprefix tailTrace_7453911
  have hstable : (prefixWord ++ tailWord_7453911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453911).length < 2 ^ (prefixWord ++ tailWord_7453911).sum := by decide
  have hdescent : baseEnd_7453911 < baseStart_7453911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453912 : List Nat := [2, 1, 2, 2, 6, 1, 1, 2, 1, 5]
def baseStart_7453912 : Nat := 118140960795 + 7453912 * 2 ^ 59
def prefixEnd_7453912 : Nat := 4983230072969 + 3 ^ 40 * 7453912 * 2
def baseEnd_7453912 : Nat := 1275813204105448589573363

theorem tailTrace_7453912 : CollatzResearch.WordTrace tailWord_7453912 prefixEnd_7453912 1275813204105448589573363 := by
  unfold tailWord_7453912
  simp only [CollatzResearch.WordTrace]
  refine ⟨135933252685878662831933995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181244336914504883775911993 135933252685878662831933995)
  ·
    refine ⟨203899879028817994247900993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135933252685878662831933995 203899879028817994247900993)
    ·
      refine ⟨152924909271613495685925745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203899879028817994247900993 152924909271613495685925745)
      ·
        refine ⟨114693681953710121764444309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152924909271613495685925745 114693681953710121764444309)
        ·
          refine ⟨5376266341580161957708327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 114693681953710121764444309 5376266341580161957708327)
          ·
            refine ⟨8064399512370242936562491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5376266341580161957708327 8064399512370242936562491)
            ·
              refine ⟨12096599268555364404843737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8064399512370242936562491 12096599268555364404843737)
              ·
                refine ⟨9072449451416523303632803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12096599268555364404843737 9072449451416523303632803)
                ·
                  refine ⟨13608674177124784955449205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9072449451416523303632803 13608674177124784955449205)
                  ·
                    refine ⟨1275813204105448589573363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13608674177124784955449205 1275813204105448589573363)
                    ·
                      rfl

theorem cell23_7453912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 1, 5].length) (baseStart_7453912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453912 prefixEnd_7453912 := by exact prefixLift 7453912
  have htrace : WordTrace (prefixWord ++ tailWord_7453912) baseStart_7453912 baseEnd_7453912 := by
    simpa [prefixWord, tailWord_7453912, baseEnd_7453912] using wordTrace_append hprefix tailTrace_7453912
  have hstable : (prefixWord ++ tailWord_7453912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453912).length < 2 ^ (prefixWord ++ tailWord_7453912).sum := by decide
  have hdescent : baseEnd_7453912 < baseStart_7453912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453921 : List Nat := [1, 2, 3, 1, 3, 2, 2, 9]
def baseStart_7453921 : Nat := 118140960795 + 7453921 * 2 ^ 59
def prefixEnd_7453921 : Nat := 4983230072969 + 3 ^ 40 * 7453921 * 2
def baseEnd_7453921 : Nat := 141757193838601341981761

theorem tailTrace_7453921 : CollatzResearch.WordTrace tailWord_7453921 prefixEnd_7453921 141757193838601341981761 := by
  unfold tailWord_7453921
  simp only [CollatzResearch.WordTrace]
  refine ⟨271866833628724720200945617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181244555752483146800630411 271866833628724720200945617)
  ·
    refine ⟨203900125221543540150709213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271866833628724720200945617 203900125221543540150709213)
    ·
      refine ⟨76462546958078827556515955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203900125221543540150709213 76462546958078827556515955)
      ·
        refine ⟨114693820437118241334773933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76462546958078827556515955 114693820437118241334773933)
        ·
          refine ⟨43010182663919340500540225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114693820437118241334773933 43010182663919340500540225)
          ·
            refine ⟨32257636997939505375405169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43010182663919340500540225 32257636997939505375405169)
            ·
              refine ⟨24193227748454629031553877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32257636997939505375405169 24193227748454629031553877)
              ·
                refine ⟨141757193838601341981761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24193227748454629031553877 141757193838601341981761)
                ·
                  rfl

theorem cell23_7453921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 9].length) (baseStart_7453921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453921 prefixEnd_7453921 := by exact prefixLift 7453921
  have htrace : WordTrace (prefixWord ++ tailWord_7453921) baseStart_7453921 baseEnd_7453921 := by
    simpa [prefixWord, tailWord_7453921, baseEnd_7453921] using wordTrace_append hprefix tailTrace_7453921
  have hstable : (prefixWord ++ tailWord_7453921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453921).length < 2 ^ (prefixWord ++ tailWord_7453921).sum := by decide
  have hdescent : baseEnd_7453921 < baseStart_7453921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453928 : List Nat := [2, 1, 4, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_7453928 : Nat := 118140960795 + 7453928 * 2 ^ 59
def prefixEnd_7453928 : Nat := 4983230072969 + 3 ^ 40 * 7453928 * 2
def baseEnd_7453928 : Nat := 3827447828006817706120015

theorem tailTrace_7453928 : CollatzResearch.WordTrace tailWord_7453928 prefixEnd_7453928 3827447828006817706120015 := by
  unfold tailWord_7453928
  simp only [CollatzResearch.WordTrace]
  refine ⟨135933544469849680198225219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181244725959799573597633625 135933544469849680198225219)
  ·
    refine ⟨203900316704774520297337829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135933544469849680198225219 203900316704774520297337829)
    ·
      refine ⟨38231309382145222555750843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203900316704774520297337829 38231309382145222555750843)
      ·
        refine ⟨57346964073217833833626265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38231309382145222555750843 57346964073217833833626265)
        ·
          refine ⟨43010223054913375375219699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57346964073217833833626265 43010223054913375375219699)
          ·
            refine ⟨64515334582370063062829549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43010223054913375375219699 64515334582370063062829549)
            ·
              refine ⟨24193250468388773648561081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64515334582370063062829549 24193250468388773648561081)
              ·
                refine ⟨18144937851291580236420811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24193250468388773648561081 18144937851291580236420811)
                ·
                  refine ⟨27217406776937370354631217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18144937851291580236420811 27217406776937370354631217)
                  ·
                    refine ⟨20413055082703027765973413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27217406776937370354631217 20413055082703027765973413)
                    ·
                      refine ⟨3827447828006817706120015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20413055082703027765973413 3827447828006817706120015)
                      ·
                        rfl

theorem cell23_7453928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_7453928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453928 prefixEnd_7453928 := by exact prefixLift 7453928
  have htrace : WordTrace (prefixWord ++ tailWord_7453928) baseStart_7453928 baseEnd_7453928 := by
    simpa [prefixWord, tailWord_7453928, baseEnd_7453928] using wordTrace_append hprefix tailTrace_7453928
  have hstable : (prefixWord ++ tailWord_7453928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453928).length < 2 ^ (prefixWord ++ tailWord_7453928).sum := by decide
  have hdescent : baseEnd_7453928 < baseStart_7453928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453935 : List Nat := [1, 1, 2, 1, 7, 2, 1, 1, 1, 1, 5]
def baseStart_7453935 : Nat := 118140960795 + 7453935 * 2 ^ 59
def prefixEnd_7453935 : Nat := 4983230072969 + 3 ^ 40 * 7453935 * 2
def baseEnd_7453935 : Nat := 3827451422371399178732483

theorem tailTrace_7453935 : CollatzResearch.WordTrace tailWord_7453935 prefixEnd_7453935 3827451422371399178732483 := by
  unfold tailWord_7453935
  simp only [CollatzResearch.WordTrace]
  refine ⟨271867344250674000591955259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181244896167116000394636839 271867344250674000591955259)
  ·
    refine ⟨407801016376011000887932889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271867344250674000591955259 407801016376011000887932889)
    ·
      refine ⟨305850762282008250665949667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407801016376011000887932889 305850762282008250665949667)
      ·
        refine ⟨458776143423012375998924501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305850762282008250665949667 458776143423012375998924501)
        ·
          refine ⟨10752565861476852562474793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 458776143423012375998924501 10752565861476852562474793)
          ·
            refine ⟨8064424396107639421856095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10752565861476852562474793 8064424396107639421856095)
            ·
              refine ⟨12096636594161459132784143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8064424396107639421856095 12096636594161459132784143)
              ·
                refine ⟨18144954891242188699176215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12096636594161459132784143 18144954891242188699176215)
                ·
                  refine ⟨27217432336863283048764323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18144954891242188699176215 27217432336863283048764323)
                  ·
                    refine ⟨40826148505294924573146485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27217432336863283048764323 40826148505294924573146485)
                    ·
                      refine ⟨3827451422371399178732483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40826148505294924573146485 3827451422371399178732483)
                      ·
                        rfl

theorem cell23_7453935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 1, 5].length) (baseStart_7453935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453935 prefixEnd_7453935 := by exact prefixLift 7453935
  have htrace : WordTrace (prefixWord ++ tailWord_7453935) baseStart_7453935 baseEnd_7453935 := by
    simpa [prefixWord, tailWord_7453935, baseEnd_7453935] using wordTrace_append hprefix tailTrace_7453935
  have hstable : (prefixWord ++ tailWord_7453935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453935).length < 2 ^ (prefixWord ++ tailWord_7453935).sum := by decide
  have hdescent : baseEnd_7453935 < baseStart_7453935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453938 : List Nat := [3, 2, 1, 3, 4, 10]
def baseStart_7453938 : Nat := 118140960795 + 7453938 * 2 ^ 59
def prefixEnd_7453938 : Nat := 4983230072969 + 3 ^ 40 * 7453938 * 2
def baseEnd_7453938 : Nat := 15750835237915072703683

theorem tailTrace_7453938 : CollatzResearch.WordTrace tailWord_7453938 prefixEnd_7453938 15750835237915072703683 := by
  unfold tailWord_7453938
  simp only [CollatzResearch.WordTrace]
  refine ⟨67966863417415783026078617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181244969113108754736209645 67966863417415783026078617)
  ·
    refine ⟨50975147563061837269558963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67966863417415783026078617 50975147563061837269558963)
    ·
      refine ⟨76462721344592755904338445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50975147563061837269558963 76462721344592755904338445)
      ·
        refine ⟨28673520504222283464126917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76462721344592755904338445 28673520504222283464126917)
        ·
          refine ⟨5376285094541678149523797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28673520504222283464126917 5376285094541678149523797)
          ·
            refine ⟨15750835237915072703683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5376285094541678149523797 15750835237915072703683)
            ·
              rfl

theorem cell23_7453938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 10].length) (baseStart_7453938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453938 prefixEnd_7453938 := by exact prefixLift 7453938
  have htrace : WordTrace (prefixWord ++ tailWord_7453938) baseStart_7453938 baseEnd_7453938 := by
    simpa [prefixWord, tailWord_7453938, baseEnd_7453938] using wordTrace_append hprefix tailTrace_7453938
  have hstable : (prefixWord ++ tailWord_7453938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453938).length < 2 ^ (prefixWord ++ tailWord_7453938).sum := by decide
  have hdescent : baseEnd_7453938 < baseStart_7453938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453951 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 2, 7]
def baseStart_7453951 : Nat := 118140960795 + 7453951 * 2 ^ 59
def prefixEnd_7453951 : Nat := 4983230072969 + 3 ^ 40 * 7453951 * 2
def baseEnd_7453951 : Nat := 1275819879353957038710803

theorem tailTrace_7453951 : CollatzResearch.WordTrace tailWord_7453951 prefixEnd_7453951 1275819879353957038710803 := by
  unfold tailWord_7453951
  simp only [CollatzResearch.WordTrace]
  refine ⟨271867927818616035324537707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181245285212410690216358471 271867927818616035324537707)
  ·
    refine ⟨407801891727924052986806561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271867927818616035324537707 407801891727924052986806561)
    ·
      refine ⟨305851418795943039740104921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407801891727924052986806561 305851418795943039740104921)
      ·
        refine ⟨229388564096957279805078691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305851418795943039740104921 229388564096957279805078691)
        ·
          refine ⟨344082846145435919707618037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229388564096957279805078691 344082846145435919707618037)
          ·
            refine ⟨32257766826134617472589191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 344082846145435919707618037 32257766826134617472589191)
            ·
              refine ⟨48386650239201926208883787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32257766826134617472589191 48386650239201926208883787)
              ·
                refine ⟨72579975358802889313325681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48386650239201926208883787 72579975358802889313325681)
                ·
                  refine ⟨54434981519102166984994261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72579975358802889313325681 54434981519102166984994261)
                  ·
                    refine ⟨1275819879353957038710803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54434981519102166984994261 1275819879353957038710803)
                    ·
                      rfl

theorem cell23_7453951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 7].length) (baseStart_7453951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453951 prefixEnd_7453951 := by exact prefixLift 7453951
  have htrace : WordTrace (prefixWord ++ tailWord_7453951) baseStart_7453951 baseEnd_7453951 := by
    simpa [prefixWord, tailWord_7453951, baseEnd_7453951] using wordTrace_append hprefix tailTrace_7453951
  have hstable : (prefixWord ++ tailWord_7453951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453951).length < 2 ^ (prefixWord ++ tailWord_7453951).sum := by decide
  have hdescent : baseEnd_7453951 < baseStart_7453951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453975 : List Nat := [1, 1, 3, 4, 1, 1, 1, 3, 3, 3, 2]
def baseStart_7453975 : Nat := 118140960795 + 7453975 * 2 ^ 59
def prefixEnd_7453975 : Nat := 4983230072969 + 3 ^ 40 * 7453975 * 2
def baseEnd_7453975 : Nat := 3827471961597579022232299

theorem tailTrace_7453975 : CollatzResearch.WordTrace tailWord_7453975 prefixEnd_7453975 3827471961597579022232299 := by
  unfold tailWord_7453975
  simp only [CollatzResearch.WordTrace]
  refine ⟨271868803170529087423411379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181245868780352724948940919 271868803170529087423411379)
  ·
    refine ⟨407803204755793631135117069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271868803170529087423411379 407803204755793631135117069)
    ·
      refine ⟨152926201783422611675668901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407803204755793631135117069 152926201783422611675668901)
      ·
        refine ⟨28673662834391739689187919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152926201783422611675668901 28673662834391739689187919)
        ·
          refine ⟨43010494251587609533781879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28673662834391739689187919 43010494251587609533781879)
          ·
            refine ⟨64515741377381414300672819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43010494251587609533781879 64515741377381414300672819)
            ·
              refine ⟨96773612066072121451009229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64515741377381414300672819 96773612066072121451009229)
              ·
                refine ⟨36290104524777045544128461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96773612066072121451009229 36290104524777045544128461)
                ·
                  refine ⟨13608789196791392079048173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36290104524777045544128461 13608789196791392079048173)
                  ·
                    refine ⟨5103295948796772029643065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13608789196791392079048173 5103295948796772029643065)
                    ·
                      refine ⟨3827471961597579022232299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5103295948796772029643065 3827471961597579022232299)
                      ·
                        rfl

theorem cell23_7453975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_7453975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453975 prefixEnd_7453975 := by exact prefixLift 7453975
  have htrace : WordTrace (prefixWord ++ tailWord_7453975) baseStart_7453975 baseEnd_7453975 := by
    simpa [prefixWord, tailWord_7453975, baseEnd_7453975] using wordTrace_append hprefix tailTrace_7453975
  have hstable : (prefixWord ++ tailWord_7453975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453975).length < 2 ^ (prefixWord ++ tailWord_7453975).sum := by decide
  have hdescent : baseEnd_7453975 < baseStart_7453975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7453986 : List Nat := [3, 3, 1, 1, 5, 1, 2, 1, 1, 2, 3]
def baseStart_7453986 : Nat := 118140960795 + 7453986 * 2 ^ 59
def prefixEnd_7453986 : Nat := 4983230072969 + 3 ^ 40 * 7453986 * 2
def baseEnd_7453986 : Nat := 3827477609884778479194749

theorem tailTrace_7453986 : CollatzResearch.WordTrace tailWord_7453986 prefixEnd_7453986 3827477609884778479194749 := by
  unfold tailWord_7453986
  simp only [CollatzResearch.WordTrace]
  refine ⟨67967301093372309075515453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181246136248992824201374541 67967301093372309075515453)
  ·
    refine ⟨25487737910014615903318295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67967301093372309075515453 25487737910014615903318295)
    ·
      refine ⟨38231606865021923854977443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25487737910014615903318295 38231606865021923854977443)
      ·
        refine ⟨57347410297532885782466165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38231606865021923854977443 57347410297532885782466165)
        ·
          refine ⟨5376319715393708042106203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57347410297532885782466165 5376319715393708042106203)
          ·
            refine ⟨8064479573090562063159305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5376319715393708042106203 8064479573090562063159305)
            ·
              refine ⟨6048359679817921547369479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8064479573090562063159305 6048359679817921547369479)
              ·
                refine ⟨9072539519726882321054219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6048359679817921547369479 9072539519726882321054219)
                ·
                  refine ⟨13608809279590323481581329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9072539519726882321054219 13608809279590323481581329)
                  ·
                    refine ⟨10206606959692742611185997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13608809279590323481581329 10206606959692742611185997)
                    ·
                      refine ⟨3827477609884778479194749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10206606959692742611185997 3827477609884778479194749)
                      ·
                        rfl

theorem cell23_7453986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_7453986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7453986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7453986 prefixEnd_7453986 := by exact prefixLift 7453986
  have htrace : WordTrace (prefixWord ++ tailWord_7453986) baseStart_7453986 baseEnd_7453986 := by
    simpa [prefixWord, tailWord_7453986, baseEnd_7453986] using wordTrace_append hprefix tailTrace_7453986
  have hstable : (prefixWord ++ tailWord_7453986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7453986).length < 2 ^ (prefixWord ++ tailWord_7453986).sum := by decide
  have hdescent : baseEnd_7453986 < baseStart_7453986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7453986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454021 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 1, 1, 9]
def baseStart_7454021 : Nat := 118140960795 + 7454021 * 2 ^ 59
def prefixEnd_7454021 : Nat := 4983230072969 + 3 ^ 40 * 7454021 * 2
def baseEnd_7454021 : Nat := 3827495581707685842257087

theorem tailTrace_7454021 : CollatzResearch.WordTrace tailWord_7454021 prefixEnd_7454021 3827495581707685842257087 := by
  unfold tailWord_7454021
  simp only [CollatzResearch.WordTrace]
  refine ⟨271870480928362437279585917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181246987285574958186390611 271870480928362437279585917)
  ·
    refine ⟨101951430348135913979844719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271870480928362437279585917 101951430348135913979844719)
    ·
      refine ⟨152927145522203870969767079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101951430348135913979844719 152927145522203870969767079)
      ·
        refine ⟨229390718283305806454650619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152927145522203870969767079 229390718283305806454650619)
        ·
          refine ⟨344086077424958709681975929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229390718283305806454650619 344086077424958709681975929)
          ·
            refine ⟨258064558068719032261481947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344086077424958709681975929 258064558068719032261481947)
            ·
              refine ⟨387096837103078548392222921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258064558068719032261481947 387096837103078548392222921)
              ·
                refine ⟨290322627827308911294167191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387096837103078548392222921 290322627827308911294167191)
                ·
                  refine ⟨435483941740963366941250787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 290322627827308911294167191 435483941740963366941250787)
                  ·
                    refine ⟨653225912611445050411876181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 435483941740963366941250787 653225912611445050411876181)
                    ·
                      refine ⟨3827495581707685842257087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 653225912611445050411876181 3827495581707685842257087)
                      ·
                        rfl

theorem cell23_7454021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_7454021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454021 prefixEnd_7454021 := by exact prefixLift 7454021
  have htrace : WordTrace (prefixWord ++ tailWord_7454021) baseStart_7454021 baseEnd_7454021 := by
    simpa [prefixWord, tailWord_7454021, baseEnd_7454021] using wordTrace_append hprefix tailTrace_7454021
  have hstable : (prefixWord ++ tailWord_7454021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454021).length < 2 ^ (prefixWord ++ tailWord_7454021).sum := by decide
  have hdescent : baseEnd_7454021 < baseStart_7454021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454028 : List Nat := [2, 2, 1, 3, 2, 2, 2, 2, 7]
def baseStart_7454028 : Nat := 118140960795 + 7454028 * 2 ^ 59
def prefixEnd_7454028 : Nat := 4983230072969 + 3 ^ 40 * 7454028 * 2
def baseEnd_7454028 : Nat := 425277686230251923874395

theorem tailTrace_7454028 : CollatzResearch.WordTrace tailWord_7454028 prefixEnd_7454028 425277686230251923874395 := by
  unfold tailWord_7454028
  simp only [CollatzResearch.WordTrace]
  refine ⟨135935368119668538737545369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181247157492891384983393825 135935368119668538737545369)
  ·
    refine ⟨101951526089751404053159027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135935368119668538737545369 101951526089751404053159027)
    ·
      refine ⟨152927289134627106079738541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101951526089751404053159027 152927289134627106079738541)
      ·
        refine ⟨57347733425485164779901953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152927289134627106079738541 57347733425485164779901953)
        ·
          refine ⟨43010800069113873584926465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57347733425485164779901953 43010800069113873584926465)
          ·
            refine ⟨32258100051835405188694849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43010800069113873584926465 32258100051835405188694849)
            ·
              refine ⟨24193575038876553891521137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32258100051835405188694849 24193575038876553891521137)
              ·
                refine ⟨18145181279157415418640853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24193575038876553891521137 18145181279157415418640853)
                ·
                  refine ⟨425277686230251923874395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18145181279157415418640853 425277686230251923874395)
                  ·
                    rfl

theorem cell23_7454028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 7].length) (baseStart_7454028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454028 prefixEnd_7454028 := by exact prefixLift 7454028
  have htrace : WordTrace (prefixWord ++ tailWord_7454028) baseStart_7454028 baseEnd_7454028 := by
    simpa [prefixWord, tailWord_7454028, baseEnd_7454028] using wordTrace_append hprefix tailTrace_7454028
  have hstable : (prefixWord ++ tailWord_7454028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454028).length < 2 ^ (prefixWord ++ tailWord_7454028).sum := by decide
  have hdescent : baseEnd_7454028 < baseStart_7454028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454031 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 6]
def baseStart_7454031 : Nat := 118140960795 + 7454031 * 2 ^ 59
def prefixEnd_7454031 : Nat := 4983230072969 + 3 ^ 40 * 7454031 * 2
def baseEnd_7454031 : Nat := 3827500716514230803132041

theorem tailTrace_7454031 : CollatzResearch.WordTrace tailWord_7454031 prefixEnd_7454031 3827500716514230803132041 := by
  unfold tailWord_7454031
  simp only [CollatzResearch.WordTrace]
  refine ⟨271870845658326208987449947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181247230438884139324966631 271870845658326208987449947)
  ·
    refine ⟨407806268487489313481174921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271870845658326208987449947 407806268487489313481174921)
    ·
      refine ⟨305854701365616985110881191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407806268487489313481174921 305854701365616985110881191)
      ·
        refine ⟨458782052048425477666321787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305854701365616985110881191 458782052048425477666321787)
        ·
          refine ⟨688173078072638216499482681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458782052048425477666321787 688173078072638216499482681)
          ·
            refine ⟨516129808554478662374612011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 688173078072638216499482681 516129808554478662374612011)
            ·
              refine ⟨774194712831717993561918017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516129808554478662374612011 774194712831717993561918017)
              ·
                refine ⟨580646034623788495171438513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 774194712831717993561918017 580646034623788495171438513)
                ·
                  refine ⟨435484525967841371378578885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 580646034623788495171438513 435484525967841371378578885)
                  ·
                    refine ⟨81653348618970257133483541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 435484525967841371378578885 81653348618970257133483541)
                    ·
                      refine ⟨3827500716514230803132041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81653348618970257133483541 3827500716514230803132041)
                      ·
                        rfl

theorem cell23_7454031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 6].length) (baseStart_7454031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454031 prefixEnd_7454031 := by exact prefixLift 7454031
  have htrace : WordTrace (prefixWord ++ tailWord_7454031) baseStart_7454031 baseEnd_7454031 := by
    simpa [prefixWord, tailWord_7454031, baseEnd_7454031] using wordTrace_append hprefix tailTrace_7454031
  have hstable : (prefixWord ++ tailWord_7454031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454031).length < 2 ^ (prefixWord ++ tailWord_7454031).sum := by decide
  have hdescent : baseEnd_7454031 < baseStart_7454031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454115 : List Nat := [1, 1, 1, 4, 1, 3, 1, 4, 2, 2, 3]
def baseStart_7454115 : Nat := 118140960795 + 7454115 * 2 ^ 59
def prefixEnd_7454115 : Nat := 4983230072969 + 3 ^ 40 * 7454115 * 2
def baseEnd_7454115 : Nat := 3827543848889208474481655

theorem tailTrace_7454115 : CollatzResearch.WordTrace tailWord_7454115 prefixEnd_7454115 3827543848889208474481655 := by
  unfold tailWord_7454115
  simp only [CollatzResearch.WordTrace]
  refine ⟨271873909390021891333507799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181249272926681260889005199 271873909390021891333507799)
  ·
    refine ⟨407810864085032837000261699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271873909390021891333507799 407810864085032837000261699)
    ·
      refine ⟨611716296127549255500392549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407810864085032837000261699 611716296127549255500392549)
      ·
        refine ⟨114696805523915485406323603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 611716296127549255500392549 114696805523915485406323603)
        ·
          refine ⟨172045208285873228109485405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114696805523915485406323603 172045208285873228109485405)
          ·
            refine ⟨64516953107202460541057027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172045208285873228109485405 64516953107202460541057027)
            ·
              refine ⟨96775429660803690811585541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64516953107202460541057027 96775429660803690811585541)
              ·
                refine ⟨18145393061400692027172289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96775429660803690811585541 18145393061400692027172289)
                ·
                  refine ⟨13609044796050519020379217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18145393061400692027172289 13609044796050519020379217)
                  ·
                    refine ⟨10206783597037889265284413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13609044796050519020379217 10206783597037889265284413)
                    ·
                      refine ⟨3827543848889208474481655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10206783597037889265284413 3827543848889208474481655)
                      ·
                        rfl

theorem cell23_7454115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_7454115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454115 prefixEnd_7454115 := by exact prefixLift 7454115
  have htrace : WordTrace (prefixWord ++ tailWord_7454115) baseStart_7454115 baseEnd_7454115 := by
    simpa [prefixWord, tailWord_7454115, baseEnd_7454115] using wordTrace_append hprefix tailTrace_7454115
  have hstable : (prefixWord ++ tailWord_7454115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454115).length < 2 ^ (prefixWord ++ tailWord_7454115).sum := by decide
  have hdescent : baseEnd_7454115 < baseStart_7454115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454179 : List Nat := [1, 1, 1, 6, 2, 2, 2, 1, 3, 1, 3]
def baseStart_7454179 : Nat := 118140960795 + 7454179 * 2 ^ 59
def prefixEnd_7454179 : Nat := 4983230072969 + 3 ^ 40 * 7454179 * 2
def baseEnd_7454179 : Nat := 3827576711651096224081361

theorem tailTrace_7454179 : CollatzResearch.WordTrace tailWord_7454179 prefixEnd_7454179 3827576711651096224081361 := by
  unfold tailWord_7454179
  simp only [CollatzResearch.WordTrace]
  refine ⟨271876243661790030263837591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181250829107860020175891727 271876243661790030263837591)
  ·
    refine ⟨407814365492685045395756387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271876243661790030263837591 407814365492685045395756387)
    ·
      refine ⟨611721548239027568093634581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407814365492685045395756387 611721548239027568093634581)
      ·
        refine ⟨28674447573704417254389121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 611721548239027568093634581 28674447573704417254389121)
        ·
          refine ⟨21505835680278312940791841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28674447573704417254389121 21505835680278312940791841)
          ·
            refine ⟨16129376760208734705593881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21505835680278312940791841 16129376760208734705593881)
            ·
              refine ⟨12097032570156551029195411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16129376760208734705593881 12097032570156551029195411)
              ·
                refine ⟨18145548855234826543793117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12097032570156551029195411 18145548855234826543793117)
                ·
                  refine ⟨6804580820713059953922419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18145548855234826543793117 6804580820713059953922419)
                  ·
                    refine ⟨10206871231069589930883629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6804580820713059953922419 10206871231069589930883629)
                    ·
                      refine ⟨3827576711651096224081361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10206871231069589930883629 3827576711651096224081361)
                      ·
                        rfl

theorem cell23_7454179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_7454179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454179 prefixEnd_7454179 := by exact prefixLift 7454179
  have htrace : WordTrace (prefixWord ++ tailWord_7454179) baseStart_7454179 baseEnd_7454179 := by
    simpa [prefixWord, tailWord_7454179, baseEnd_7454179] using wordTrace_append hprefix tailTrace_7454179
  have hstable : (prefixWord ++ tailWord_7454179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454179).length < 2 ^ (prefixWord ++ tailWord_7454179).sum := by decide
  have hdescent : baseEnd_7454179 < baseStart_7454179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454202 : List Nat := [3, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4]
def baseStart_7454202 : Nat := 118140960795 + 7454202 * 2 ^ 59
def prefixEnd_7454202 : Nat := 4983230072969 + 3 ^ 40 * 7454202 * 2
def baseEnd_7454202 : Nat := 3827588521706149634093755

theorem tailTrace_7454202 : CollatzResearch.WordTrace tailWord_7454202 prefixEnd_7454202 3827588521706149634093755 := by
  unfold tailWord_7454202
  simp only [CollatzResearch.WordTrace]
  refine ⟨67969270635176676297981215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181251388360471136794616573 67969270635176676297981215)
  ·
    refine ⟨101953905952765014446971823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67969270635176676297981215 101953905952765014446971823)
    ·
      refine ⟨152930858929147521670457735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101953905952765014446971823 152930858929147521670457735)
      ·
        refine ⟨229396288393721282505686603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152930858929147521670457735 229396288393721282505686603)
        ·
          refine ⟨344094432590581923758529905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229396288393721282505686603 344094432590581923758529905)
          ·
            refine ⟨258070824442936442818897429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344094432590581923758529905 258070824442936442818897429)
            ·
              refine ⟨12097069895762645757135817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 258070824442936442818897429 12097069895762645757135817)
              ·
                refine ⟨9072802421821984317851863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12097069895762645757135817 9072802421821984317851863)
                ·
                  refine ⟨13609203632732976476777795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9072802421821984317851863 13609203632732976476777795)
                  ·
                    refine ⟨20413805449099464715166693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13609203632732976476777795 20413805449099464715166693)
                    ·
                      refine ⟨3827588521706149634093755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20413805449099464715166693 3827588521706149634093755)
                      ·
                        rfl

theorem cell23_7454202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4].length) (baseStart_7454202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454202 prefixEnd_7454202 := by exact prefixLift 7454202
  have htrace : WordTrace (prefixWord ++ tailWord_7454202) baseStart_7454202 baseEnd_7454202 := by
    simpa [prefixWord, tailWord_7454202, baseEnd_7454202] using wordTrace_append hprefix tailTrace_7454202
  have hstable : (prefixWord ++ tailWord_7454202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454202).length < 2 ^ (prefixWord ++ tailWord_7454202).sum := by decide
  have hdescent : baseEnd_7454202 < baseStart_7454202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454269 : List Nat := [1, 4, 1, 3, 3, 1, 1, 2, 1, 3, 3]
def baseStart_7454269 : Nat := 118140960795 + 7454269 * 2 ^ 59
def prefixEnd_7454269 : Nat := 4983230072969 + 3 ^ 40 * 7454269 * 2
def baseEnd_7454269 : Nat := 3827622924910000871955947

theorem tailTrace_7454269 : CollatzResearch.WordTrace tailWord_7454269 prefixEnd_7454269 3827622924910000871955947 := by
  unfold tailWord_7454269
  simp only [CollatzResearch.WordTrace]
  refine ⟨271879526231463975634613861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181253017487642650423075907 271879526231463975634613861)
  ·
    refine ⟨50977411168399495431490099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271879526231463975634613861 50977411168399495431490099)
    ·
      refine ⟨76466116752599243147235149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50977411168399495431490099 76466116752599243147235149)
      ·
        refine ⟨28674793782224716180213181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76466116752599243147235149 28674793782224716180213181)
        ·
          refine ⟨10753047668334268567579943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28674793782224716180213181 10753047668334268567579943)
          ·
            refine ⟨16129571502501402851369915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10753047668334268567579943 16129571502501402851369915)
            ·
              refine ⟨24194357253752104277054873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16129571502501402851369915 24194357253752104277054873)
              ·
                refine ⟨18145767940314078207791155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24194357253752104277054873 18145767940314078207791155)
                ·
                  refine ⟨27218651910471117311686733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18145767940314078207791155 27218651910471117311686733)
                  ·
                    refine ⟨10206994466426668991882525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27218651910471117311686733 10206994466426668991882525)
                    ·
                      refine ⟨3827622924910000871955947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10206994466426668991882525 3827622924910000871955947)
                      ·
                        rfl

theorem cell23_7454269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_7454269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454269 prefixEnd_7454269 := by exact prefixLift 7454269
  have htrace : WordTrace (prefixWord ++ tailWord_7454269) baseStart_7454269 baseEnd_7454269 := by
    simpa [prefixWord, tailWord_7454269, baseEnd_7454269] using wordTrace_append hprefix tailTrace_7454269
  have hstable : (prefixWord ++ tailWord_7454269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454269).length < 2 ^ (prefixWord ++ tailWord_7454269).sum := by decide
  have hdescent : baseEnd_7454269 < baseStart_7454269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454309 : List Nat := [1, 3, 1, 3, 3, 1, 1, 3, 1, 4, 2]
def baseStart_7454309 : Nat := 118140960795 + 7454309 * 2 ^ 59
def prefixEnd_7454309 : Nat := 4983230072969 + 3 ^ 40 * 7454309 * 2
def baseEnd_7454309 : Nat := 3827643464136180715455763

theorem tailTrace_7454309 : CollatzResearch.WordTrace tailWord_7454309 prefixEnd_7454309 3827643464136180715455763 := by
  unfold tailWord_7454309
  simp only [CollatzResearch.WordTrace]
  refine ⟨271880985151319062466069981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181253990100879374977379987 271880985151319062466069981)
  ·
    refine ⟨101955369431744648424776243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271880985151319062466069981 101955369431744648424776243)
    ·
      refine ⟨152933054147616972637164365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101955369431744648424776243 152933054147616972637164365)
      ·
        refine ⟨57349895305356364738936637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152933054147616972637164365 57349895305356364738936637)
        ·
          refine ⟨21506210739508636777101239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57349895305356364738936637 21506210739508636777101239)
          ·
            refine ⟨32259316109262955165651859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21506210739508636777101239 32259316109262955165651859)
            ·
              refine ⟨48388974163894432748477789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32259316109262955165651859 48388974163894432748477789)
              ·
                refine ⟨18145865311460412280679171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48388974163894432748477789 18145865311460412280679171)
                ·
                  refine ⟨27218797967190618421018757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18145865311460412280679171 27218797967190618421018757)
                  ·
                    refine ⟨5103524618848240953941017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27218797967190618421018757 5103524618848240953941017)
                    ·
                      refine ⟨3827643464136180715455763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5103524618848240953941017 3827643464136180715455763)
                      ·
                        rfl

theorem cell23_7454309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_7454309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454309 prefixEnd_7454309 := by exact prefixLift 7454309
  have htrace : WordTrace (prefixWord ++ tailWord_7454309) baseStart_7454309 baseEnd_7454309 := by
    simpa [prefixWord, tailWord_7454309, baseEnd_7454309] using wordTrace_append hprefix tailTrace_7454309
  have hstable : (prefixWord ++ tailWord_7454309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454309).length < 2 ^ (prefixWord ++ tailWord_7454309).sum := by decide
  have hdescent : baseEnd_7454309 < baseStart_7454309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454326 : List Nat := [5, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2]
def baseStart_7454326 : Nat := 118140960795 + 7454326 * 2 ^ 59
def prefixEnd_7454326 : Nat := 4983230072969 + 3 ^ 40 * 7454326 * 2
def baseEnd_7454326 : Nat := 3827652193307307148943185

theorem tailTrace_7454326 : CollatzResearch.WordTrace tailWord_7454326 prefixEnd_7454326 3827652193307307148943185 := by
  unfold tailWord_7454326
  simp only [CollatzResearch.WordTrace]
  refine ⟨16992600324516092148089927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181254403461504982912959221 16992600324516092148089927)
  ·
    refine ⟨25488900486774138222134891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16992600324516092148089927 25488900486774138222134891)
    ·
      refine ⟨38233350730161207333202337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25488900486774138222134891 38233350730161207333202337)
      ·
        refine ⟨28675013047620905499901753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38233350730161207333202337 28675013047620905499901753)
        ·
          refine ⟨21506259785715679124926315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28675013047620905499901753 21506259785715679124926315)
          ·
            refine ⟨32259389678573518687389473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21506259785715679124926315 32259389678573518687389473)
            ·
              refine ⟨24194542258930139015542105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32259389678573518687389473 24194542258930139015542105)
              ·
                refine ⟨18145906694197604261656579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24194542258930139015542105 18145906694197604261656579)
                ·
                  refine ⟨27218860041296406392484869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18145906694197604261656579 27218860041296406392484869)
                  ·
                    refine ⟨5103536257743076198590913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27218860041296406392484869 5103536257743076198590913)
                    ·
                      refine ⟨3827652193307307148943185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5103536257743076198590913 3827652193307307148943185)
                      ·
                        rfl

theorem cell23_7454326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_7454326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454326 prefixEnd_7454326 := by exact prefixLift 7454326
  have htrace : WordTrace (prefixWord ++ tailWord_7454326) baseStart_7454326 baseEnd_7454326 := by
    simpa [prefixWord, tailWord_7454326, baseEnd_7454326] using wordTrace_append hprefix tailTrace_7454326
  have hstable : (prefixWord ++ tailWord_7454326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454326).length < 2 ^ (prefixWord ++ tailWord_7454326).sum := by decide
  have hdescent : baseEnd_7454326 < baseStart_7454326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454343 : List Nat := [1, 1, 4, 2, 1, 5, 1, 2, 2, 2, 2]
def baseStart_7454343 : Nat := 118140960795 + 7454343 * 2 ^ 59
def prefixEnd_7454343 : Nat := 4983230072969 + 3 ^ 40 * 7454343 * 2
def baseEnd_7454343 : Nat := 3827660922478433582430607

theorem tailTrace_7454343 : CollatzResearch.WordTrace tailWord_7454343 prefixEnd_7454343 3827660922478433582430607 := by
  unfold tailWord_7454343
  simp only [CollatzResearch.WordTrace]
  refine ⟨271882225233195886272807683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181254816822130590848538455 271882225233195886272807683)
  ·
    refine ⟨407823337849793829409211525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271882225233195886272807683 407823337849793829409211525)
    ·
      refine ⟨76466875846836343014227161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 407823337849793829409211525 76466875846836343014227161)
      ·
        refine ⟨57350156885127257260670371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76466875846836343014227161 57350156885127257260670371)
        ·
          refine ⟨86025235327690885891005557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57350156885127257260670371 86025235327690885891005557)
          ·
            refine ⟨8064865811971020552281771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86025235327690885891005557 8064865811971020552281771)
            ·
              refine ⟨12097298717956530828422657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8064865811971020552281771 12097298717956530828422657)
              ·
                refine ⟨9072974038467398121316993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12097298717956530828422657 9072974038467398121316993)
                ·
                  refine ⟨6804730528850548590987745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9072974038467398121316993 6804730528850548590987745)
                  ·
                    refine ⟨5103547896637911443240809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6804730528850548590987745 5103547896637911443240809)
                    ·
                      refine ⟨3827660922478433582430607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5103547896637911443240809 3827660922478433582430607)
                      ·
                        rfl

theorem cell23_7454343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_7454343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454343 prefixEnd_7454343 := by exact prefixLift 7454343
  have htrace : WordTrace (prefixWord ++ tailWord_7454343) baseStart_7454343 baseEnd_7454343 := by
    simpa [prefixWord, tailWord_7454343, baseEnd_7454343] using wordTrace_append hprefix tailTrace_7454343
  have hstable : (prefixWord ++ tailWord_7454343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454343).length < 2 ^ (prefixWord ++ tailWord_7454343).sum := by decide
  have hdescent : baseEnd_7454343 < baseStart_7454343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454352 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 1, 7, 2]
def baseStart_7454352 : Nat := 118140960795 + 7454352 * 2 ^ 59
def prefixEnd_7454352 : Nat := 4983230072969 + 3 ^ 40 * 7454352 * 2
def baseEnd_7454352 : Nat := 3827665543804324047218065

theorem tailTrace_7454352 : CollatzResearch.WordTrace tailWord_7454352 prefixEnd_7454352 3827665543804324047218065 := by
  unfold tailWord_7454352
  simp only [CollatzResearch.WordTrace]
  refine ⟨135941276745081640404942655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181255035660108853873256873 135941276745081640404942655)
  ·
    refine ⟨203911915117622460607413983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135941276745081640404942655 203911915117622460607413983)
    ·
      refine ⟨305867872676433690911120975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203911915117622460607413983 305867872676433690911120975)
      ·
        refine ⟨458801809014650536366681463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305867872676433690911120975 458801809014650536366681463)
        ·
          refine ⟨688202713521975804550022195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458801809014650536366681463 688202713521975804550022195)
          ·
            refine ⟨1032304070282963706825033293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688202713521975804550022195 1032304070282963706825033293)
            ·
              refine ⟨387114026356111390059387485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1032304070282963706825033293 387114026356111390059387485)
              ·
                refine ⟨145167759883541771272270307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 387114026356111390059387485 145167759883541771272270307)
                ·
                  refine ⟨217751639825312656908405461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145167759883541771272270307 217751639825312656908405461)
                  ·
                    refine ⟨5103554058405765396290753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 217751639825312656908405461 5103554058405765396290753)
                    ·
                      refine ⟨3827665543804324047218065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5103554058405765396290753 3827665543804324047218065)
                      ·
                        rfl

theorem cell23_7454352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 7, 2].length) (baseStart_7454352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454352 prefixEnd_7454352 := by exact prefixLift 7454352
  have htrace : WordTrace (prefixWord ++ tailWord_7454352) baseStart_7454352 baseEnd_7454352 := by
    simpa [prefixWord, tailWord_7454352, baseEnd_7454352] using wordTrace_append hprefix tailTrace_7454352
  have hstable : (prefixWord ++ tailWord_7454352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454352).length < 2 ^ (prefixWord ++ tailWord_7454352).sum := by decide
  have hdescent : baseEnd_7454352 < baseStart_7454352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454392 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 5, 4]
def baseStart_7454392 : Nat := 118140960795 + 7454392 * 2 ^ 59
def prefixEnd_7454392 : Nat := 4983230072969 + 3 ^ 40 * 7454392 * 2
def baseEnd_7454392 : Nat := 1275895361010167963572627

theorem tailTrace_7454392 : CollatzResearch.WordTrace tailWord_7454392 prefixEnd_7454392 1275895361010167963572627 := by
  unfold tailWord_7454392
  simp only [CollatzResearch.WordTrace]
  refine ⟨135942006205009183820670715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181256008273345578427560953 135942006205009183820670715)
  ·
    refine ⟨203913009307513775731006073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135942006205009183820670715 203913009307513775731006073)
    ·
      refine ⟨152934756980635331798254555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203913009307513775731006073 152934756980635331798254555)
      ·
        refine ⟨229402135470952997697381833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152934756980635331798254555 229402135470952997697381833)
        ·
          refine ⟨172051601603214748273036375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229402135470952997697381833 172051601603214748273036375)
          ·
            refine ⟨258077402404822122409554563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172051601603214748273036375 258077402404822122409554563)
            ·
              refine ⟨387116103607233183614331845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258077402404822122409554563 387116103607233183614331845)
              ·
                refine ⟨72584269426356221927687221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 387116103607233183614331845 72584269426356221927687221)
                ·
                  refine ⟨6804775258720895805720677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72584269426356221927687221 6804775258720895805720677)
                  ·
                    refine ⟨1275895361010167963572627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6804775258720895805720677 1275895361010167963572627)
                    ·
                      rfl

theorem cell23_7454392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 5, 4].length) (baseStart_7454392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454392 prefixEnd_7454392 := by exact prefixLift 7454392
  have htrace : WordTrace (prefixWord ++ tailWord_7454392) baseStart_7454392 baseEnd_7454392 := by
    simpa [prefixWord, tailWord_7454392, baseEnd_7454392] using wordTrace_append hprefix tailTrace_7454392
  have hstable : (prefixWord ++ tailWord_7454392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454392).length < 2 ^ (prefixWord ++ tailWord_7454392).sum := by decide
  have hdescent : baseEnd_7454392 < baseStart_7454392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454395 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 6]
def baseStart_7454395 : Nat := 118140960795 + 7454395 * 2 ^ 59
def prefixEnd_7454395 : Nat := 4983230072969 + 3 ^ 40 * 7454395 * 2
def baseEnd_7454395 : Nat := 3827687623472467378980367

theorem tailTrace_7454395 : CollatzResearch.WordTrace tailWord_7454395 prefixEnd_7454395 3827687623472467378980367 := by
  unfold tailWord_7454395
  simp only [CollatzResearch.WordTrace]
  refine ⟨271884121829007499153700639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181256081219338332769133759 271884121829007499153700639)
  ·
    refine ⟨407826182743511248730550959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271884121829007499153700639 407826182743511248730550959)
    ·
      refine ⟨611739274115266873095826439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407826182743511248730550959 611739274115266873095826439)
      ·
        refine ⟨917608911172900309643739659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611739274115266873095826439 917608911172900309643739659)
        ·
          refine ⟨1376413366759350464465609489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 917608911172900309643739659 1376413366759350464465609489)
          ·
            refine ⟨1032310025069512848349207117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1376413366759350464465609489 1032310025069512848349207117)
            ·
              refine ⟨387116259401067318130952669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1032310025069512848349207117 387116259401067318130952669)
              ·
                refine ⟨145168597275400244299107251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 387116259401067318130952669 145168597275400244299107251)
                ·
                  refine ⟨217752895913100366448660877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145168597275400244299107251 217752895913100366448660877)
                  ·
                    refine ⟨81657335967412637418247829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 217752895913100366448660877 81657335967412637418247829)
                    ·
                      refine ⟨3827687623472467378980367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81657335967412637418247829 3827687623472467378980367)
                      ·
                        rfl

theorem cell23_7454395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 6].length) (baseStart_7454395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454395 prefixEnd_7454395 := by exact prefixLift 7454395
  have htrace : WordTrace (prefixWord ++ tailWord_7454395) baseStart_7454395 baseEnd_7454395 := by
    simpa [prefixWord, tailWord_7454395, baseEnd_7454395] using wordTrace_append hprefix tailTrace_7454395
  have hstable : (prefixWord ++ tailWord_7454395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454395).length < 2 ^ (prefixWord ++ tailWord_7454395).sum := by decide
  have hdescent : baseEnd_7454395 < baseStart_7454395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454406 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_7454406 : Nat := 118140960795 + 7454406 * 2 ^ 59
def prefixEnd_7454406 : Nat := 4983230072969 + 3 ^ 40 * 7454406 * 2
def baseEnd_7454406 : Nat := 3827693271759666835942817

theorem tailTrace_7454406 : CollatzResearch.WordTrace tailWord_7454406 prefixEnd_7454406 3827693271759666835942817 := by
  unfold tailWord_7454406
  simp only [CollatzResearch.WordTrace]
  refine ⟨8496391344748989001010971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 181256348687978432021567381 8496391344748989001010971)
  ·
    refine ⟨12744587017123483501516457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8496391344748989001010971 12744587017123483501516457)
    ·
      refine ⟨9558440262842612626137343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12744587017123483501516457 9558440262842612626137343)
      ·
        refine ⟨14337660394263918939206015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9558440262842612626137343 14337660394263918939206015)
        ·
          refine ⟨21506490591395878408809023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14337660394263918939206015 21506490591395878408809023)
          ·
            refine ⟨32259735887093817613213535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21506490591395878408809023 32259735887093817613213535)
            ·
              refine ⟨48389603830640726419820303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32259735887093817613213535 48389603830640726419820303)
              ·
                refine ⟨72584405745961089629730455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48389603830640726419820303 72584405745961089629730455)
                ·
                  refine ⟨108876608618941634444595683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72584405745961089629730455 108876608618941634444595683)
                  ·
                    refine ⟨163314912928412451666893525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108876608618941634444595683 163314912928412451666893525)
                    ·
                      refine ⟨3827693271759666835942817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163314912928412451666893525 3827693271759666835942817)
                      ·
                        rfl

theorem cell23_7454406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_7454406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454406 prefixEnd_7454406 := by exact prefixLift 7454406
  have htrace : WordTrace (prefixWord ++ tailWord_7454406) baseStart_7454406 baseEnd_7454406 := by
    simpa [prefixWord, tailWord_7454406, baseEnd_7454406] using wordTrace_append hprefix tailTrace_7454406
  have hstable : (prefixWord ++ tailWord_7454406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454406).length < 2 ^ (prefixWord ++ tailWord_7454406).sum := by decide
  have hdescent : baseEnd_7454406 < baseStart_7454406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454432 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 3]
def baseStart_7454432 : Nat := 118140960795 + 7454432 * 2 ^ 59
def prefixEnd_7454432 : Nat := 4983230072969 + 3 ^ 40 * 7454432 * 2
def baseEnd_7454432 : Nat := 3827706622256683734217697

theorem tailTrace_7454432 : CollatzResearch.WordTrace tailWord_7454432 prefixEnd_7454432 3827706622256683734217697 := by
  unfold tailWord_7454432
  simp only [CollatzResearch.WordTrace]
  refine ⟨135942735664936727236398775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181256980886582302981865033 135942735664936727236398775)
  ·
    refine ⟨203914103497405090854598163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135942735664936727236398775 203914103497405090854598163)
    ·
      refine ⟨305871155246107636281897245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203914103497405090854598163 305871155246107636281897245)
      ·
        refine ⟨114701683217290363605711467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305871155246107636281897245 114701683217290363605711467)
        ·
          refine ⟨172052524825935545408567201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114701683217290363605711467 172052524825935545408567201)
          ·
            refine ⟨129039393619451659056425401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172052524825935545408567201 129039393619451659056425401)
            ·
              refine ⟨96779545214588744292319051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129039393619451659056425401 96779545214588744292319051)
              ·
                refine ⟨145169317821883116438478577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96779545214588744292319051 145169317821883116438478577)
                ·
                  refine ⟨108876988366412337328858933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145169317821883116438478577 108876988366412337328858933)
                  ·
                    refine ⟨10207217659351156624580525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108876988366412337328858933 10207217659351156624580525)
                    ·
                      refine ⟨3827706622256683734217697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10207217659351156624580525 3827706622256683734217697)
                      ·
                        rfl

theorem cell23_7454432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_7454432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454432 prefixEnd_7454432 := by exact prefixLift 7454432
  have htrace : WordTrace (prefixWord ++ tailWord_7454432) baseStart_7454432 baseEnd_7454432 := by
    simpa [prefixWord, tailWord_7454432, baseEnd_7454432] using wordTrace_append hprefix tailTrace_7454432
  have hstable : (prefixWord ++ tailWord_7454432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454432).length < 2 ^ (prefixWord ++ tailWord_7454432).sum := by decide
  have hdescent : baseEnd_7454432 < baseStart_7454432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454459 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 4, 3, 2]
def baseStart_7454459 : Nat := 118140960795 + 7454459 * 2 ^ 59
def prefixEnd_7454459 : Nat := 4983230072969 + 3 ^ 40 * 7454459 * 2
def baseEnd_7454459 : Nat := 3827720486234355128580073

theorem tailTrace_7454459 : CollatzResearch.WordTrace tailWord_7454459 prefixEnd_7454459 3827720486234355128580073 := by
  unfold tailWord_7454459
  simp only [CollatzResearch.WordTrace]
  refine ⟨271886456100775638084030431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181257637400517092056020287 271886456100775638084030431)
  ·
    refine ⟨407829684151163457126045647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271886456100775638084030431 407829684151163457126045647)
    ·
      refine ⟨611744526226745185689068471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407829684151163457126045647 611744526226745185689068471)
      ·
        refine ⟨917616789340117778533602707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611744526226745185689068471 917616789340117778533602707)
        ·
          refine ⟨1376425184010176667800404061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 917616789340117778533602707 1376425184010176667800404061)
          ·
            refine ⟨516159444003816250425151523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1376425184010176667800404061 516159444003816250425151523)
            ·
              refine ⟨774239166005724375637727285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516159444003816250425151523 774239166005724375637727285)
              ·
                refine ⟨72584921813036660216036933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 774239166005724375637727285 72584921813036660216036933)
                ·
                  refine ⟨13609672839944373790506925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72584921813036660216036933 13609672839944373790506925)
                  ·
                    refine ⟨5103627314979140171440097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13609672839944373790506925 5103627314979140171440097)
                    ·
                      refine ⟨3827720486234355128580073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5103627314979140171440097 3827720486234355128580073)
                      ·
                        rfl

theorem cell23_7454459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 3, 2].length) (baseStart_7454459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454459 prefixEnd_7454459 := by exact prefixLift 7454459
  have htrace : WordTrace (prefixWord ++ tailWord_7454459) baseStart_7454459 baseEnd_7454459 := by
    simpa [prefixWord, tailWord_7454459, baseEnd_7454459] using wordTrace_append hprefix tailTrace_7454459
  have hstable : (prefixWord ++ tailWord_7454459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454459).length < 2 ^ (prefixWord ++ tailWord_7454459).sum := by decide
  have hdescent : baseEnd_7454459 < baseStart_7454459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454477 : List Nat := [1, 7, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_7454477 : Nat := 118140960795 + 7454477 * 2 ^ 59
def prefixEnd_7454477 : Nat := 4983230072969 + 3 ^ 40 * 7454477 * 2
def baseEnd_7454477 : Nat := 1275909909628712019384997

theorem tailTrace_7454477 : CollatzResearch.WordTrace tailWord_7454477 prefixEnd_7454477 1275909909628712019384997 := by
  unfold tailWord_7454477
  simp only [CollatzResearch.WordTrace]
  refine ⟨271887112614710427158185685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181258075076473618105457123 271887112614710427158185685)
  ·
    refine ⟨6372354201907275636519977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 271887112614710427158185685 6372354201907275636519977)
    ·
      refine ⟨4779265651430456727389983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6372354201907275636519977 4779265651430456727389983)
      ·
        refine ⟨7168898477145685091084975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4779265651430456727389983 7168898477145685091084975)
        ·
          refine ⟨10753347715718527636627463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7168898477145685091084975 10753347715718527636627463)
          ·
            refine ⟨16130021573577791454941195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10753347715718527636627463 16130021573577791454941195)
            ·
              refine ⟨24195032360366687182411793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16130021573577791454941195 24195032360366687182411793)
              ·
                refine ⟨18146274270275015386808845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24195032360366687182411793 18146274270275015386808845)
                ·
                  refine ⟨6804852851353130770053317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18146274270275015386808845 6804852851353130770053317)
                  ·
                    refine ⟨1275909909628712019384997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6804852851353130770053317 1275909909628712019384997)
                    ·
                      rfl

theorem cell23_7454477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_7454477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454477 prefixEnd_7454477 := by exact prefixLift 7454477
  have htrace : WordTrace (prefixWord ++ tailWord_7454477) baseStart_7454477 baseEnd_7454477 := by
    simpa [prefixWord, tailWord_7454477, baseEnd_7454477] using wordTrace_append hprefix tailTrace_7454477
  have hstable : (prefixWord ++ tailWord_7454477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454477).length < 2 ^ (prefixWord ++ tailWord_7454477).sum := by decide
  have hdescent : baseEnd_7454477 < baseStart_7454477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454500 : List Nat := [2, 3, 1, 3, 2, 2, 2, 3, 1, 1, 3]
def baseStart_7454500 : Nat := 118140960795 + 7454500 * 2 ^ 59
def prefixEnd_7454500 : Nat := 4983230072969 + 3 ^ 40 * 7454500 * 2
def baseEnd_7454500 : Nat := 3827741538941189468167385

theorem tailTrace_7454500 : CollatzResearch.WordTrace tailWord_7454500 prefixEnd_7454500 3827741538941189468167385 := by
  unfold tailWord_7454500
  simp only [CollatzResearch.WordTrace]
  refine ⟨135943975746813551043136477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181258634329084734724181969 135943975746813551043136477)
  ·
    refine ⟨50978990905055081641176179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135943975746813551043136477 50978990905055081641176179)
    ·
      refine ⟨76468486357582622461764269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50978990905055081641176179 76468486357582622461764269)
      ·
        refine ⟨28675682384093483423161601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76468486357582622461764269 28675682384093483423161601)
        ·
          refine ⟨21506761788070112567371201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28675682384093483423161601 21506761788070112567371201)
          ·
            refine ⟨16130071341052584425528401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21506761788070112567371201 16130071341052584425528401)
            ·
              refine ⟨12097553505789438319146301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16130071341052584425528401 12097553505789438319146301)
              ·
                refine ⟨4536582564671039369679863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12097553505789438319146301 4536582564671039369679863)
                ·
                  refine ⟨6804873847006559054519795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4536582564671039369679863 6804873847006559054519795)
                  ·
                    refine ⟨10207310770509838581779693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6804873847006559054519795 10207310770509838581779693)
                    ·
                      refine ⟨3827741538941189468167385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10207310770509838581779693 3827741538941189468167385)
                      ·
                        rfl

theorem cell23_7454500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_7454500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454500 prefixEnd_7454500 := by exact prefixLift 7454500
  have htrace : WordTrace (prefixWord ++ tailWord_7454500) baseStart_7454500 baseEnd_7454500 := by
    simpa [prefixWord, tailWord_7454500, baseEnd_7454500] using wordTrace_append hprefix tailTrace_7454500
  have hstable : (prefixWord ++ tailWord_7454500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454500).length < 2 ^ (prefixWord ++ tailWord_7454500).sum := by decide
  have hdescent : baseEnd_7454500 < baseStart_7454500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454526 : List Nat := [4, 2, 1, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_7454526 : Nat := 118140960795 + 7454526 * 2 ^ 59
def prefixEnd_7454526 : Nat := 4983230072969 + 3 ^ 40 * 7454526 * 2
def baseEnd_7454526 : Nat := 3827754889438206366442265

theorem tailTrace_7454526 : CollatzResearch.WordTrace tailWord_7454526 prefixEnd_7454526 3827754889438206366442265 := by
  unfold tailWord_7454526
  simp only [CollatzResearch.WordTrace]
  refine ⟨33986112473941613565839929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181259266527688605684479621 33986112473941613565839929)
  ·
    refine ⟨25489584355456210174379947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33986112473941613565839929 25489584355456210174379947)
    ·
      refine ⟨38234376533184315261569921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25489584355456210174379947 38234376533184315261569921)
      ·
        refine ⟨28675782399888236446177441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38234376533184315261569921 28675782399888236446177441)
        ·
          refine ⟨21506836799916177334633081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28675782399888236446177441 21506836799916177334633081)
          ·
            refine ⟨16130127599937133000974811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21506836799916177334633081 16130127599937133000974811)
            ·
              refine ⟨24195191399905699501462217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16130127599937133000974811 24195191399905699501462217)
              ·
                refine ⟨18146393549929274626096663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24195191399905699501462217 18146393549929274626096663)
                ·
                  refine ⟨27219590324893911939144995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18146393549929274626096663 27219590324893911939144995)
                  ·
                    refine ⟨40829385487340867908717493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27219590324893911939144995 40829385487340867908717493)
                    ·
                      refine ⟨3827754889438206366442265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40829385487340867908717493 3827754889438206366442265)
                      ·
                        rfl

theorem cell23_7454526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_7454526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454526 prefixEnd_7454526 := by exact prefixLift 7454526
  have htrace : WordTrace (prefixWord ++ tailWord_7454526) baseStart_7454526 baseEnd_7454526 := by
    simpa [prefixWord, tailWord_7454526, baseEnd_7454526] using wordTrace_append hprefix tailTrace_7454526
  have hstable : (prefixWord ++ tailWord_7454526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454526).length < 2 ^ (prefixWord ++ tailWord_7454526).sum := by decide
  have hdescent : baseEnd_7454526 < baseStart_7454526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454536 : List Nat := [2, 1, 3, 1, 1, 6, 1, 1, 1, 2, 4]
def baseStart_7454536 : Nat := 118140960795 + 7454536 * 2 ^ 59
def prefixEnd_7454536 : Nat := 4983230072969 + 3 ^ 40 * 7454536 * 2
def baseEnd_7454536 : Nat := 3827760024244751327317219

theorem tailTrace_7454536 : CollatzResearch.WordTrace tailWord_7454536 prefixEnd_7454536 3827760024244751327317219 := by
  unfold tailWord_7454536
  simp only [CollatzResearch.WordTrace]
  refine ⟨135944632260748340117291731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181259509680997786823055641 135944632260748340117291731)
  ·
    refine ⟨203916948391122510175937597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135944632260748340117291731 203916948391122510175937597)
    ·
      refine ⟨76468855646670941315976599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203916948391122510175937597 76468855646670941315976599)
      ·
        refine ⟨114703283470006411973964899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76468855646670941315976599 114703283470006411973964899)
        ·
          refine ⟨172054925205009617960947349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114703283470006411973964899 172054925205009617960947349)
          ·
            refine ⟨8065074618984825841919407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 172054925205009617960947349 8065074618984825841919407)
            ·
              refine ⟨12097611928477238762879111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8065074618984825841919407 12097611928477238762879111)
              ·
                refine ⟨18146417892715858144318667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12097611928477238762879111 18146417892715858144318667)
                ·
                  refine ⟨27219626839073787216478001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18146417892715858144318667 27219626839073787216478001)
                  ·
                    refine ⟨20414720129305340412358501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27219626839073787216478001 20414720129305340412358501)
                    ·
                      refine ⟨3827760024244751327317219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20414720129305340412358501 3827760024244751327317219)
                      ·
                        rfl

theorem cell23_7454536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_7454536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454536 prefixEnd_7454536 := by exact prefixLift 7454536
  have htrace : WordTrace (prefixWord ++ tailWord_7454536) baseStart_7454536 baseEnd_7454536 := by
    simpa [prefixWord, tailWord_7454536, baseEnd_7454536] using wordTrace_append hprefix tailTrace_7454536
  have hstable : (prefixWord ++ tailWord_7454536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454536).length < 2 ^ (prefixWord ++ tailWord_7454536).sum := by decide
  have hdescent : baseEnd_7454536 < baseStart_7454536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454546 : List Nat := [3, 2, 2, 1, 1, 5, 2, 7]
def baseStart_7454546 : Nat := 118140960795 + 7454546 * 2 ^ 59
def prefixEnd_7454546 : Nat := 4983230072969 + 3 ^ 40 * 7454546 * 2
def baseEnd_7454546 : Nat := 141769079964862825488599

theorem tailTrace_7454546 : CollatzResearch.WordTrace tailWord_7454546 prefixEnd_7454546 141769079964862825488599 := by
  unfold tailWord_7454546
  simp only [CollatzResearch.WordTrace]
  refine ⟨67972407312865112985611873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181259752834306967961631661 67972407312865112985611873)
  ·
    refine ⟨50979305484648834739208905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67972407312865112985611873 50979305484648834739208905)
    ·
      refine ⟨38234479113486626054406679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50979305484648834739208905 38234479113486626054406679)
      ·
        refine ⟨57351718670229939081610019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38234479113486626054406679 57351718670229939081610019)
        ·
          refine ⟨86027578005344908622415029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57351718670229939081610019 86027578005344908622415029)
          ·
            refine ⟨8065085438001085183351409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86027578005344908622415029 8065085438001085183351409)
            ·
              refine ⟨6048814078500813887513557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8065085438001085183351409 6048814078500813887513557)
              ·
                refine ⟨141769079964862825488599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6048814078500813887513557 141769079964862825488599)
                ·
                  rfl

theorem cell23_7454546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 7].length) (baseStart_7454546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454546 prefixEnd_7454546 := by exact prefixLift 7454546
  have htrace : WordTrace (prefixWord ++ tailWord_7454546) baseStart_7454546 baseEnd_7454546 := by
    simpa [prefixWord, tailWord_7454546, baseEnd_7454546] using wordTrace_append hprefix tailTrace_7454546
  have hstable : (prefixWord ++ tailWord_7454546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454546).length < 2 ^ (prefixWord ++ tailWord_7454546).sum := by decide
  have hdescent : baseEnd_7454546 < baseStart_7454546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454574 : List Nat := [4, 1, 2, 3, 1, 2, 3, 2, 1, 2, 2]
def baseStart_7454574 : Nat := 118140960795 + 7454574 * 2 ^ 59
def prefixEnd_7454574 : Nat := 4983230072969 + 3 ^ 40 * 7454574 * 2
def baseEnd_7454574 : Nat := 3827779536509622178642045

theorem tailTrace_7454574 : CollatzResearch.WordTrace tailWord_7454574 prefixEnd_7454574 3827779536509622178642045 := by
  unfold tailWord_7454574
  simp only [CollatzResearch.WordTrace]
  refine ⟨33986331311919876590558347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181260433663572675149644517 33986331311919876590558347)
  ·
    refine ⟨50979496967879814885837521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33986331311919876590558347 50979496967879814885837521)
    ·
      refine ⟨38234622725909861164378141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50979496967879814885837521 38234622725909861164378141)
      ·
        refine ⟨14337983522216197936641803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38234622725909861164378141 14337983522216197936641803)
        ·
          refine ⟨21506975283324296904962705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14337983522216197936641803 21506975283324296904962705)
          ·
            refine ⟨16130231462493222678722029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21506975283324296904962705 16130231462493222678722029)
            ·
              refine ⟨6048836798434958504520761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16130231462493222678722029 6048836798434958504520761)
              ·
                refine ⟨4536627598826218878390571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6048836798434958504520761 4536627598826218878390571)
                ·
                  refine ⟨6804941398239328317585857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4536627598826218878390571 6804941398239328317585857)
                  ·
                    refine ⟨5103706048679496238189393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6804941398239328317585857 5103706048679496238189393)
                    ·
                      refine ⟨3827779536509622178642045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5103706048679496238189393 3827779536509622178642045)
                      ·
                        rfl

theorem cell23_7454574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_7454574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454574 prefixEnd_7454574 := by exact prefixLift 7454574
  have htrace : WordTrace (prefixWord ++ tailWord_7454574) baseStart_7454574 baseEnd_7454574 := by
    simpa [prefixWord, tailWord_7454574, baseEnd_7454574] using wordTrace_append hprefix tailTrace_7454574
  have hstable : (prefixWord ++ tailWord_7454574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454574).length < 2 ^ (prefixWord ++ tailWord_7454574).sum := by decide
  have hdescent : baseEnd_7454574 < baseStart_7454574 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454629 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 3, 5, 3]
def baseStart_7454629 : Nat := 118140960795 + 7454629 * 2 ^ 59
def prefixEnd_7454629 : Nat := 4983230072969 + 3 ^ 40 * 7454629 * 2
def baseEnd_7454629 : Nat := 3827807777945619463454291

theorem tailTrace_7454629 : CollatzResearch.WordTrace tailWord_7454629 prefixEnd_7454629 3827807777945619463454291 := by
  unfold tailWord_7454629
  simp only [CollatzResearch.WordTrace]
  refine ⟨271892656510159757117718941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181261771006773171411812627 271892656510159757117718941)
  ·
    refine ⟨101959746191309908919144603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271892656510159757117718941 101959746191309908919144603)
    ·
      refine ⟨152939619286964863378716905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101959746191309908919144603 152939619286964863378716905)
      ·
        refine ⟨114704714465223647534037679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152939619286964863378716905 114704714465223647534037679)
        ·
          refine ⟨172057071697835471301056519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114704714465223647534037679 172057071697835471301056519)
          ·
            refine ⟨258085607546753206951584779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172057071697835471301056519 258085607546753206951584779)
            ·
              refine ⟨387128411320129810427377169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258085607546753206951584779 387128411320129810427377169)
              ·
                refine ⟨290346308490097357820532877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387128411320129810427377169 290346308490097357820532877)
                ·
                  refine ⟨108879865683786509182699829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 290346308490097357820532877 108879865683786509182699829)
                  ·
                    refine ⟨10207487407854985235878109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108879865683786509182699829 10207487407854985235878109)
                    ·
                      refine ⟨3827807777945619463454291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10207487407854985235878109 3827807777945619463454291)
                      ·
                        rfl

theorem cell23_7454629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_7454629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454629 prefixEnd_7454629 := by exact prefixLift 7454629
  have htrace : WordTrace (prefixWord ++ tailWord_7454629) baseStart_7454629 baseEnd_7454629 := by
    simpa [prefixWord, tailWord_7454629, baseEnd_7454629] using wordTrace_append hprefix tailTrace_7454629
  have hstable : (prefixWord ++ tailWord_7454629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454629).length < 2 ^ (prefixWord ++ tailWord_7454629).sum := by decide
  have hdescent : baseEnd_7454629 < baseStart_7454629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454649 : List Nat := [1, 2, 1, 4, 2, 1, 2, 2, 1, 7]
def baseStart_7454649 : Nat := 118140960795 + 7454649 * 2 ^ 59
def prefixEnd_7454649 : Nat := 4983230072969 + 3 ^ 40 * 7454649 * 2
def baseEnd_7454649 : Nat := 1275939349186236461734733

theorem tailTrace_7454649 : CollatzResearch.WordTrace tailWord_7454649 prefixEnd_7454649 1275939349186236461734733 := by
  unfold tailWord_7454649
  simp only [CollatzResearch.WordTrace]
  refine ⟨271893385970087300533447001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181262257313391533688964667 271893385970087300533447001)
  ·
    refine ⟨203920039477565475400085251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271893385970087300533447001 203920039477565475400085251)
    ·
      refine ⟨305880059216348213100127877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203920039477565475400085251 305880059216348213100127877)
      ·
        refine ⟨57352511103065289956273977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305880059216348213100127877 57352511103065289956273977)
        ·
          refine ⟨43014383327298967467205483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57352511103065289956273977 43014383327298967467205483)
          ·
            refine ⟨64521574990948451200808225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43014383327298967467205483 64521574990948451200808225)
            ·
              refine ⟨48391181243211338400606169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64521574990948451200808225 48391181243211338400606169)
              ·
                refine ⟨36293385932408503800454627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48391181243211338400606169 36293385932408503800454627)
                ·
                  refine ⟨54440078898612755700681941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36293385932408503800454627 54440078898612755700681941)
                  ·
                    refine ⟨1275939349186236461734733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54440078898612755700681941 1275939349186236461734733)
                    ·
                      rfl

theorem cell23_7454649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 7].length) (baseStart_7454649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454649 prefixEnd_7454649 := by exact prefixLift 7454649
  have htrace : WordTrace (prefixWord ++ tailWord_7454649) baseStart_7454649 baseEnd_7454649 := by
    simpa [prefixWord, tailWord_7454649, baseEnd_7454649] using wordTrace_append hprefix tailTrace_7454649
  have hstable : (prefixWord ++ tailWord_7454649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454649).length < 2 ^ (prefixWord ++ tailWord_7454649).sum := by decide
  have hdescent : baseEnd_7454649 < baseStart_7454649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454656 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 2, 5, 2]
def baseStart_7454656 : Nat := 118140960795 + 7454656 * 2 ^ 59
def prefixEnd_7454656 : Nat := 4983230072969 + 3 ^ 40 * 7454656 * 2
def baseEnd_7454656 : Nat := 3827821641923290857816667

theorem tailTrace_7454656 : CollatzResearch.WordTrace tailWord_7454656 prefixEnd_7454656 3827821641923290857816667 := by
  unfold tailWord_7454656
  simp only [CollatzResearch.WordTrace]
  refine ⟨135946820640530970364475911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181262427520707960485967881 135946820640530970364475911)
  ·
    refine ⟨203920230960796455546713867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135946820640530970364475911 203920230960796455546713867)
    ·
      refine ⟨305880346441194683320070801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203920230960796455546713867 305880346441194683320070801)
      ·
        refine ⟨229410259830896012490053101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305880346441194683320070801 229410259830896012490053101)
        ·
          refine ⟨86028847436586004683769913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229410259830896012490053101 86028847436586004683769913)
          ·
            refine ⟨64521635577439503512827435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86028847436586004683769913 64521635577439503512827435)
            ·
              refine ⟨96782453366159255269241153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64521635577439503512827435 96782453366159255269241153)
              ·
                refine ⟨72586840024619441451930865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96782453366159255269241153 72586840024619441451930865)
                ·
                  refine ⟨54440130018464581088948149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72586840024619441451930865 54440130018464581088948149)
                  ·
                    refine ⟨5103762189231054477088889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54440130018464581088948149 5103762189231054477088889)
                    ·
                      refine ⟨3827821641923290857816667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5103762189231054477088889 3827821641923290857816667)
                      ·
                        rfl

theorem cell23_7454656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 2, 5, 2].length) (baseStart_7454656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454656 prefixEnd_7454656 := by exact prefixLift 7454656
  have htrace : WordTrace (prefixWord ++ tailWord_7454656) baseStart_7454656 baseEnd_7454656 := by
    simpa [prefixWord, tailWord_7454656, baseEnd_7454656] using wordTrace_append hprefix tailTrace_7454656
  have hstable : (prefixWord ++ tailWord_7454656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454656).length < 2 ^ (prefixWord ++ tailWord_7454656).sum := by decide
  have hdescent : baseEnd_7454656 < baseStart_7454656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454666 : List Nat := [3, 1, 2, 1, 2, 1, 5, 1, 2, 5]
def baseStart_7454666 : Nat := 118140960795 + 7454666 * 2 ^ 59
def prefixEnd_7454666 : Nat := 4983230072969 + 3 ^ 40 * 7454666 * 2
def baseEnd_7454666 : Nat := 1275942258909945272897207

theorem tailTrace_7454666 : CollatzResearch.WordTrace tailWord_7454666 prefixEnd_7454666 1275942258909945272897207 := by
  unfold tailWord_7454666
  simp only [CollatzResearch.WordTrace]
  refine ⟨67973501502756428109203963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181262670674017141624543901 67973501502756428109203963)
  ·
    refine ⟨101960252254134642163805945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67973501502756428109203963 101960252254134642163805945)
    ·
      refine ⟨76470189190600981622854459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101960252254134642163805945 76470189190600981622854459)
      ·
        refine ⟨114705283785901472434281689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76470189190600981622854459 114705283785901472434281689)
        ·
          refine ⟨86028962839426104325711267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114705283785901472434281689 86028962839426104325711267)
          ·
            refine ⟨129043444259139156488566901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86028962839426104325711267 129043444259139156488566901)
            ·
              refine ⟨12097822899294295920803147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129043444259139156488566901 12097822899294295920803147)
              ·
                refine ⟨18146734348941443881204721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12097822899294295920803147 18146734348941443881204721)
                ·
                  refine ⟨13610050761706082910903541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18146734348941443881204721 13610050761706082910903541)
                  ·
                    refine ⟨1275942258909945272897207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13610050761706082910903541 1275942258909945272897207)
                    ·
                      rfl

theorem cell23_7454666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_7454666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454666 prefixEnd_7454666 := by exact prefixLift 7454666
  have htrace : WordTrace (prefixWord ++ tailWord_7454666) baseStart_7454666 baseEnd_7454666 := by
    simpa [prefixWord, tailWord_7454666, baseEnd_7454666] using wordTrace_append hprefix tailTrace_7454666
  have hstable : (prefixWord ++ tailWord_7454666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454666).length < 2 ^ (prefixWord ++ tailWord_7454666).sum := by decide
  have hdescent : baseEnd_7454666 < baseStart_7454666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454689 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 2, 3, 5]
def baseStart_7454689 : Nat := 118140960795 + 7454689 * 2 ^ 59
def prefixEnd_7454689 : Nat := 4983230072969 + 3 ^ 40 * 7454689 * 2
def baseEnd_7454689 : Nat := 3827838586784889228704015

theorem tailTrace_7454689 : CollatzResearch.WordTrace tailWord_7454689 prefixEnd_7454689 3827838586784889228704015 := by
  unfold tailWord_7454689
  simp only [CollatzResearch.WordTrace]
  refine ⟨271894844889942387364903121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181263229926628258243268747 271894844889942387364903121)
  ·
    refine ⟨203921133667456790523677341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271894844889942387364903121 203921133667456790523677341)
    ·
      refine ⟨76470425125296296446379003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203921133667456790523677341 76470425125296296446379003)
      ·
        refine ⟨114705637687944444669568505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76470425125296296446379003 114705637687944444669568505)
        ·
          refine ⟨86029228265958333502176379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114705637687944444669568505 86029228265958333502176379)
          ·
            refine ⟨129043842398937500253264569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86029228265958333502176379 129043842398937500253264569)
            ·
              refine ⟨96782881799203125189948427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129043842398937500253264569 96782881799203125189948427)
              ·
                refine ⟨145174322698804687784922641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96782881799203125189948427 145174322698804687784922641)
                ·
                  refine ⟨108880742024103515838691981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145174322698804687784922641 108880742024103515838691981)
                  ·
                    refine ⟨40830278259038818439509493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108880742024103515838691981 40830278259038818439509493)
                    ·
                      refine ⟨3827838586784889228704015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40830278259038818439509493 3827838586784889228704015)
                      ·
                        rfl

theorem cell23_7454689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_7454689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454689 prefixEnd_7454689 := by exact prefixLift 7454689
  have htrace : WordTrace (prefixWord ++ tailWord_7454689) baseStart_7454689 baseEnd_7454689 := by
    simpa [prefixWord, tailWord_7454689, baseEnd_7454689] using wordTrace_append hprefix tailTrace_7454689
  have hstable : (prefixWord ++ tailWord_7454689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454689).length < 2 ^ (prefixWord ++ tailWord_7454689).sum := by decide
  have hdescent : baseEnd_7454689 < baseStart_7454689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454760 : List Nat := [2, 1, 5, 3, 1, 1, 1, 3, 6]
def baseStart_7454760 : Nat := 118140960795 + 7454760 * 2 ^ 59
def prefixEnd_7454760 : Nat := 4983230072969 + 3 ^ 40 * 7454760 * 2
def baseEnd_7454760 : Nat := 425319449323484272324021

theorem tailTrace_7454760 : CollatzResearch.WordTrace tailWord_7454760 prefixEnd_7454760 425319449323484272324021 := by
  unfold tailWord_7454760
  simp only [CollatzResearch.WordTrace]
  refine ⟨135948717236342583245368867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181264956315123444327158489 135948717236342583245368867)
  ·
    refine ⟨203923075854513874868053301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135948717236342583245368867 203923075854513874868053301)
    ·
      refine ⟨19117788361360675768879997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 203923075854513874868053301 19117788361360675768879997)
      ·
        refine ⟨7169170635510253413329999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19117788361360675768879997 7169170635510253413329999)
        ·
          refine ⟨10753755953265380119994999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7169170635510253413329999 10753755953265380119994999)
          ·
            refine ⟨16130633929898070179992499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10753755953265380119994999 16130633929898070179992499)
            ·
              refine ⟨24195950894847105269988749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16130633929898070179992499 24195950894847105269988749)
              ·
                refine ⟨9073481585567664476245781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24195950894847105269988749 9073481585567664476245781)
                ·
                  refine ⟨425319449323484272324021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9073481585567664476245781 425319449323484272324021)
                  ·
                    rfl

theorem cell23_7454760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 6].length) (baseStart_7454760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454760 prefixEnd_7454760 := by exact prefixLift 7454760
  have htrace : WordTrace (prefixWord ++ tailWord_7454760) baseStart_7454760 baseEnd_7454760 := by
    simpa [prefixWord, tailWord_7454760, baseEnd_7454760] using wordTrace_append hprefix tailTrace_7454760
  have hstable : (prefixWord ++ tailWord_7454760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454760).length < 2 ^ (prefixWord ++ tailWord_7454760).sum := by decide
  have hdescent : baseEnd_7454760 < baseStart_7454760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454773 : List Nat := [1, 3, 3, 1, 1, 1, 5, 2, 1, 5]
def baseStart_7454773 : Nat := 118140960795 + 7454773 * 2 ^ 59
def prefixEnd_7454773 : Nat := 4983230072969 + 3 ^ 40 * 7454773 * 2
def baseEnd_7454773 : Nat := 1275960573053288966684543

theorem tailTrace_7454773 : CollatzResearch.WordTrace tailWord_7454773 prefixEnd_7454773 1275960573053288966684543 := by
  unfold tailWord_7454773
  simp only [CollatzResearch.WordTrace]
  refine ⟨271897908621638069710960973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181265272414425379807307315 271897908621638069710960973)
  ·
    refine ⟨101961715733114276141610365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271897908621638069710960973 101961715733114276141610365)
    ·
      refine ⟨38235643399917853553103887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101961715733114276141610365 38235643399917853553103887)
      ·
        refine ⟨57353465099876780329655831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38235643399917853553103887 57353465099876780329655831)
        ·
          refine ⟨86030197649815170494483747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57353465099876780329655831 86030197649815170494483747)
          ·
            refine ⟨129045296474722755741725621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86030197649815170494483747 129045296474722755741725621)
            ·
              refine ⟨12097996544505258350786777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129045296474722755741725621 12097996544505258350786777)
              ·
                refine ⟨9073497408378943763090083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12097996544505258350786777 9073497408378943763090083)
                ·
                  refine ⟨13610246112568415644635125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9073497408378943763090083 13610246112568415644635125)
                  ·
                    refine ⟨1275960573053288966684543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13610246112568415644635125 1275960573053288966684543)
                    ·
                      rfl

theorem cell23_7454773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_7454773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454773 prefixEnd_7454773 := by exact prefixLift 7454773
  have htrace : WordTrace (prefixWord ++ tailWord_7454773) baseStart_7454773 baseEnd_7454773 := by
    simpa [prefixWord, tailWord_7454773, baseEnd_7454773] using wordTrace_append hprefix tailTrace_7454773
  have hstable : (prefixWord ++ tailWord_7454773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454773).length < 2 ^ (prefixWord ++ tailWord_7454773).sum := by decide
  have hdescent : baseEnd_7454773 < baseStart_7454773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454780 : List Nat := [2, 2, 2, 2, 2, 1, 4, 1, 2, 3, 2]
def baseStart_7454780 : Nat := 118140960795 + 7454780 * 2 ^ 59
def prefixEnd_7454780 : Nat := 4983230072969 + 3 ^ 40 * 7454780 * 2
def baseEnd_7454780 : Nat := 3827885313524448372666097

theorem tailTrace_7454780 : CollatzResearch.WordTrace tailWord_7454780 prefixEnd_7454780 3827885313524448372666097 := by
  unfold tailWord_7454780
  simp only [CollatzResearch.WordTrace]
  refine ⟨135949081966306354953232897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181265442621741806604310529 135949081966306354953232897)
  ·
    refine ⟨101961811474729766214924673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135949081966306354953232897 101961811474729766214924673)
    ·
      refine ⟨76471358606047324661193505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101961811474729766214924673 76471358606047324661193505)
      ·
        refine ⟨57353518954535493495895129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76471358606047324661193505 57353518954535493495895129)
        ·
          refine ⟨43015139215901620121921347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57353518954535493495895129 43015139215901620121921347)
          ·
            refine ⟨64522708823852430182882021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43015139215901620121921347 64522708823852430182882021)
            ·
              refine ⟨12098007904472330659290379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64522708823852430182882021 12098007904472330659290379)
              ·
                refine ⟨18147011856708495988935569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12098007904472330659290379 18147011856708495988935569)
                ·
                  refine ⟨13610258892531371991701677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18147011856708495988935569 13610258892531371991701677)
                  ·
                    refine ⟨5103847084699264496888129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13610258892531371991701677 5103847084699264496888129)
                    ·
                      refine ⟨3827885313524448372666097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5103847084699264496888129 3827885313524448372666097)
                      ·
                        rfl

theorem cell23_7454780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_7454780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454780 prefixEnd_7454780 := by exact prefixLift 7454780
  have htrace : WordTrace (prefixWord ++ tailWord_7454780) baseStart_7454780 baseEnd_7454780 := by
    simpa [prefixWord, tailWord_7454780, baseEnd_7454780] using wordTrace_append hprefix tailTrace_7454780
  have hstable : (prefixWord ++ tailWord_7454780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454780).length < 2 ^ (prefixWord ++ tailWord_7454780).sum := by decide
  have hdescent : baseEnd_7454780 < baseStart_7454780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454810 : List Nat := [3, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2]
def baseStart_7454810 : Nat := 118140960795 + 7454810 * 2 ^ 59
def prefixEnd_7454810 : Nat := 4983230072969 + 3 ^ 40 * 7454810 * 2
def baseEnd_7454810 : Nat := 3827900717944083255290959

theorem tailTrace_7454810 : CollatzResearch.WordTrace tailWord_7454810 prefixEnd_7454810 3827900717944083255290959 := by
  unfold tailWord_7454810
  simp only [CollatzResearch.WordTrace]
  refine ⟨67974814530626006257514471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181266172081669350020038589 67974814530626006257514471)
  ·
    refine ⟨101962221795939009386271707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67974814530626006257514471 101962221795939009386271707)
    ·
      refine ⟨152943332693908514079407561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101962221795939009386271707 152943332693908514079407561)
      ·
        refine ⟨114707499520431385559555671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152943332693908514079407561 114707499520431385559555671)
        ·
          refine ⟨172061249280647078339333507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114707499520431385559555671 172061249280647078339333507)
          ·
            refine ⟨258091873920970617509000261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172061249280647078339333507 258091873920970617509000261)
            ·
              refine ⟨48392226360181990782937549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 258091873920970617509000261 48392226360181990782937549)
              ·
                refine ⟨18147084885068246543601581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48392226360181990782937549 18147084885068246543601581)
                ·
                  refine ⟨6805156831900592453850593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18147084885068246543601581 6805156831900592453850593)
                  ·
                    refine ⟨5103867623925444340387945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6805156831900592453850593 5103867623925444340387945)
                    ·
                      refine ⟨3827900717944083255290959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5103867623925444340387945 3827900717944083255290959)
                      ·
                        rfl

theorem cell23_7454810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2].length) (baseStart_7454810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454810 prefixEnd_7454810 := by exact prefixLift 7454810
  have htrace : WordTrace (prefixWord ++ tailWord_7454810) baseStart_7454810 baseEnd_7454810 := by
    simpa [prefixWord, tailWord_7454810, baseEnd_7454810] using wordTrace_append hprefix tailTrace_7454810
  have hstable : (prefixWord ++ tailWord_7454810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454810).length < 2 ^ (prefixWord ++ tailWord_7454810).sum := by decide
  have hdescent : baseEnd_7454810 < baseStart_7454810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454816 : List Nat := [2, 1, 1, 3, 2, 3, 3, 8]
def baseStart_7454816 : Nat := 118140960795 + 7454816 * 2 ^ 59
def prefixEnd_7454816 : Nat := 4983230072969 + 3 ^ 40 * 7454816 * 2
def baseEnd_7454816 : Nat := 141774214771407786363553

theorem tailTrace_7454816 : CollatzResearch.WordTrace tailWord_7454816 prefixEnd_7454816 141774214771407786363553 := by
  unfold tailWord_7454816
  simp only [CollatzResearch.WordTrace]
  refine ⟨135949738480241144027388151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181266317973654858703184201 135949738480241144027388151)
  ·
    refine ⟨203924607720361716041082227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135949738480241144027388151 203924607720361716041082227)
    ·
      refine ⟨305886911580542574061623341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203924607720361716041082227 305886911580542574061623341)
      ·
        refine ⟨114707591842703465273108753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305886911580542574061623341 114707591842703465273108753)
        ·
          refine ⟨86030693882027598954831565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114707591842703465273108753 86030693882027598954831565)
          ·
            refine ⟨32261510205760349608061837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86030693882027598954831565 32261510205760349608061837)
            ·
              refine ⟨12098066327160131103023189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32261510205760349608061837 12098066327160131103023189)
              ·
                refine ⟨141774214771407786363553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12098066327160131103023189 141774214771407786363553)
                ·
                  rfl

theorem cell23_7454816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 8].length) (baseStart_7454816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454816 prefixEnd_7454816 := by exact prefixLift 7454816
  have htrace : WordTrace (prefixWord ++ tailWord_7454816) baseStart_7454816 baseEnd_7454816 := by
    simpa [prefixWord, tailWord_7454816, baseEnd_7454816] using wordTrace_append hprefix tailTrace_7454816
  have hstable : (prefixWord ++ tailWord_7454816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454816).length < 2 ^ (prefixWord ++ tailWord_7454816).sum := by decide
  have hdescent : baseEnd_7454816 < baseStart_7454816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454823 : List Nat := [1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 4]
def baseStart_7454823 : Nat := 118140960795 + 7454823 * 2 ^ 59
def prefixEnd_7454823 : Nat := 4983230072969 + 3 ^ 40 * 7454823 * 2
def baseEnd_7454823 : Nat := 3827907393192591704428399

theorem tailTrace_7454823 : CollatzResearch.WordTrace tailWord_7454823 prefixEnd_7454823 3827907393192591704428399 := by
  unfold tailWord_7454823
  simp only [CollatzResearch.WordTrace]
  refine ⟨271899732271456928250281123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181266488180971285500187415 271899732271456928250281123)
  ·
    refine ⟨407849598407185392375421685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271899732271456928250281123 407849598407185392375421685)
    ·
      refine ⟨38235899850673630535195783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 407849598407185392375421685 38235899850673630535195783)
      ·
        refine ⟨57353849776010445802793675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38235899850673630535195783 57353849776010445802793675)
        ·
          refine ⟨86030774664015668704190513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57353849776010445802793675 86030774664015668704190513)
          ·
            refine ⟨64523080998011751528142885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86030774664015668704190513 64523080998011751528142885)
            ·
              refine ⟨12098077687127203411526791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64523080998011751528142885 12098077687127203411526791)
              ·
                refine ⟨18147116530690805117290187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12098077687127203411526791 18147116530690805117290187)
                ·
                  refine ⟨27220674796036207675935281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18147116530690805117290187 27220674796036207675935281)
                  ·
                    refine ⟨20415506097027155756951461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27220674796036207675935281 20415506097027155756951461)
                    ·
                      refine ⟨3827907393192591704428399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20415506097027155756951461 3827907393192591704428399)
                      ·
                        rfl

theorem cell23_7454823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_7454823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454823 prefixEnd_7454823 := by exact prefixLift 7454823
  have htrace : WordTrace (prefixWord ++ tailWord_7454823) baseStart_7454823 baseEnd_7454823 := by
    simpa [prefixWord, tailWord_7454823, baseEnd_7454823] using wordTrace_append hprefix tailTrace_7454823
  have hstable : (prefixWord ++ tailWord_7454823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454823).length < 2 ^ (prefixWord ++ tailWord_7454823).sum := by decide
  have hdescent : baseEnd_7454823 < baseStart_7454823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454830 : List Nat := [4, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3]
def baseStart_7454830 : Nat := 118140960795 + 7454830 * 2 ^ 59
def prefixEnd_7454830 : Nat := 4983230072969 + 3 ^ 40 * 7454830 * 2
def baseEnd_7454830 : Nat := 3827910987557173177040867

theorem tailTrace_7454830 : CollatzResearch.WordTrace tailWord_7454830 prefixEnd_7454830 3827910987557173177040867 := by
  unfold tailWord_7454830
  simp only [CollatzResearch.WordTrace]
  refine ⟨33987498447803946055723243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181266658388287712297190629 33987498447803946055723243)
  ·
    refine ⟨50981247671705919083584865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33987498447803946055723243 50981247671705919083584865)
    ·
      refine ⟨38235935753779439312688649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50981247671705919083584865 38235935753779439312688649)
      ·
        refine ⟨28676951815334579484516487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38235935753779439312688649 28676951815334579484516487)
        ·
          refine ⟨43015427723001869226774731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28676951815334579484516487 43015427723001869226774731)
          ·
            refine ⟨64523141584502803840162097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43015427723001869226774731 64523141584502803840162097)
            ·
              refine ⟨48392356188377102880121573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64523141584502803840162097 48392356188377102880121573)
              ·
                refine ⟨9073566785320706790022795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48392356188377102880121573 9073566785320706790022795)
                ·
                  refine ⟨13610350177981060185034193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9073566785320706790022795 13610350177981060185034193)
                  ·
                    refine ⟨10207762633485795138775645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13610350177981060185034193 10207762633485795138775645)
                    ·
                      refine ⟨3827910987557173177040867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10207762633485795138775645 3827910987557173177040867)
                      ·
                        rfl

theorem cell23_7454830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_7454830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454830 prefixEnd_7454830 := by exact prefixLift 7454830
  have htrace : WordTrace (prefixWord ++ tailWord_7454830) baseStart_7454830 baseEnd_7454830 := by
    simpa [prefixWord, tailWord_7454830, baseEnd_7454830] using wordTrace_append hprefix tailTrace_7454830
  have hstable : (prefixWord ++ tailWord_7454830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454830).length < 2 ^ (prefixWord ++ tailWord_7454830).sum := by decide
  have hdescent : baseEnd_7454830 < baseStart_7454830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454844 : List Nat := [2, 2, 2, 1, 1, 5, 2, 3, 1, 2, 2]
def baseStart_7454844 : Nat := 118140960795 + 7454844 * 2 ^ 59
def prefixEnd_7454844 : Nat := 4983230072969 + 3 ^ 40 * 7454844 * 2
def baseEnd_7454844 : Nat := 3827918176286336122265803

theorem tailTrace_7454844 : CollatzResearch.WordTrace tailWord_7454844 prefixEnd_7454844 3827918176286336122265803 := by
  unfold tailWord_7454844
  simp only [CollatzResearch.WordTrace]
  refine ⟨135950249102190424418397793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181266998802920565891197057 135950249102190424418397793)
  ·
    refine ⟨101962686826642818313798345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135950249102190424418397793 101962686826642818313798345)
    ·
      refine ⟨76472015119982113735348759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101962686826642818313798345 76472015119982113735348759)
      ·
        refine ⟨114708022679973170603023139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76472015119982113735348759 114708022679973170603023139)
        ·
          refine ⟨172062034019959755904534709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114708022679973170603023139 172062034019959755904534709)
          ·
            refine ⟨16130815689371227116050129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 172062034019959755904534709 16130815689371227116050129)
            ·
              refine ⟨12098111767028420337037597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16130815689371227116050129 12098111767028420337037597)
              ·
                refine ⟨4536791912635657626389099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12098111767028420337037597 4536791912635657626389099)
                ·
                  refine ⟨6805187868953486439583649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4536791912635657626389099 6805187868953486439583649)
                  ·
                    refine ⟨5103890901715114829687737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6805187868953486439583649 5103890901715114829687737)
                    ·
                      refine ⟨3827918176286336122265803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5103890901715114829687737 3827918176286336122265803)
                      ·
                        rfl

theorem cell23_7454844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3, 1, 2, 2].length) (baseStart_7454844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454844 prefixEnd_7454844 := by exact prefixLift 7454844
  have htrace : WordTrace (prefixWord ++ tailWord_7454844) baseStart_7454844 baseEnd_7454844 := by
    simpa [prefixWord, tailWord_7454844, baseEnd_7454844] using wordTrace_append hprefix tailTrace_7454844
  have hstable : (prefixWord ++ tailWord_7454844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454844).length < 2 ^ (prefixWord ++ tailWord_7454844).sum := by decide
  have hdescent : baseEnd_7454844 < baseStart_7454844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454903 : List Nat := [1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 5]
def baseStart_7454903 : Nat := 118140960795 + 7454903 * 2 ^ 59
def prefixEnd_7454903 : Nat := 4983230072969 + 3 ^ 40 * 7454903 * 2
def baseEnd_7454903 : Nat := 3827948471644951391428031

theorem tailTrace_7454903 : CollatzResearch.WordTrace tailWord_7454903 prefixEnd_7454903 3827948471644951391428031 := by
  unfold tailWord_7454903
  simp only [CollatzResearch.WordTrace]
  refine ⟨271902650111167101913193363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181268433407444734608795575 271902650111167101913193363)
  ·
    refine ⟨407853975166750652869790045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271902650111167101913193363 407853975166750652869790045)
    ·
      refine ⟨152945240687531494826171267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407853975166750652869790045 152945240687531494826171267)
      ·
        refine ⟨229417861031297242239256901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152945240687531494826171267 229417861031297242239256901)
        ·
          refine ⟨43015848943368232919860669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229417861031297242239256901 43015848943368232919860669)
          ·
            refine ⟨16130943353763087344947751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43015848943368232919860669 16130943353763087344947751)
            ·
              refine ⟨24196415030644631017421627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16130943353763087344947751 24196415030644631017421627)
              ·
                refine ⟨36294622545966946526132441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24196415030644631017421627 36294622545966946526132441)
                ·
                  refine ⟨27220966909475209894599331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36294622545966946526132441 27220966909475209894599331)
                  ·
                    refine ⟨40831450364212814841898997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27220966909475209894599331 40831450364212814841898997)
                    ·
                      refine ⟨3827948471644951391428031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40831450364212814841898997 3827948471644951391428031)
                      ·
                        rfl

theorem cell23_7454903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_7454903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454903 prefixEnd_7454903 := by exact prefixLift 7454903
  have htrace : WordTrace (prefixWord ++ tailWord_7454903) baseStart_7454903 baseEnd_7454903 := by
    simpa [prefixWord, tailWord_7454903, baseEnd_7454903] using wordTrace_append hprefix tailTrace_7454903
  have hstable : (prefixWord ++ tailWord_7454903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454903).length < 2 ^ (prefixWord ++ tailWord_7454903).sum := by decide
  have hdescent : baseEnd_7454903 < baseStart_7454903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7454906 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 9]
def baseStart_7454906 : Nat := 118140960795 + 7454906 * 2 ^ 59
def prefixEnd_7454906 : Nat := 4983230072969 + 3 ^ 40 * 7454906 * 2
def baseEnd_7454906 : Nat := 425327779120768319965613

theorem tailTrace_7454906 : CollatzResearch.WordTrace tailWord_7454906 prefixEnd_7454906 425327779120768319965613 := by
  unfold tailWord_7454906
  simp only [CollatzResearch.WordTrace]
  refine ⟨67975689882539058356388143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181268506353437488950368381 67975689882539058356388143)
  ·
    refine ⟨101963534823808587534582215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67975689882539058356388143 101963534823808587534582215)
    ·
      refine ⟨152945302235712881301873323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101963534823808587534582215 152945302235712881301873323)
      ·
        refine ⟨229417953353569321952809985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152945302235712881301873323 229417953353569321952809985)
        ·
          refine ⟨172063465015176991464607489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229417953353569321952809985 172063465015176991464607489)
          ·
            refine ⟨129047598761382743598455617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172063465015176991464607489 129047598761382743598455617)
            ·
              refine ⟨96785699071037057698841713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129047598761382743598455617 96785699071037057698841713)
              ·
                refine ⟨72589274303277793274131285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96785699071037057698841713 72589274303277793274131285)
                ·
                  refine ⟨425327779120768319965613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72589274303277793274131285 425327779120768319965613)
                  ·
                    rfl

theorem cell23_7454906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 9].length) (baseStart_7454906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7454906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7454906 prefixEnd_7454906 := by exact prefixLift 7454906
  have htrace : WordTrace (prefixWord ++ tailWord_7454906) baseStart_7454906 baseEnd_7454906 := by
    simpa [prefixWord, tailWord_7454906, baseEnd_7454906] using wordTrace_append hprefix tailTrace_7454906
  have hstable : (prefixWord ++ tailWord_7454906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7454906).length < 2 ^ (prefixWord ++ tailWord_7454906).sum := by decide
  have hdescent : baseEnd_7454906 < baseStart_7454906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7454906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455000 : List Nat := [2, 1, 2, 3, 1, 2, 3, 2, 3, 4]
def baseStart_7455000 : Nat := 118140960795 + 7455000 * 2 ^ 59
def prefixEnd_7455000 : Nat := 4983230072969 + 3 ^ 40 * 7455000 * 2
def baseEnd_7455000 : Nat := 1275999426422812503971695

theorem tailTrace_7455000 : CollatzResearch.WordTrace tailWord_7455000 prefixEnd_7455000 1275999426422812503971695 := by
  unfold tailWord_7455000
  simp only [CollatzResearch.WordTrace]
  refine ⟨135953093995907843739737227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181270791994543791652982969 135953093995907843739737227)
  ·
    refine ⟨203929640993861765609605841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135953093995907843739737227 203929640993861765609605841)
    ·
      refine ⟨152947230745396324207204381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203929640993861765609605841 152947230745396324207204381)
      ·
        refine ⟨57355211529523621577701643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152947230745396324207204381 57355211529523621577701643)
        ·
          refine ⟨86032817294285432366552465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57355211529523621577701643 86032817294285432366552465)
          ·
            refine ⟨64524612970714074274914349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86032817294285432366552465 64524612970714074274914349)
            ·
              refine ⟨24196729864017777853092881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64524612970714074274914349 24196729864017777853092881)
              ·
                refine ⟨18147547398013333389819661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24196729864017777853092881 18147547398013333389819661)
                ·
                  refine ⟨6805330274255000021182373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18147547398013333389819661 6805330274255000021182373)
                  ·
                    refine ⟨1275999426422812503971695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6805330274255000021182373 1275999426422812503971695)
                    ·
                      rfl

theorem cell23_7455000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 3, 4].length) (baseStart_7455000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455000 prefixEnd_7455000 := by exact prefixLift 7455000
  have htrace : WordTrace (prefixWord ++ tailWord_7455000) baseStart_7455000 baseEnd_7455000 := by
    simpa [prefixWord, tailWord_7455000, baseEnd_7455000] using wordTrace_append hprefix tailTrace_7455000
  have hstable : (prefixWord ++ tailWord_7455000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455000).length < 2 ^ (prefixWord ++ tailWord_7455000).sum := by decide
  have hdescent : baseEnd_7455000 < baseStart_7455000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455007 : List Nat := [1, 1, 2, 4, 3, 3, 1, 1, 2, 1, 4]
def baseStart_7455007 : Nat := 118140960795 + 7455007 * 2 ^ 59
def prefixEnd_7455007 : Nat := 4983230072969 + 3 ^ 40 * 7455007 * 2
def baseEnd_7455007 : Nat := 3828001873633018984527553

theorem tailTrace_7455007 : CollatzResearch.WordTrace tailWord_7455007 prefixEnd_7455007 3828001873633018984527553 := by
  unfold tailWord_7455007
  simp only [CollatzResearch.WordTrace]
  refine ⟨271906443302790327674979275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181270962201860218449986183 271906443302790327674979275)
  ·
    refine ⟨407859664954185491512468913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271906443302790327674979275 407859664954185491512468913)
    ·
      refine ⟨305894748715639118634351685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407859664954185491512468913 305894748715639118634351685)
      ·
        refine ⟨57355265384182334743940941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305894748715639118634351685 57355265384182334743940941)
        ·
          refine ⟨21508224519068375528977853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57355265384182334743940941 21508224519068375528977853)
          ·
            refine ⟨8065584194650640823366695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21508224519068375528977853 8065584194650640823366695)
            ·
              refine ⟨12098376291975961235050043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8065584194650640823366695 12098376291975961235050043)
              ·
                refine ⟨18147564437963941852575065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12098376291975961235050043 18147564437963941852575065)
                ·
                  refine ⟨13610673328472956389431299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18147564437963941852575065 13610673328472956389431299)
                  ·
                    refine ⟨20416009992709434584146949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13610673328472956389431299 20416009992709434584146949)
                    ·
                      refine ⟨3828001873633018984527553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20416009992709434584146949 3828001873633018984527553)
                      ·
                        rfl

theorem cell23_7455007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_7455007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455007 prefixEnd_7455007 := by exact prefixLift 7455007
  have htrace : WordTrace (prefixWord ++ tailWord_7455007) baseStart_7455007 baseEnd_7455007 := by
    simpa [prefixWord, tailWord_7455007, baseEnd_7455007] using wordTrace_append hprefix tailTrace_7455007
  have hstable : (prefixWord ++ tailWord_7455007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455007).length < 2 ^ (prefixWord ++ tailWord_7455007).sum := by decide
  have hdescent : baseEnd_7455007 < baseStart_7455007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455043 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 5, 5]
def baseStart_7455043 : Nat := 118140960795 + 7455043 * 2 ^ 59
def prefixEnd_7455043 : Nat := 4983230072969 + 3 ^ 40 * 7455043 * 2
def baseEnd_7455043 : Nat := 1276006786312193614559129

theorem tailTrace_7455043 : CollatzResearch.WordTrace tailWord_7455043 prefixEnd_7455043 1276006786312193614559129 := by
  unfold tailWord_7455043
  simp only [CollatzResearch.WordTrace]
  refine ⟨271907756330659905823289783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181271837553773270548859855 271907756330659905823289783)
  ·
    refine ⟨407861634495989858734934675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271907756330659905823289783 407861634495989858734934675)
    ·
      refine ⟨611792451743984788102402013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407861634495989858734934675 611792451743984788102402013)
      ·
        refine ⟨229422169403994295538400755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 611792451743984788102402013 229422169403994295538400755)
        ·
          refine ⟨344133254105991443307601133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229422169403994295538400755 344133254105991443307601133)
          ·
            refine ⟨129049970289746791240350425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344133254105991443307601133 129049970289746791240350425)
            ·
              refine ⟨96787477717310093430262819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129049970289746791240350425 96787477717310093430262819)
              ·
                refine ⟨145181216575965140145394229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96787477717310093430262819 145181216575965140145394229)
                ·
                  refine ⟨13610739053996731888630709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145181216575965140145394229 13610739053996731888630709)
                  ·
                    refine ⟨1276006786312193614559129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13610739053996731888630709 1276006786312193614559129)
                    ·
                      rfl

theorem cell23_7455043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 5].length) (baseStart_7455043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455043 prefixEnd_7455043 := by exact prefixLift 7455043
  have htrace : WordTrace (prefixWord ++ tailWord_7455043) baseStart_7455043 baseEnd_7455043 := by
    simpa [prefixWord, tailWord_7455043, baseEnd_7455043] using wordTrace_append hprefix tailTrace_7455043
  have hstable : (prefixWord ++ tailWord_7455043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455043).length < 2 ^ (prefixWord ++ tailWord_7455043).sum := by decide
  have hdescent : baseEnd_7455043 < baseStart_7455043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455057 : List Nat := [1, 2, 2, 1, 4, 2, 2, 2, 3, 1, 3]
def baseStart_7455057 : Nat := 118140960795 + 7455057 * 2 ^ 59
def prefixEnd_7455057 : Nat := 4983230072969 + 3 ^ 40 * 7455057 * 2
def baseEnd_7455057 : Nat := 3828027547665743788902323

theorem tailTrace_7455057 : CollatzResearch.WordTrace tailWord_7455057 prefixEnd_7455057 3828027547665743788902323 := by
  unfold tailWord_7455057
  simp only [CollatzResearch.WordTrace]
  refine ⟨271908266952609186214299425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181272177968406124142866283 271908266952609186214299425)
  ·
    refine ⟨203931200214456889660724569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271908266952609186214299425 203931200214456889660724569)
    ·
      refine ⟨152948400160842667245543427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203931200214456889660724569 152948400160842667245543427)
      ·
        refine ⟨229422600241264000868315141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152948400160842667245543427 229422600241264000868315141)
        ·
          refine ⟨43016737545237000162809089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229422600241264000868315141 43016737545237000162809089)
          ·
            refine ⟨32262553158927750122106817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43016737545237000162809089 32262553158927750122106817)
            ·
              refine ⟨24196914869195812591580113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32262553158927750122106817 24196914869195812591580113)
              ·
                refine ⟨18147686151896859443685085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24196914869195812591580113 18147686151896859443685085)
                ·
                  refine ⟨6805382306961322291381907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18147686151896859443685085 6805382306961322291381907)
                  ·
                    refine ⟨10208073460441983437072861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6805382306961322291381907 10208073460441983437072861)
                    ·
                      refine ⟨3828027547665743788902323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10208073460441983437072861 3828027547665743788902323)
                      ·
                        rfl

theorem cell23_7455057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3, 1, 3].length) (baseStart_7455057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455057 prefixEnd_7455057 := by exact prefixLift 7455057
  have htrace : WordTrace (prefixWord ++ tailWord_7455057) baseStart_7455057 baseEnd_7455057 := by
    simpa [prefixWord, tailWord_7455057, baseEnd_7455057] using wordTrace_append hprefix tailTrace_7455057
  have hstable : (prefixWord ++ tailWord_7455057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455057).length < 2 ^ (prefixWord ++ tailWord_7455057).sum := by decide
  have hdescent : baseEnd_7455057 < baseStart_7455057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455068 : List Nat := [2, 2, 4, 3, 1, 2, 1, 3, 1, 4]
def baseStart_7455068 : Nat := 118140960795 + 7455068 * 2 ^ 59
def prefixEnd_7455068 : Nat := 4983230072969 + 3 ^ 40 * 7455068 * 2
def baseEnd_7455068 : Nat := 1276011065317647748621591

theorem tailTrace_7455068 : CollatzResearch.WordTrace tailWord_7455068 prefixEnd_7455068 1276011065317647748621591 := by
  unfold tailWord_7455068
  simp only [CollatzResearch.WordTrace]
  refine ⟨135954334077784667546474929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181272445437046223395299905 135954334077784667546474929)
  ·
    refine ⟨101965750558338500659856197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135954334077784667546474929 101965750558338500659856197)
    ·
      refine ⟨19118578229688468873723037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101965750558338500659856197 19118578229688468873723037)
      ·
        refine ⟨7169466836133175827646139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19118578229688468873723037 7169466836133175827646139)
        ·
          refine ⟨10754200254199763741469209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7169466836133175827646139 10754200254199763741469209)
          ·
            refine ⟨8065650190649822806101907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10754200254199763741469209 8065650190649822806101907)
            ·
              refine ⟨12098475285974734209152861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8065650190649822806101907 12098475285974734209152861)
              ·
                refine ⟨4536928232240525328432323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12098475285974734209152861 4536928232240525328432323)
                ·
                  refine ⟨6805392348360787992648485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4536928232240525328432323 6805392348360787992648485)
                  ·
                    refine ⟨1276011065317647748621591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6805392348360787992648485 1276011065317647748621591)
                    ·
                      rfl

theorem cell23_7455068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_7455068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455068 prefixEnd_7455068 := by exact prefixLift 7455068
  have htrace : WordTrace (prefixWord ++ tailWord_7455068) baseStart_7455068 baseEnd_7455068 := by
    simpa [prefixWord, tailWord_7455068, baseEnd_7455068] using wordTrace_append hprefix tailTrace_7455068
  have hstable : (prefixWord ++ tailWord_7455068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455068).length < 2 ^ (prefixWord ++ tailWord_7455068).sum := by decide
  have hdescent : baseEnd_7455068 < baseStart_7455068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455083 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 5]
def baseStart_7455083 : Nat := 118140960795 + 7455083 * 2 ^ 59
def prefixEnd_7455083 : Nat := 4983230072969 + 3 ^ 40 * 7455083 * 2
def baseEnd_7455083 : Nat := 3828040898162760687177203

theorem tailTrace_7455083 : CollatzResearch.WordTrace tailWord_7455083 prefixEnd_7455083 3828040898162760687177203 := by
  unfold tailWord_7455083
  simp only [CollatzResearch.WordTrace]
  refine ⟨271909215250514992654745903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181272810167009995103163935 271909215250514992654745903)
  ·
    refine ⟨407863822875772488982118855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271909215250514992654745903 407863822875772488982118855)
    ·
      refine ⟨611795734313658733473178283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407863822875772488982118855 611795734313658733473178283)
      ·
        refine ⟨917693601470488100209767425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611795734313658733473178283 917693601470488100209767425)
        ·
          refine ⟨688270201102866075157325569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 917693601470488100209767425 688270201102866075157325569)
          ·
            refine ⟨516202650827149556367994177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 688270201102866075157325569 516202650827149556367994177)
            ·
              refine ⟨387151988120362167275995633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 516202650827149556367994177 387151988120362167275995633)
              ·
                refine ⟨290363991090271625456996725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387151988120362167275995633 290363991090271625456996725)
                ·
                  refine ⟨27221624164712964886593443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 290363991090271625456996725 27221624164712964886593443)
                  ·
                    refine ⟨40832436247069447329890165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27221624164712964886593443 40832436247069447329890165)
                    ·
                      refine ⟨3828040898162760687177203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40832436247069447329890165 3828040898162760687177203)
                      ·
                        rfl

theorem cell23_7455083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 5].length) (baseStart_7455083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455083 prefixEnd_7455083 := by exact prefixLift 7455083
  have htrace : WordTrace (prefixWord ++ tailWord_7455083) baseStart_7455083 baseEnd_7455083 := by
    simpa [prefixWord, tailWord_7455083, baseEnd_7455083] using wordTrace_append hprefix tailTrace_7455083
  have hstable : (prefixWord ++ tailWord_7455083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455083).length < 2 ^ (prefixWord ++ tailWord_7455083).sum := by decide
  have hdescent : baseEnd_7455083 < baseStart_7455083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455084 : List Nat := [2, 2, 1, 1, 6, 1, 1, 2, 2, 3, 2]
def baseStart_7455084 : Nat := 118140960795 + 7455084 * 2 ^ 59
def prefixEnd_7455084 : Nat := 4983230072969 + 3 ^ 40 * 7455084 * 2
def baseEnd_7455084 : Nat := 3828041411643415183264699

theorem tailTrace_7455084 : CollatzResearch.WordTrace tailWord_7455084 prefixEnd_7455084 3828041411643415183264699 := by
  unfold tailWord_7455084
  simp only [CollatzResearch.WordTrace]
  refine ⟨135954625861755684912766153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181272834482340913217021537 135954625861755684912766153)
  ·
    refine ⟨101965969396316763684574615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135954625861755684912766153 101965969396316763684574615)
    ·
      refine ⟨152948954094475145526861923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101965969396316763684574615 152948954094475145526861923)
      ·
        refine ⟨229423431141712718290292885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152948954094475145526861923 229423431141712718290292885)
        ·
          refine ⟨10754223334767783669857479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 229423431141712718290292885 10754223334767783669857479)
          ·
            refine ⟨16131335002151675504786219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10754223334767783669857479 16131335002151675504786219)
            ·
              refine ⟨24197002503227513257179329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16131335002151675504786219 24197002503227513257179329)
              ·
                refine ⟨18147751877420634942884497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24197002503227513257179329 18147751877420634942884497)
                ·
                  refine ⟨13610813908065476207163373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18147751877420634942884497 13610813908065476207163373)
                  ·
                    refine ⟨5104055215524553577686265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13610813908065476207163373 5104055215524553577686265)
                    ·
                      refine ⟨3828041411643415183264699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5104055215524553577686265 3828041411643415183264699)
                      ·
                        rfl

theorem cell23_7455084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 3, 2].length) (baseStart_7455084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455084 prefixEnd_7455084 := by exact prefixLift 7455084
  have htrace : WordTrace (prefixWord ++ tailWord_7455084) baseStart_7455084 baseEnd_7455084 := by
    simpa [prefixWord, tailWord_7455084, baseEnd_7455084] using wordTrace_append hprefix tailTrace_7455084
  have hstable : (prefixWord ++ tailWord_7455084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455084).length < 2 ^ (prefixWord ++ tailWord_7455084).sum := by decide
  have hdescent : baseEnd_7455084 < baseStart_7455084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455114 : List Nat := [3, 1, 2, 5, 1, 1, 1, 1, 3, 1, 4]
def baseStart_7455114 : Nat := 118140960795 + 7455114 * 2 ^ 59
def prefixEnd_7455114 : Nat := 4983230072969 + 3 ^ 40 * 7455114 * 2
def baseEnd_7455114 : Nat := 3828056816063050065889561

theorem tailTrace_7455114 : CollatzResearch.WordTrace tailWord_7455114 prefixEnd_7455114 3828056816063050065889561 := by
  unfold tailWord_7455114
  simp only [CollatzResearch.WordTrace]
  refine ⟨67977586478350671237281099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181273563942268456632749597 67977586478350671237281099)
  ·
    refine ⟨101966379717526006855921649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67977586478350671237281099 101966379717526006855921649)
    ·
      refine ⟨76474784788144505141941237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101966379717526006855921649 76474784788144505141941237)
      ·
        refine ⟨7169511073888547357056991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76474784788144505141941237 7169511073888547357056991)
        ·
          refine ⟨10754266610832821035585487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7169511073888547357056991 10754266610832821035585487)
          ·
            refine ⟨16131399916249231553378231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10754266610832821035585487 16131399916249231553378231)
            ·
              refine ⟨24197099874373847330067347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16131399916249231553378231 24197099874373847330067347)
              ·
                refine ⟨36295649811560770995101021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24197099874373847330067347 36295649811560770995101021)
                ·
                  refine ⟨13610868679335289123162883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36295649811560770995101021 13610868679335289123162883)
                  ·
                    refine ⟨20416303019002933684744325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13610868679335289123162883 20416303019002933684744325)
                    ·
                      refine ⟨3828056816063050065889561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20416303019002933684744325 3828056816063050065889561)
                      ·
                        rfl

theorem cell23_7455114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_7455114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455114 prefixEnd_7455114 := by exact prefixLift 7455114
  have htrace : WordTrace (prefixWord ++ tailWord_7455114) baseStart_7455114 baseEnd_7455114 := by
    simpa [prefixWord, tailWord_7455114, baseEnd_7455114] using wordTrace_append hprefix tailTrace_7455114
  have hstable : (prefixWord ++ tailWord_7455114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455114).length < 2 ^ (prefixWord ++ tailWord_7455114).sum := by decide
  have hdescent : baseEnd_7455114 < baseStart_7455114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455134 : List Nat := [4, 3, 1, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_7455134 : Nat := 118140960795 + 7455134 * 2 ^ 59
def prefixEnd_7455134 : Nat := 4983230072969 + 3 ^ 40 * 7455134 * 2
def baseEnd_7455134 : Nat := 3828067085676139987639469

theorem tailTrace_7455134 : CollatzResearch.WordTrace tailWord_7455134 prefixEnd_7455134 3828067085676139987639469 := by
  unfold tailWord_7455134
  simp only [CollatzResearch.WordTrace]
  refine ⟨33988884421666278545606557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181274050248886818909901637 33988884421666278545606557)
  ·
    refine ⟨12745831658124854454602459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33988884421666278545606557 12745831658124854454602459)
    ·
      refine ⟨19118747487187281681903689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12745831658124854454602459 19118747487187281681903689)
      ·
        refine ⟨14339060615390461261427767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19118747487187281681903689 14339060615390461261427767)
        ·
          refine ⟨21508590923085691892141651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14339060615390461261427767 21508590923085691892141651)
          ·
            refine ⟨32262886384628537838212477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21508590923085691892141651 32262886384628537838212477)
            ·
              refine ⟨12098582394235701689329679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32262886384628537838212477 12098582394235701689329679)
              ·
                refine ⟨18147873591353552533994519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12098582394235701689329679 18147873591353552533994519)
                ·
                  refine ⟨27221810387030328800991779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18147873591353552533994519 27221810387030328800991779)
                  ·
                    refine ⟨40832715580545493201487669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27221810387030328800991779 40832715580545493201487669)
                    ·
                      refine ⟨3828067085676139987639469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40832715580545493201487669 3828067085676139987639469)
                      ·
                        rfl

theorem cell23_7455134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_7455134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455134 prefixEnd_7455134 := by exact prefixLift 7455134
  have htrace : WordTrace (prefixWord ++ tailWord_7455134) baseStart_7455134 baseEnd_7455134 := by
    simpa [prefixWord, tailWord_7455134, baseEnd_7455134] using wordTrace_append hprefix tailTrace_7455134
  have hstable : (prefixWord ++ tailWord_7455134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455134).length < 2 ^ (prefixWord ++ tailWord_7455134).sum := by decide
  have hdescent : baseEnd_7455134 < baseStart_7455134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455137 : List Nat := [1, 2, 3, 5, 2, 10]
def baseStart_7455137 : Nat := 118140960795 + 7455137 * 2 ^ 59
def prefixEnd_7455137 : Nat := 4983230072969 + 3 ^ 40 * 7455137 * 2
def baseEnd_7455137 : Nat := 15753368831761742699185

theorem tailTrace_7455137 : CollatzResearch.WordTrace tailWord_7455137 prefixEnd_7455137 15753368831761742699185 := by
  unfold tailWord_7455137
  simp only [CollatzResearch.WordTrace]
  refine ⟨271911184792319359877211665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181274123194879573251474443 271911184792319359877211665)
  ·
    refine ⟨203933388594239519907908749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271911184792319359877211665 203933388594239519907908749)
    ·
      refine ⟨76475020722839819965465781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203933388594239519907908749 76475020722839819965465781)
      ·
        refine ⟨7169533192766233121762417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76475020722839819965465781 7169533192766233121762417)
        ·
          refine ⟨5377149894574674841321813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7169533192766233121762417 5377149894574674841321813)
          ·
            refine ⟨15753368831761742699185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5377149894574674841321813 15753368831761742699185)
            ·
              rfl

theorem cell23_7455137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 10].length) (baseStart_7455137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455137 prefixEnd_7455137 := by exact prefixLift 7455137
  have htrace : WordTrace (prefixWord ++ tailWord_7455137) baseStart_7455137 baseEnd_7455137 := by
    simpa [prefixWord, tailWord_7455137, baseEnd_7455137] using wordTrace_append hprefix tailTrace_7455137
  have hstable : (prefixWord ++ tailWord_7455137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455137).length < 2 ^ (prefixWord ++ tailWord_7455137).sum := by decide
  have hdescent : baseEnd_7455137 < baseStart_7455137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455164 : List Nat := [2, 2, 2, 4, 1, 2, 2, 1, 1, 3, 3]
def baseStart_7455164 : Nat := 118140960795 + 7455164 * 2 ^ 59
def prefixEnd_7455164 : Nat := 4983230072969 + 3 ^ 40 * 7455164 * 2
def baseEnd_7455164 : Nat := 3828082490095774870264331

theorem tailTrace_7455164 : CollatzResearch.WordTrace tailWord_7455164 prefixEnd_7455164 3828082490095774870264331 := by
  unfold tailWord_7455164
  simp only [CollatzResearch.WordTrace]
  refine ⟨135956084781610771744222273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181274779708814362325629697 135956084781610771744222273)
  ·
    refine ⟨101967063586208078808166705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135956084781610771744222273 101967063586208078808166705)
    ·
      refine ⟨76475297689656059106125029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101967063586208078808166705 76475297689656059106125029)
      ·
        refine ⟨14339118316810511082398443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76475297689656059106125029 14339118316810511082398443)
        ·
          refine ⟨21508677475215766623597665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14339118316810511082398443 21508677475215766623597665)
          ·
            refine ⟨16131508106411824967698249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21508677475215766623597665 16131508106411824967698249)
            ·
              refine ⟨12098631079808868725773687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16131508106411824967698249 12098631079808868725773687)
              ·
                refine ⟨18147946619713303088660531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12098631079808868725773687 18147946619713303088660531)
                ·
                  refine ⟨27221919929569954632990797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18147946619713303088660531 27221919929569954632990797)
                  ·
                    refine ⟨10208219973588732987371549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27221919929569954632990797 10208219973588732987371549)
                    ·
                      refine ⟨3828082490095774870264331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10208219973588732987371549 3828082490095774870264331)
                      ·
                        rfl

theorem cell23_7455164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_7455164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455164 prefixEnd_7455164 := by exact prefixLift 7455164
  have htrace : WordTrace (prefixWord ++ tailWord_7455164) baseStart_7455164 baseEnd_7455164 := by
    simpa [prefixWord, tailWord_7455164, baseEnd_7455164] using wordTrace_append hprefix tailTrace_7455164
  have hstable : (prefixWord ++ tailWord_7455164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455164).length < 2 ^ (prefixWord ++ tailWord_7455164).sum := by decide
  have hdescent : baseEnd_7455164 < baseStart_7455164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455200 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 4]
def baseStart_7455200 : Nat := 118140960795 + 7455200 * 2 ^ 59
def prefixEnd_7455200 : Nat := 4983230072969 + 3 ^ 40 * 7455200 * 2
def baseEnd_7455200 : Nat := 3828100975399336729414165

theorem tailTrace_7455200 : CollatzResearch.WordTrace tailWord_7455200 prefixEnd_7455200 3828100975399336729414165 := by
  unfold tailWord_7455200
  simp only [CollatzResearch.WordTrace]
  refine ⟨135956741295545560818377527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181275655060727414424503369 135956741295545560818377527)
  ·
    refine ⟨203935111943318341227566291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135956741295545560818377527 203935111943318341227566291)
    ·
      refine ⟨305902667914977511841349437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203935111943318341227566291 305902667914977511841349437)
      ·
        refine ⟨114713500468116566940506039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305902667914977511841349437 114713500468116566940506039)
        ·
          refine ⟨172070250702174850410759059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114713500468116566940506039 172070250702174850410759059)
          ·
            refine ⟨258105376053262275616138589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172070250702174850410759059 258105376053262275616138589)
            ·
              refine ⟨96789516019973353356051971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258105376053262275616138589 96789516019973353356051971)
              ·
                refine ⟨145184274029960030034077957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96789516019973353356051971 145184274029960030034077957)
                ·
                  refine ⟨27222051380617505631389617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145184274029960030034077957 27222051380617505631389617)
                  ·
                    refine ⟨20416538535463129223542213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27222051380617505631389617 20416538535463129223542213)
                    ·
                      refine ⟨3828100975399336729414165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20416538535463129223542213 3828100975399336729414165)
                      ·
                        rfl

theorem cell23_7455200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_7455200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455200 prefixEnd_7455200 := by exact prefixLift 7455200
  have htrace : WordTrace (prefixWord ++ tailWord_7455200) baseStart_7455200 baseEnd_7455200 := by
    simpa [prefixWord, tailWord_7455200, baseEnd_7455200] using wordTrace_append hprefix tailTrace_7455200
  have hstable : (prefixWord ++ tailWord_7455200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455200).length < 2 ^ (prefixWord ++ tailWord_7455200).sum := by decide
  have hdescent : baseEnd_7455200 < baseStart_7455200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455244 : List Nat := [2, 2, 1, 2, 4, 1, 3, 3, 5]
def baseStart_7455244 : Nat := 118140960795 + 7455244 * 2 ^ 59
def prefixEnd_7455244 : Nat := 4983230072969 + 3 ^ 40 * 7455244 * 2
def baseEnd_7455244 : Nat := 425347063172014950807107

theorem tailTrace_7455244 : CollatzResearch.WordTrace tailWord_7455244 prefixEnd_7455244 425347063172014950807107 := by
  unfold tailWord_7455244
  simp only [CollatzResearch.WordTrace]
  refine ⟨135957543701465858575678393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181276724935287811434237857 135957543701465858575678393)
  ·
    refine ⟨101968157776099393931758795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135957543701465858575678393 101968157776099393931758795)
    ·
      refine ⟨152952236664149090897638193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101968157776099393931758795 152952236664149090897638193)
      ·
        refine ⟨114714177498111818173228645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152952236664149090897638193 114714177498111818173228645)
        ·
          refine ⟨21508908280895965907480371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114714177498111818173228645 21508908280895965907480371)
          ·
            refine ⟨32263362421343948861220557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21508908280895965907480371 32263362421343948861220557)
            ·
              refine ⟨12098760908003980822957709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32263362421343948861220557 12098760908003980822957709)
              ·
                refine ⟨4537035340501492808609141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12098760908003980822957709 4537035340501492808609141)
                ·
                  refine ⟨425347063172014950807107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4537035340501492808609141 425347063172014950807107)
                  ·
                    rfl

theorem cell23_7455244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3, 5].length) (baseStart_7455244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455244 prefixEnd_7455244 := by exact prefixLift 7455244
  have htrace : WordTrace (prefixWord ++ tailWord_7455244) baseStart_7455244 baseEnd_7455244 := by
    simpa [prefixWord, tailWord_7455244, baseEnd_7455244] using wordTrace_append hprefix tailTrace_7455244
  have hstable : (prefixWord ++ tailWord_7455244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455244).length < 2 ^ (prefixWord ++ tailWord_7455244).sum := by decide
  have hdescent : baseEnd_7455244 < baseStart_7455244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455261 : List Nat := [1, 4, 2, 2, 1, 3, 3, 2, 5]
def baseStart_7455261 : Nat := 118140960795 + 7455261 * 2 ^ 59
def prefixEnd_7455261 : Nat := 4983230072969 + 3 ^ 40 * 7455261 * 2
def baseEnd_7455261 : Nat := 425348033079917887861265

theorem tailTrace_7455261 : CollatzResearch.WordTrace tailWord_7455261 prefixEnd_7455261 425348033079917887861265 := by
  unfold tailWord_7455261
  simp only [CollatzResearch.WordTrace]
  refine ⟨271915707443870129054725637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181277138295913419369817091 271915707443870129054725637)
  ·
    refine ⟨50984195145725649197761057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271915707443870129054725637 50984195145725649197761057)
    ·
      refine ⟨38238146359294236898320793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50984195145725649197761057 38238146359294236898320793)
      ·
        refine ⟨28678609769470677673740595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38238146359294236898320793 28678609769470677673740595)
        ·
          refine ⟨43017914654206016510610893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28678609769470677673740595 43017914654206016510610893)
          ·
            refine ⟨16131717995327256191479085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43017914654206016510610893 16131717995327256191479085)
            ·
              refine ⟨6049394248247721071804657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16131717995327256191479085 6049394248247721071804657)
              ·
                refine ⟨4537045686185790803853493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6049394248247721071804657 4537045686185790803853493)
                ·
                  refine ⟨425348033079917887861265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4537045686185790803853493 425348033079917887861265)
                  ·
                    rfl

theorem cell23_7455261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2, 5].length) (baseStart_7455261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455261 prefixEnd_7455261 := by exact prefixLift 7455261
  have htrace : WordTrace (prefixWord ++ tailWord_7455261) baseStart_7455261 baseEnd_7455261 := by
    simpa [prefixWord, tailWord_7455261, baseEnd_7455261] using wordTrace_append hprefix tailTrace_7455261
  have hstable : (prefixWord ++ tailWord_7455261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455261).length < 2 ^ (prefixWord ++ tailWord_7455261).sum := by decide
  have hdescent : baseEnd_7455261 < baseStart_7455261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455267 : List Nat := [1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 5]
def baseStart_7455267 : Nat := 118140960795 + 7455267 * 2 ^ 59
def prefixEnd_7455267 : Nat := 4983230072969 + 3 ^ 40 * 7455267 * 2
def baseEnd_7455267 : Nat := 3828135378603187967276357

theorem tailTrace_7455267 : CollatzResearch.WordTrace tailWord_7455267 prefixEnd_7455267 3828135378603187967276357 := by
  unfold tailWord_7455267
  simp only [CollatzResearch.WordTrace]
  refine ⟨271915926281848392079444055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181277284187898928052962703 271915926281848392079444055)
  ·
    refine ⟨407873889422772588119166083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271915926281848392079444055 407873889422772588119166083)
    ·
      refine ⟨611810834134158882178749125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407873889422772588119166083 611810834134158882178749125)
      ·
        refine ⟨114714531400154790408515461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 611810834134158882178749125 114714531400154790408515461)
        ·
          refine ⟨21508974637529023201596649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114714531400154790408515461 21508974637529023201596649)
          ·
            refine ⟨16131730978146767401197487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21508974637529023201596649 16131730978146767401197487)
            ·
              refine ⟨24197596467220151101796231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16131730978146767401197487 24197596467220151101796231)
              ·
                refine ⟨36296394700830226652694347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24197596467220151101796231 36296394700830226652694347)
                ·
                  refine ⟨54444592051245339979041521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36296394700830226652694347 54444592051245339979041521)
                  ·
                    refine ⟨40833444038434004984281141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54444592051245339979041521 40833444038434004984281141)
                    ·
                      refine ⟨3828135378603187967276357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40833444038434004984281141 3828135378603187967276357)
                      ·
                        rfl

theorem cell23_7455267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_7455267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455267 prefixEnd_7455267 := by exact prefixLift 7455267
  have htrace : WordTrace (prefixWord ++ tailWord_7455267) baseStart_7455267 baseEnd_7455267 := by
    simpa [prefixWord, tailWord_7455267, baseEnd_7455267] using wordTrace_append hprefix tailTrace_7455267
  have hstable : (prefixWord ++ tailWord_7455267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455267).length < 2 ^ (prefixWord ++ tailWord_7455267).sum := by decide
  have hdescent : baseEnd_7455267 < baseStart_7455267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455287 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 5, 4]
def baseStart_7455287 : Nat := 118140960795 + 7455287 * 2 ^ 59
def prefixEnd_7455287 : Nat := 4983230072969 + 3 ^ 40 * 7455287 * 2
def baseEnd_7455287 : Nat := 1276048549405425963008755

theorem tailTrace_7455287 : CollatzResearch.WordTrace tailWord_7455287 prefixEnd_7455287 1276048549405425963008755 := by
  unfold tailWord_7455287
  simp only [CollatzResearch.WordTrace]
  refine ⟨271916655741775935495172115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181277770494517290330114743 271916655741775935495172115)
  ·
    refine ⟨407874983612663903242758173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271916655741775935495172115 407874983612663903242758173)
    ·
      refine ⟨152953118854748963716034315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407874983612663903242758173 152953118854748963716034315)
      ·
        refine ⟨229429678282123445574051473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152953118854748963716034315 229429678282123445574051473)
        ·
          refine ⟨172072258711592584180538605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229429678282123445574051473 172072258711592584180538605)
          ·
            refine ⟨64527097016847219067701977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172072258711592584180538605 64527097016847219067701977)
            ·
              refine ⟨48395322762635414300776483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64527097016847219067701977 48395322762635414300776483)
              ·
                refine ⟨72592984143953121451164725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48395322762635414300776483 72592984143953121451164725)
                ·
                  refine ⟨6805592263495605136046693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72592984143953121451164725 6805592263495605136046693)
                  ·
                    refine ⟨1276048549405425963008755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6805592263495605136046693 1276048549405425963008755)
                    ·
                      rfl

theorem cell23_7455287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5, 4].length) (baseStart_7455287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455287 prefixEnd_7455287 := by exact prefixLift 7455287
  have htrace : WordTrace (prefixWord ++ tailWord_7455287) baseStart_7455287 baseEnd_7455287 := by
    simpa [prefixWord, tailWord_7455287, baseEnd_7455287] using wordTrace_append hprefix tailTrace_7455287
  have hstable : (prefixWord ++ tailWord_7455287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455287).length < 2 ^ (prefixWord ++ tailWord_7455287).sum := by decide
  have hdescent : baseEnd_7455287 < baseStart_7455287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455314 : List Nat := [3, 2, 2, 1, 2, 1, 1, 4, 2, 2, 3]
def baseStart_7455314 : Nat := 118140960795 + 7455314 * 2 ^ 59
def prefixEnd_7455314 : Nat := 4983230072969 + 3 ^ 40 * 7455314 * 2
def baseEnd_7455314 : Nat := 3828159512193949283388641

theorem tailTrace_7455314 : CollatzResearch.WordTrace tailWord_7455314 prefixEnd_7455314 3828159512193949283388641 := by
  unfold tailWord_7455314
  simp only [CollatzResearch.WordTrace]
  refine ⟨67979410128169529776601249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181278427008452079404269997 67979410128169529776601249)
  ·
    refine ⟨50984557596127147332450937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67979410128169529776601249 50984557596127147332450937)
    ·
      refine ⟨38238418197095360499338203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50984557596127147332450937 38238418197095360499338203)
      ·
        refine ⟨57357627295643040749007305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38238418197095360499338203 57357627295643040749007305)
        ·
          refine ⟨43018220471732280561755479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57357627295643040749007305 43018220471732280561755479)
          ·
            refine ⟨64527330707598420842633219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43018220471732280561755479 64527330707598420842633219)
            ·
              refine ⟨96790996061397631263949829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64527330707598420842633219 96790996061397631263949829)
              ·
                refine ⟨18148311761512055861990593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96790996061397631263949829 18148311761512055861990593)
                ·
                  refine ⟨13611233821134041896492945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18148311761512055861990593 13611233821134041896492945)
                  ·
                    refine ⟨10208425365850531422369709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13611233821134041896492945 10208425365850531422369709)
                    ·
                      refine ⟨3828159512193949283388641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10208425365850531422369709 3828159512193949283388641)
                      ·
                        rfl

theorem cell23_7455314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_7455314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455314 prefixEnd_7455314 := by exact prefixLift 7455314
  have htrace : WordTrace (prefixWord ++ tailWord_7455314) baseStart_7455314 baseEnd_7455314 := by
    simpa [prefixWord, tailWord_7455314, baseEnd_7455314] using wordTrace_append hprefix tailTrace_7455314
  have hstable : (prefixWord ++ tailWord_7455314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455314).length < 2 ^ (prefixWord ++ tailWord_7455314).sum := by decide
  have hdescent : baseEnd_7455314 < baseStart_7455314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455317 : List Nat := [1, 3, 2, 2, 1, 1, 3, 4, 6]
def baseStart_7455317 : Nat := 118140960795 + 7455317 * 2 ^ 59
def prefixEnd_7455317 : Nat := 4983230072969 + 3 ^ 40 * 7455317 * 2
def baseEnd_7455317 : Nat := 425351228070656974627903

theorem tailTrace_7455317 : CollatzResearch.WordTrace tailWord_7455317 prefixEnd_7455317 425351228070656974627903 := by
  unfold tailWord_7455317
  simp only [CollatzResearch.WordTrace]
  refine ⟨271917749931667250618764205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181278499954444833745842803 271917749931667250618764205)
  ·
    refine ⟨101969156224375218982036577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271917749931667250618764205 101969156224375218982036577)
    ·
      refine ⟨76476867168281414236527433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101969156224375218982036577 76476867168281414236527433)
      ·
        refine ⟨57357650376211060677395575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76476867168281414236527433 57357650376211060677395575)
        ·
          refine ⟨86036475564316591016093363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57357650376211060677395575 86036475564316591016093363)
          ·
            refine ⟨129054713346474886524140045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86036475564316591016093363 129054713346474886524140045)
            ·
              refine ⟨48395517504928082446552517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129054713346474886524140045 48395517504928082446552517)
              ·
                refine ⟨9074159532174015458728597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48395517504928082446552517 9074159532174015458728597)
                ·
                  refine ⟨425351228070656974627903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9074159532174015458728597 425351228070656974627903)
                  ·
                    rfl

theorem cell23_7455317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 6].length) (baseStart_7455317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455317 prefixEnd_7455317 := by exact prefixLift 7455317
  have htrace : WordTrace (prefixWord ++ tailWord_7455317) baseStart_7455317 baseEnd_7455317 := by
    simpa [prefixWord, tailWord_7455317, baseEnd_7455317] using wordTrace_append hprefix tailTrace_7455317
  have hstable : (prefixWord ++ tailWord_7455317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455317).length < 2 ^ (prefixWord ++ tailWord_7455317).sum := by decide
  have hdescent : baseEnd_7455317 < baseStart_7455317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455378 : List Nat := [3, 2, 3, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_7455378 : Nat := 118140960795 + 7455378 * 2 ^ 59
def prefixEnd_7455378 : Nat := 4983230072969 + 3 ^ 40 * 7455378 * 2
def baseEnd_7455378 : Nat := 3828192374955837032988347

theorem tailTrace_7455378 : CollatzResearch.WordTrace tailWord_7455378 prefixEnd_7455378 3828192374955837032988347 := by
  unfold tailWord_7455378
  simp only [CollatzResearch.WordTrace]
  refine ⟨67979993696111564509183697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181279983189630838691156525 67979993696111564509183697)
  ·
    refine ⟨50984995272083673381887773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67979993696111564509183697 50984995272083673381887773)
    ·
      refine ⟨19119373227031377518207915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50984995272083673381887773 19119373227031377518207915)
      ·
        refine ⟨28679059840547066277311873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19119373227031377518207915 28679059840547066277311873)
        ·
          refine ⟨21509294880410299707983905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28679059840547066277311873 21509294880410299707983905)
          ·
            refine ⟨16131971160307724780987929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21509294880410299707983905 16131971160307724780987929)
            ·
              refine ⟨12098978370230793585740947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16131971160307724780987929 12098978370230793585740947)
              ·
                refine ⟨18148467555346190378611421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12098978370230793585740947 18148467555346190378611421)
                ·
                  refine ⟨6805675333254821391979283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18148467555346190378611421 6805675333254821391979283)
                  ·
                    refine ⟨10208512999882232087968925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6805675333254821391979283 10208512999882232087968925)
                    ·
                      refine ⟨3828192374955837032988347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10208512999882232087968925 3828192374955837032988347)
                      ·
                        rfl

theorem cell23_7455378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_7455378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455378 prefixEnd_7455378 := by exact prefixLift 7455378
  have htrace : WordTrace (prefixWord ++ tailWord_7455378) baseStart_7455378 baseEnd_7455378 := by
    simpa [prefixWord, tailWord_7455378, baseEnd_7455378] using wordTrace_append hprefix tailTrace_7455378
  have hstable : (prefixWord ++ tailWord_7455378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455378).length < 2 ^ (prefixWord ++ tailWord_7455378).sum := by decide
  have hdescent : baseEnd_7455378 < baseStart_7455378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455407 : List Nat := [1, 1, 2, 1, 2, 6, 1, 9]
def baseStart_7455407 : Nat := 118140960795 + 7455407 * 2 ^ 59
def prefixEnd_7455407 : Nat := 4983230072969 + 3 ^ 40 * 7455407 * 2
def baseEnd_7455407 : Nat := 141785454292400645167619

theorem tailTrace_7455407 : CollatzResearch.WordTrace tailWord_7455407 prefixEnd_7455407 141785454292400645167619 := by
  unfold tailWord_7455407
  simp only [CollatzResearch.WordTrace]
  refine ⟨271921032501341195989540475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181280688334227463993026983 271921032501341195989540475)
  ·
    refine ⟨407881548752011793984310713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271921032501341195989540475 407881548752011793984310713)
    ·
      refine ⟨305911161564008845488233035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407881548752011793984310713 305911161564008845488233035)
      ·
        refine ⟨458866742346013268232349553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305911161564008845488233035 458866742346013268232349553)
        ·
          refine ⟨344150056759509951174262165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 458866742346013268232349553 344150056759509951174262165)
          ·
            refine ⟨16132033910602028961293539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 344150056759509951174262165 16132033910602028961293539)
            ·
              refine ⟨24198050865903043441940309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16132033910602028961293539 24198050865903043441940309)
              ·
                refine ⟨141785454292400645167619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24198050865903043441940309 141785454292400645167619)
                ·
                  rfl

theorem cell23_7455407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 9].length) (baseStart_7455407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455407 prefixEnd_7455407 := by exact prefixLift 7455407
  have htrace : WordTrace (prefixWord ++ tailWord_7455407) baseStart_7455407 baseEnd_7455407 := by
    simpa [prefixWord, tailWord_7455407, baseEnd_7455407] using wordTrace_append hprefix tailTrace_7455407
  have hstable : (prefixWord ++ tailWord_7455407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455407).length < 2 ^ (prefixWord ++ tailWord_7455407).sum := by decide
  have hdescent : baseEnd_7455407 < baseStart_7455407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455421 : List Nat := [1, 4, 1, 2, 1, 3, 2, 3, 1, 2, 3]
def baseStart_7455421 : Nat := 118140960795 + 7455421 * 2 ^ 59
def prefixEnd_7455421 : Nat := 4983230072969 + 3 ^ 40 * 7455421 * 2
def baseEnd_7455421 : Nat := 3828214454623980364750649

theorem tailTrace_7455421 : CollatzResearch.WordTrace tailWord_7455421 prefixEnd_7455421 3828214454623980364750649 := by
  unfold tailWord_7455421
  simp only [CollatzResearch.WordTrace]
  refine ⟨271921543123290476380550117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181281028748860317587033411 271921543123290476380550117)
  ·
    refine ⟨50985289335616964321353147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271921543123290476380550117 50985289335616964321353147)
    ·
      refine ⟨76477934003425446482029721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50985289335616964321353147 76477934003425446482029721)
      ·
        refine ⟨57358450502569084861522291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76477934003425446482029721 57358450502569084861522291)
        ·
          refine ⟨86037675753853627292283437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57358450502569084861522291 86037675753853627292283437)
          ·
            refine ⟨32264128407695110234606289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86037675753853627292283437 32264128407695110234606289)
            ·
              refine ⟨24198096305771332675954717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32264128407695110234606289 24198096305771332675954717)
              ·
                refine ⟨9074286114664249753483019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24198096305771332675954717 9074286114664249753483019)
                ·
                  refine ⟨13611429171996374630224529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9074286114664249753483019 13611429171996374630224529)
                  ·
                    refine ⟨10208571878997280972668397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13611429171996374630224529 10208571878997280972668397)
                    ·
                      refine ⟨3828214454623980364750649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10208571878997280972668397 3828214454623980364750649)
                      ·
                        rfl

theorem cell23_7455421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_7455421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455421 prefixEnd_7455421 := by exact prefixLift 7455421
  have htrace : WordTrace (prefixWord ++ tailWord_7455421) baseStart_7455421 baseEnd_7455421 := by
    simpa [prefixWord, tailWord_7455421, baseEnd_7455421] using wordTrace_append hprefix tailTrace_7455421
  have hstable : (prefixWord ++ tailWord_7455421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455421).length < 2 ^ (prefixWord ++ tailWord_7455421).sum := by decide
  have hdescent : baseEnd_7455421 < baseStart_7455421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455467 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 4, 6]
def baseStart_7455467 : Nat := 118140960795 + 7455467 * 2 ^ 59
def prefixEnd_7455467 : Nat := 4983230072969 + 3 ^ 40 * 7455467 * 2
def baseEnd_7455467 : Nat := 1276079358244695728258479

theorem tailTrace_7455467 : CollatzResearch.WordTrace tailWord_7455467 prefixEnd_7455467 1276079358244695728258479 := by
  unfold tailWord_7455467
  simp only [CollatzResearch.WordTrace]
  refine ⟨271923220881123826236724655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181282147254082550824483103 271923220881123826236724655)
  ·
    refine ⟨407884831321685739355086983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271923220881123826236724655 407884831321685739355086983)
    ·
      refine ⟨611827246982528609032630475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407884831321685739355086983 611827246982528609032630475)
      ·
        refine ⟨917740870473792913548945713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611827246982528609032630475 917740870473792913548945713)
        ·
          refine ⟨688305652855344685161709285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 917740870473792913548945713 688305652855344685161709285)
          ·
            refine ⟨129057309910377128467820491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 688305652855344685161709285 129057309910377128467820491)
            ·
              refine ⟨193585964865565692701730737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129057309910377128467820491 193585964865565692701730737)
              ·
                refine ⟨145189473649174269526298053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193585964865565692701730737 145189473649174269526298053)
                ·
                  refine ⟨27223026309220175536180885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145189473649174269526298053 27223026309220175536180885)
                  ·
                    refine ⟨1276079358244695728258479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27223026309220175536180885 1276079358244695728258479)
                    ·
                      rfl

theorem cell23_7455467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 6].length) (baseStart_7455467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455467 prefixEnd_7455467 := by exact prefixLift 7455467
  have htrace : WordTrace (prefixWord ++ tailWord_7455467) baseStart_7455467 baseEnd_7455467 := by
    simpa [prefixWord, tailWord_7455467, baseEnd_7455467] using wordTrace_append hprefix tailTrace_7455467
  have hstable : (prefixWord ++ tailWord_7455467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455467).length < 2 ^ (prefixWord ++ tailWord_7455467).sum := by decide
  have hdescent : baseEnd_7455467 < baseStart_7455467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455487 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 6]
def baseStart_7455487 : Nat := 118140960795 + 7455487 * 2 ^ 59
def prefixEnd_7455487 : Nat := 4983230072969 + 3 ^ 40 * 7455487 * 2
def baseEnd_7455487 : Nat := 3828248344347177106525345

theorem tailTrace_7455487 : CollatzResearch.WordTrace tailWord_7455487 prefixEnd_7455487 3828248344347177106525345 := by
  unfold tailWord_7455487
  simp only [CollatzResearch.WordTrace]
  refine ⟨271923950341051369652452715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181282633560700913101635143 271923950341051369652452715)
  ·
    refine ⟨407885925511577054478679073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271923950341051369652452715 407885925511577054478679073)
    ·
      refine ⟨305914444133682790859009305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407885925511577054478679073 305914444133682790859009305)
      ·
        refine ⟨229435833100262093144256979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305914444133682790859009305 229435833100262093144256979)
        ·
          refine ⟨344153749650393139716385469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229435833100262093144256979 344153749650393139716385469)
          ·
            refine ⟨129057656118897427393644551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344153749650393139716385469 129057656118897427393644551)
            ·
              refine ⟨193586484178346141090466827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129057656118897427393644551 193586484178346141090466827)
              ·
                refine ⟨290379726267519211635700241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193586484178346141090466827 290379726267519211635700241)
                ·
                  refine ⟨217784794700639408726775181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 290379726267519211635700241 217784794700639408726775181)
                  ·
                    refine ⟨81669298012739778272540693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 217784794700639408726775181 81669298012739778272540693)
                    ·
                      refine ⟨3828248344347177106525345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81669298012739778272540693 3828248344347177106525345)
                      ·
                        rfl

theorem cell23_7455487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_7455487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455487 prefixEnd_7455487 := by exact prefixLift 7455487
  have htrace : WordTrace (prefixWord ++ tailWord_7455487) baseStart_7455487 baseEnd_7455487 := by
    simpa [prefixWord, tailWord_7455487, baseEnd_7455487] using wordTrace_append hprefix tailTrace_7455487
  have hstable : (prefixWord ++ tailWord_7455487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455487).length < 2 ^ (prefixWord ++ tailWord_7455487).sum := by decide
  have hdescent : baseEnd_7455487 < baseStart_7455487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455514 : List Nat := [3, 1, 1, 3, 2, 1, 3, 2, 7]
def baseStart_7455514 : Nat := 118140960795 + 7455514 * 2 ^ 59
def prefixEnd_7455514 : Nat := 4983230072969 + 3 ^ 40 * 7455514 * 2
def baseEnd_7455514 : Nat := 425362467591649833431969

theorem tailTrace_7455514 : CollatzResearch.WordTrace tailWord_7455514 prefixEnd_7455514 425362467591649833431969 := by
  unfold tailWord_7455514
  simp only [CollatzResearch.WordTrace]
  refine ⟨67981233777988388315921399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181283290074635702175790397 67981233777988388315921399)
  ·
    refine ⟨101971850666982582473882099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67981233777988388315921399 101971850666982582473882099)
    ·
      refine ⟨152957776000473873710823149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101971850666982582473882099 152957776000473873710823149)
      ·
        refine ⟨57359166000177702641558681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152957776000473873710823149 57359166000177702641558681)
        ·
          refine ⟨43019374500133276981169011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57359166000177702641558681 43019374500133276981169011)
          ·
            refine ⟨64529061750199915471753517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43019374500133276981169011 64529061750199915471753517)
            ·
              refine ⟨24198398156324968301907569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64529061750199915471753517 24198398156324968301907569)
              ·
                refine ⟨18148798617243726226430677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24198398156324968301907569 18148798617243726226430677)
                ·
                  refine ⟨425362467591649833431969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18148798617243726226430677 425362467591649833431969)
                  ·
                    rfl

theorem cell23_7455514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 7].length) (baseStart_7455514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455514 prefixEnd_7455514 := by exact prefixLift 7455514
  have htrace : WordTrace (prefixWord ++ tailWord_7455514) baseStart_7455514 baseEnd_7455514 := by
    simpa [prefixWord, tailWord_7455514, baseEnd_7455514] using wordTrace_append hprefix tailTrace_7455514
  have hstable : (prefixWord ++ tailWord_7455514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455514).length < 2 ^ (prefixWord ++ tailWord_7455514).sum := by decide
  have hdescent : baseEnd_7455514 < baseStart_7455514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455541 : List Nat := [1, 3, 3, 1, 3, 1, 1, 2, 2, 3, 3]
def baseStart_7455541 : Nat := 118140960795 + 7455541 * 2 ^ 59
def prefixEnd_7455541 : Nat := 4983230072969 + 3 ^ 40 * 7455541 * 2
def baseEnd_7455541 : Nat := 3828276072302519895250097

theorem tailTrace_7455541 : CollatzResearch.WordTrace tailWord_7455541 prefixEnd_7455541 3828276072302519895250097 := by
  unfold tailWord_7455541
  simp only [CollatzResearch.WordTrace]
  refine ⟨271925919882855736874918477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181283946588570491249945651 271925919882855736874918477)
  ·
    refine ⟨101972219956070901328094429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271925919882855736874918477 101972219956070901328094429)
    ·
      refine ⟨38239582483526587998035411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101972219956070901328094429 38239582483526587998035411)
      ·
        refine ⟨57359373725289881997053117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38239582483526587998035411 57359373725289881997053117)
        ·
          refine ⟨21509765146983705748894919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57359373725289881997053117 21509765146983705748894919)
          ·
            refine ⟨32264647720475558623342379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21509765146983705748894919 32264647720475558623342379)
            ·
              refine ⟨48396971580713337935013569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32264647720475558623342379 48396971580713337935013569)
              ·
                refine ⟨36297728685535003451260177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48396971580713337935013569 36297728685535003451260177)
                ·
                  refine ⟨27223296514151252588445133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36297728685535003451260177 27223296514151252588445133)
                  ·
                    refine ⟨10208736192806719720666925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27223296514151252588445133 10208736192806719720666925)
                    ·
                      refine ⟨3828276072302519895250097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10208736192806719720666925 3828276072302519895250097)
                      ·
                        rfl

theorem cell23_7455541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_7455541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455541 prefixEnd_7455541 := by exact prefixLift 7455541
  have htrace : WordTrace (prefixWord ++ tailWord_7455541) baseStart_7455541 baseEnd_7455541 := by
    simpa [prefixWord, tailWord_7455541, baseEnd_7455541] using wordTrace_append hprefix tailTrace_7455541
  have hstable : (prefixWord ++ tailWord_7455541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455541).length < 2 ^ (prefixWord ++ tailWord_7455541).sum := by decide
  have hdescent : baseEnd_7455541 < baseStart_7455541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455542 : List Nat := [5, 1, 2, 2, 2, 1, 1, 1, 4, 2, 2]
def baseStart_7455542 : Nat := 118140960795 + 7455542 * 2 ^ 59
def prefixEnd_7455542 : Nat := 4983230072969 + 3 ^ 40 * 7455542 * 2
def baseEnd_7455542 : Nat := 3828276585783174391337593

theorem tailTrace_7455542 : CollatzResearch.WordTrace tailWord_7455542 prefixEnd_7455542 3828276585783174391337593 := by
  unfold tailWord_7455542
  simp only [CollatzResearch.WordTrace]
  refine ⟨16995372272240757127856555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181283970903901409363803253 16995372272240757127856555)
  ·
    refine ⟨25493058408361135691784833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16995372272240757127856555 25493058408361135691784833)
    ·
      refine ⟨19119793806270851768838625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25493058408361135691784833 19119793806270851768838625)
      ·
        refine ⟨14339845354703138826628969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19119793806270851768838625 14339845354703138826628969)
        ·
          refine ⟨10754884016027354119971727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14339845354703138826628969 10754884016027354119971727)
          ·
            refine ⟨16132326024041031179957591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10754884016027354119971727 16132326024041031179957591)
            ·
              refine ⟨24198489036061546769936387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16132326024041031179957591 24198489036061546769936387)
              ·
                refine ⟨36297733554092320154904581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24198489036061546769936387 36297733554092320154904581)
                ·
                  refine ⟨6805825041392310029044609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36297733554092320154904581 6805825041392310029044609)
                  ·
                    refine ⟨5104368781044232521783457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6805825041392310029044609 5104368781044232521783457)
                    ·
                      refine ⟨3828276585783174391337593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5104368781044232521783457 3828276585783174391337593)
                      ·
                        rfl

theorem cell23_7455542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_7455542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455542 prefixEnd_7455542 := by exact prefixLift 7455542
  have htrace : WordTrace (prefixWord ++ tailWord_7455542) baseStart_7455542 baseEnd_7455542 := by
    simpa [prefixWord, tailWord_7455542, baseEnd_7455542] using wordTrace_append hprefix tailTrace_7455542
  have hstable : (prefixWord ++ tailWord_7455542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455542).length < 2 ^ (prefixWord ++ tailWord_7455542).sum := by decide
  have hdescent : baseEnd_7455542 < baseStart_7455542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455544 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 4, 5]
def baseStart_7455544 : Nat := 118140960795 + 7455544 * 2 ^ 59
def prefixEnd_7455544 : Nat := 4983230072969 + 3 ^ 40 * 7455544 * 2
def baseEnd_7455544 : Nat := 1276092537581494461170861

theorem tailTrace_7455544 : CollatzResearch.WordTrace tailWord_7455544 prefixEnd_7455544 1276092537581494461170861 := by
  unfold tailWord_7455544
  simp only [CollatzResearch.WordTrace]
  refine ⟨135963014650922434193638843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181284019534563245591518457 135963014650922434193638843)
  ·
    refine ⟨203944521976383651290458265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135963014650922434193638843 203944521976383651290458265)
    ·
      refine ⟨152958391482287738467843699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203944521976383651290458265 152958391482287738467843699)
      ·
        refine ⟨229437587223431607701765549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152958391482287738467843699 229437587223431607701765549)
        ·
          refine ⟨86039095208786852888162081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229437587223431607701765549 86039095208786852888162081)
          ·
            refine ⟨64529321406590139666121561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86039095208786852888162081 64529321406590139666121561)
            ·
              refine ⟨48396991054942604749591171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64529321406590139666121561 48396991054942604749591171)
              ·
                refine ⟨72595486582413907124386757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48396991054942604749591171 72595486582413907124386757)
                ·
                  refine ⟨13611653734202607585822517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72595486582413907124386757 13611653734202607585822517)
                  ·
                    refine ⟨1276092537581494461170861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13611653734202607585822517 1276092537581494461170861)
                    ·
                      rfl

theorem cell23_7455544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 4, 5].length) (baseStart_7455544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455544 prefixEnd_7455544 := by exact prefixLift 7455544
  have htrace : WordTrace (prefixWord ++ tailWord_7455544) baseStart_7455544 baseEnd_7455544 := by
    simpa [prefixWord, tailWord_7455544, baseEnd_7455544] using wordTrace_append hprefix tailTrace_7455544
  have hstable : (prefixWord ++ tailWord_7455544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455544).length < 2 ^ (prefixWord ++ tailWord_7455544).sum := by decide
  have hdescent : baseEnd_7455544 < baseStart_7455544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455601 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 4, 2, 3]
def baseStart_7455601 : Nat := 118140960795 + 7455601 * 2 ^ 59
def prefixEnd_7455601 : Nat := 4983230072969 + 3 ^ 40 * 7455601 * 2
def baseEnd_7455601 : Nat := 3828306881141789660499821

theorem tailTrace_7455601 : CollatzResearch.WordTrace tailWord_7455601 prefixEnd_7455601 3828306881141789660499821 := by
  unfold tailWord_7455601
  simp only [CollatzResearch.WordTrace]
  refine ⟨271928108262638367122102657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181285405508425578081401771 271928108262638367122102657)
  ·
    refine ⟨203946081196978775341576993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271928108262638367122102657 203946081196978775341576993)
    ·
      refine ⟨152959560897734081506182745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203946081196978775341576993 152959560897734081506182745)
      ·
        refine ⟨114719670673300561129637059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152959560897734081506182745 114719670673300561129637059)
        ·
          refine ⟨172079506009950841694455589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114719670673300561129637059 172079506009950841694455589)
          ·
            refine ⟨32264907376865782817710423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172079506009950841694455589 32264907376865782817710423)
            ·
              refine ⟨48397361065298674226565635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32264907376865782817710423 48397361065298674226565635)
              ·
                refine ⟨72596041597948011339848453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48397361065298674226565635 72596041597948011339848453)
                ·
                  refine ⟨13611757799615252126221585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72596041597948011339848453 13611757799615252126221585)
                  ·
                    refine ⟨10208818349711439094666189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13611757799615252126221585 10208818349711439094666189)
                    ·
                      refine ⟨3828306881141789660499821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10208818349711439094666189 3828306881141789660499821)
                      ·
                        rfl

theorem cell23_7455601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_7455601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455601 prefixEnd_7455601 := by exact prefixLift 7455601
  have htrace : WordTrace (prefixWord ++ tailWord_7455601) baseStart_7455601 baseEnd_7455601 := by
    simpa [prefixWord, tailWord_7455601, baseEnd_7455601] using wordTrace_append hprefix tailTrace_7455601
  have hstable : (prefixWord ++ tailWord_7455601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455601).length < 2 ^ (prefixWord ++ tailWord_7455601).sum := by decide
  have hdescent : baseEnd_7455601 < baseStart_7455601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455621 : List Nat := [1, 3, 1, 1, 3, 4, 1, 3, 6]
def baseStart_7455621 : Nat := 118140960795 + 7455621 * 2 ^ 59
def prefixEnd_7455621 : Nat := 4983230072969 + 3 ^ 40 * 7455621 * 2
def baseEnd_7455621 : Nat := 425368572306097731361081

theorem tailTrace_7455621 : CollatzResearch.WordTrace tailWord_7455621 prefixEnd_7455621 425368572306097731361081 := by
  unfold tailWord_7455621
  simp only [CollatzResearch.WordTrace]
  refine ⟨271928837722565910537830717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181285891815043940358553811 271928837722565910537830717)
  ·
    refine ⟨101973314145962216451686519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271928837722565910537830717 101973314145962216451686519)
    ·
      refine ⟨152959971218943324677529779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101973314145962216451686519 152959971218943324677529779)
      ·
        refine ⟨229439956828414987016294669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152959971218943324677529779 229439956828414987016294669)
        ·
          refine ⟨86039983810655620131110501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229439956828414987016294669 86039983810655620131110501)
          ·
            refine ⟨16132496964497928774583219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86039983810655620131110501 16132496964497928774583219)
            ·
              refine ⟨24198745446746893161874829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16132496964497928774583219 24198745446746893161874829)
              ·
                refine ⟨9074529542530084935703061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24198745446746893161874829 9074529542530084935703061)
                ·
                  refine ⟨425368572306097731361081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9074529542530084935703061 425368572306097731361081)
                  ·
                    rfl

theorem cell23_7455621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 6].length) (baseStart_7455621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455621 prefixEnd_7455621 := by exact prefixLift 7455621
  have htrace : WordTrace (prefixWord ++ tailWord_7455621) baseStart_7455621 baseEnd_7455621 := by
    simpa [prefixWord, tailWord_7455621, baseEnd_7455621] using wordTrace_append hprefix tailTrace_7455621
  have hstable : (prefixWord ++ tailWord_7455621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455621).length < 2 ^ (prefixWord ++ tailWord_7455621).sum := by decide
  have hdescent : baseEnd_7455621 < baseStart_7455621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455651 : List Nat := [1, 1, 1, 4, 1, 2, 2, 5, 1, 5]
def baseStart_7455651 : Nat := 118140960795 + 7455651 * 2 ^ 59
def prefixEnd_7455651 : Nat := 4983230072969 + 3 ^ 40 * 7455651 * 2
def baseEnd_7455651 : Nat := 1276110851724838154958197

theorem tailTrace_7455651 : CollatzResearch.WordTrace tailWord_7455651 prefixEnd_7455651 1276110851724838154958197 := by
  unfold tailWord_7455651
  simp only [CollatzResearch.WordTrace]
  refine ⟨271929931912457225661422807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181286621274971483774281871 271929931912457225661422807)
  ·
    refine ⟨407894897868685838492134211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271929931912457225661422807 407894897868685838492134211)
    ·
      refine ⟨611842346803028757738201317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407894897868685838492134211 611842346803028757738201317)
      ·
        refine ⟨114720440025567892075912747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 611842346803028757738201317 114720440025567892075912747)
        ·
          refine ⟨172080660038351838113869121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114720440025567892075912747 172080660038351838113869121)
          ·
            refine ⟨129060495028763878585401841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172080660038351838113869121 129060495028763878585401841)
            ·
              refine ⟨96795371271572908939051381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129060495028763878585401841 96795371271572908939051381)
              ·
                refine ⟨9074566056709960213036067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96795371271572908939051381 9074566056709960213036067)
                ·
                  refine ⟨13611849085064940319554101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9074566056709960213036067 13611849085064940319554101)
                  ·
                    refine ⟨1276110851724838154958197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13611849085064940319554101 1276110851724838154958197)
                    ·
                      rfl

theorem cell23_7455651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 5].length) (baseStart_7455651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455651 prefixEnd_7455651 := by exact prefixLift 7455651
  have htrace : WordTrace (prefixWord ++ tailWord_7455651) baseStart_7455651 baseEnd_7455651 := by
    simpa [prefixWord, tailWord_7455651, baseEnd_7455651] using wordTrace_append hprefix tailTrace_7455651
  have hstable : (prefixWord ++ tailWord_7455651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455651).length < 2 ^ (prefixWord ++ tailWord_7455651).sum := by decide
  have hdescent : baseEnd_7455651 < baseStart_7455651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455671 : List Nat := [1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 4]
def baseStart_7455671 : Nat := 118140960795 + 7455671 * 2 ^ 59
def prefixEnd_7455671 : Nat := 4983230072969 + 3 ^ 40 * 7455671 * 2
def baseEnd_7455671 : Nat := 3828342824787604386624499

theorem tailTrace_7455671 : CollatzResearch.WordTrace tailWord_7455671 prefixEnd_7455671 3828342824787604386624499 := by
  unfold tailWord_7455671
  simp only [CollatzResearch.WordTrace]
  refine ⟨271930661372384769077150867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181287107581589846051433911 271930661372384769077150867)
  ·
    refine ⟨407895992058577153615726301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271930661372384769077150867 407895992058577153615726301)
    ·
      refine ⟨152960997021966432605897363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407895992058577153615726301 152960997021966432605897363)
      ·
        refine ⟨229441495532949648908846045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152960997021966432605897363 229441495532949648908846045)
        ·
          refine ⟨86040560824856118340817267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229441495532949648908846045 86040560824856118340817267)
          ·
            refine ⟨129060841237284177511225901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86040560824856118340817267 129060841237284177511225901)
            ·
              refine ⟨48397815463981566566709713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129060841237284177511225901 48397815463981566566709713)
              ·
                refine ⟨36298361597986174925032285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48397815463981566566709713 36298361597986174925032285)
                ·
                  refine ⟨13611885599244815596887107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36298361597986174925032285 13611885599244815596887107)
                  ·
                    refine ⟨20417828398867223395330661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13611885599244815596887107 20417828398867223395330661)
                    ·
                      refine ⟨3828342824787604386624499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20417828398867223395330661 3828342824787604386624499)
                      ·
                        rfl

theorem cell23_7455671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_7455671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455671 prefixEnd_7455671 := by exact prefixLift 7455671
  have htrace : WordTrace (prefixWord ++ tailWord_7455671) baseStart_7455671 baseEnd_7455671 := by
    simpa [prefixWord, tailWord_7455671, baseEnd_7455671] using wordTrace_append hprefix tailTrace_7455671
  have hstable : (prefixWord ++ tailWord_7455671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455671).length < 2 ^ (prefixWord ++ tailWord_7455671).sum := by decide
  have hdescent : baseEnd_7455671 < baseStart_7455671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455698 : List Nat := [3, 2, 2, 3, 1, 1, 2, 2, 1, 6]
def baseStart_7455698 : Nat := 118140960795 + 7455698 * 2 ^ 59
def prefixEnd_7455698 : Nat := 4983230072969 + 3 ^ 40 * 7455698 * 2
def baseEnd_7455698 : Nat := 1276118896255091926995625

theorem tailTrace_7455698 : CollatzResearch.WordTrace tailWord_7455698 prefixEnd_7455698 1276118896255091926995625 := by
  unfold tailWord_7455698
  simp only [CollatzResearch.WordTrace]
  refine ⟨67982911535821738172095937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181287764095524635125589165 67982911535821738172095937)
  ·
    refine ⟨50987183651866303629071953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67982911535821738172095937 50987183651866303629071953)
    ·
      refine ⟨38240387738899727721803965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50987183651866303629071953 38240387738899727721803965)
      ·
        refine ⟨14340145402087397895676487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38240387738899727721803965 14340145402087397895676487)
        ·
          refine ⟨21510218103131096843514731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14340145402087397895676487 21510218103131096843514731)
          ·
            refine ⟨32265327154696645265272097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21510218103131096843514731 32265327154696645265272097)
            ·
              refine ⟨24198995366022483948954073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32265327154696645265272097 24198995366022483948954073)
              ·
                refine ⟨18149246524516862961715555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24198995366022483948954073 18149246524516862961715555)
                ·
                  refine ⟨27223869786775294442573333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18149246524516862961715555 27223869786775294442573333)
                  ·
                    refine ⟨1276118896255091926995625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27223869786775294442573333 1276118896255091926995625)
                    ·
                      rfl

theorem cell23_7455698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_7455698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455698 prefixEnd_7455698 := by exact prefixLift 7455698
  have htrace : WordTrace (prefixWord ++ tailWord_7455698) baseStart_7455698 baseEnd_7455698 := by
    simpa [prefixWord, tailWord_7455698, baseEnd_7455698] using wordTrace_append hprefix tailTrace_7455698
  have hstable : (prefixWord ++ tailWord_7455698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455698).length < 2 ^ (prefixWord ++ tailWord_7455698).sum := by decide
  have hdescent : baseEnd_7455698 < baseStart_7455698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455702 : List Nat := [5, 2, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_7455702 : Nat := 118140960795 + 7455702 * 2 ^ 59
def prefixEnd_7455702 : Nat := 4983230072969 + 3 ^ 40 * 7455702 * 2
def baseEnd_7455702 : Nat := 1276119580895964588445619

theorem tailTrace_7455702 : CollatzResearch.WordTrace tailWord_7455702 prefixEnd_7455702 1276119580895964588445619 := by
  unfold tailWord_7455702
  simp only [CollatzResearch.WordTrace]
  refine ⟨16995737002204528835720585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181287861356848307581019573 16995737002204528835720585)
  ·
    refine ⟨12746802751653396626790439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16995737002204528835720585 12746802751653396626790439)
    ·
      refine ⟨19120204127480094940185659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12746802751653396626790439 19120204127480094940185659)
      ·
        refine ⟨28680306191220142410278489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19120204127480094940185659 28680306191220142410278489)
        ·
          refine ⟨21510229643415106807708867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28680306191220142410278489 21510229643415106807708867)
          ·
            refine ⟨32265344465122660211563301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21510229643415106807708867 32265344465122660211563301)
            ·
              refine ⟨6049752087210498789668119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32265344465122660211563301 6049752087210498789668119)
              ·
                refine ⟨9074628130815748184502179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6049752087210498789668119 9074628130815748184502179)
                ·
                  refine ⟨13611942196223622276753269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9074628130815748184502179 13611942196223622276753269)
                  ·
                    refine ⟨1276119580895964588445619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13611942196223622276753269 1276119580895964588445619)
                    ·
                      rfl

theorem cell23_7455702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_7455702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455702 prefixEnd_7455702 := by exact prefixLift 7455702
  have htrace : WordTrace (prefixWord ++ tailWord_7455702) baseStart_7455702 baseEnd_7455702 := by
    simpa [prefixWord, tailWord_7455702, baseEnd_7455702] using wordTrace_append hprefix tailTrace_7455702
  have hstable : (prefixWord ++ tailWord_7455702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455702).length < 2 ^ (prefixWord ++ tailWord_7455702).sum := by decide
  have hdescent : baseEnd_7455702 < baseStart_7455702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455705 : List Nat := [1, 2, 1, 2, 5, 1, 4, 1, 1, 1, 4]
def baseStart_7455705 : Nat := 118140960795 + 7455705 * 2 ^ 59
def prefixEnd_7455705 : Nat := 4983230072969 + 3 ^ 40 * 7455705 * 2
def baseEnd_7455705 : Nat := 3828360283129857253599343

theorem tailTrace_7455705 : CollatzResearch.WordTrace tailWord_7455705 prefixEnd_7455705 3828360283129857253599343 := by
  unfold tailWord_7455705
  simp only [CollatzResearch.WordTrace]
  refine ⟨271931901454261592883888569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181287934302841061922592379 271931901454261592883888569)
  ·
    refine ⟨203948926090696194662916427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271931901454261592883888569 203948926090696194662916427)
    ·
      refine ⟨305923389136044291994374641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203948926090696194662916427 305923389136044291994374641)
      ·
        refine ⟨229442541852033218995780981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305923389136044291994374641 229442541852033218995780981)
        ·
          refine ⟨21510238298628114280854467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 229442541852033218995780981 21510238298628114280854467)
          ·
            refine ⟨32265357447942171421281701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21510238298628114280854467 32265357447942171421281701)
            ·
              refine ⟨6049754521489157141490319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32265357447942171421281701 6049754521489157141490319)
              ·
                refine ⟨9074631782233735712235479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6049754521489157141490319 9074631782233735712235479)
                ·
                  refine ⟨13611947673350603568353219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9074631782233735712235479 13611947673350603568353219)
                  ·
                    refine ⟨20417921510025905352529829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13611947673350603568353219 20417921510025905352529829)
                    ·
                      refine ⟨3828360283129857253599343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20417921510025905352529829 3828360283129857253599343)
                      ·
                        rfl

theorem cell23_7455705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 1, 1, 4].length) (baseStart_7455705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455705 prefixEnd_7455705 := by exact prefixLift 7455705
  have htrace : WordTrace (prefixWord ++ tailWord_7455705) baseStart_7455705 baseEnd_7455705 := by
    simpa [prefixWord, tailWord_7455705, baseEnd_7455705] using wordTrace_append hprefix tailTrace_7455705
  have hstable : (prefixWord ++ tailWord_7455705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455705).length < 2 ^ (prefixWord ++ tailWord_7455705).sum := by decide
  have hdescent : baseEnd_7455705 < baseStart_7455705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455711 : List Nat := [1, 1, 2, 3, 5, 1, 10]
def baseStart_7455711 : Nat := 118140960795 + 7455711 * 2 ^ 59
def prefixEnd_7455711 : Nat := 4983230072969 + 3 ^ 40 * 7455711 * 2
def baseEnd_7455711 : Nat := 47263745234738076915115

theorem tailTrace_7455711 : CollatzResearch.WordTrace tailWord_7455711 prefixEnd_7455711 47263745234738076915115 := by
  unfold tailWord_7455711
  simp only [CollatzResearch.WordTrace]
  refine ⟨271932120292239855908606987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181288080194826570605737991 271932120292239855908606987)
  ·
    refine ⟨407898180438359783862910481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271932120292239855908606987 407898180438359783862910481)
    ·
      refine ⟨305923635328769837897182861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407898180438359783862910481 305923635328769837897182861)
      ·
        refine ⟨114721363248288689211443573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305923635328769837897182861 114721363248288689211443573)
        ·
          refine ⟨10755127804527064613572835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114721363248288689211443573 10755127804527064613572835)
          ·
            refine ⟨16132691706790596920359253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10755127804527064613572835 16132691706790596920359253)
            ·
              refine ⟨47263745234738076915115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16132691706790596920359253 47263745234738076915115)
              ·
                rfl

theorem cell23_7455711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 10].length) (baseStart_7455711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455711 prefixEnd_7455711 := by exact prefixLift 7455711
  have htrace : WordTrace (prefixWord ++ tailWord_7455711) baseStart_7455711 baseEnd_7455711 := by
    simpa [prefixWord, tailWord_7455711, baseEnd_7455711] using wordTrace_append hprefix tailTrace_7455711
  have hstable : (prefixWord ++ tailWord_7455711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455711).length < 2 ^ (prefixWord ++ tailWord_7455711).sum := by decide
  have hdescent : baseEnd_7455711 < baseStart_7455711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455722 : List Nat := [3, 1, 3, 1, 2, 3, 2, 1, 3, 2, 2]
def baseStart_7455722 : Nat := 118140960795 + 7455722 * 2 ^ 59
def prefixEnd_7455722 : Nat := 4983230072969 + 3 ^ 40 * 7455722 * 2
def baseEnd_7455722 : Nat := 3828369012300983687086765

theorem tailTrace_7455722 : CollatzResearch.WordTrace tailWord_7455722 prefixEnd_7455722 3828369012300983687086765 := by
  unfold tailWord_7455722
  simp only [CollatzResearch.WordTrace]
  refine ⟨67983130373800001196814355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181288347663466669858171613 67983130373800001196814355)
  ·
    refine ⟨101974695560700001795221533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67983130373800001196814355 101974695560700001795221533)
    ·
      refine ⟨38240510835262500673208075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101974695560700001795221533 38240510835262500673208075)
      ·
        refine ⟨57360766252893751009812113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38240510835262500673208075 57360766252893751009812113)
        ·
          refine ⟨43020574689670313257359085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57360766252893751009812113 43020574689670313257359085)
          ·
            refine ⟨16132715508626367471509657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43020574689670313257359085 16132715508626367471509657)
            ·
              refine ⟨12099536631469775603632243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16132715508626367471509657 12099536631469775603632243)
              ·
                refine ⟨18149304947204663405448365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12099536631469775603632243 18149304947204663405448365)
                ·
                  refine ⟨6805989355201748777043137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18149304947204663405448365 6805989355201748777043137)
                  ·
                    refine ⟨5104492016401311582782353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6805989355201748777043137 5104492016401311582782353)
                    ·
                      refine ⟨3828369012300983687086765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5104492016401311582782353 3828369012300983687086765)
                      ·
                        rfl

theorem cell23_7455722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_7455722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455722 prefixEnd_7455722 := by exact prefixLift 7455722
  have htrace : WordTrace (prefixWord ++ tailWord_7455722) baseStart_7455722 baseEnd_7455722 := by
    simpa [prefixWord, tailWord_7455722, baseEnd_7455722] using wordTrace_append hprefix tailTrace_7455722
  have hstable : (prefixWord ++ tailWord_7455722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455722).length < 2 ^ (prefixWord ++ tailWord_7455722).sum := by decide
  have hdescent : baseEnd_7455722 < baseStart_7455722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455751 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 5]
def baseStart_7455751 : Nat := 118140960795 + 7455751 * 2 ^ 59
def prefixEnd_7455751 : Nat := 4983230072969 + 3 ^ 40 * 7455751 * 2
def baseEnd_7455751 : Nat := 3828383903239964073624131

theorem tailTrace_7455751 : CollatzResearch.WordTrace tailWord_7455751 prefixEnd_7455751 3828383903239964073624131 := by
  unfold tailWord_7455751
  simp only [CollatzResearch.WordTrace]
  refine ⟨271933579212094942740063107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181289052808063295160042071 271933579212094942740063107)
  ·
    refine ⟨407900368818142414110094661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271933579212094942740063107 407900368818142414110094661)
    ·
      refine ⟨76481319153401702645642749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 407900368818142414110094661 76481319153401702645642749)
      ·
        refine ⟨28680494682525638492116031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76481319153401702645642749 28680494682525638492116031)
        ·
          refine ⟨43020742023788457738174047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28680494682525638492116031 43020742023788457738174047)
          ·
            refine ⟨64531113035682686607261071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43020742023788457738174047 64531113035682686607261071)
            ·
              refine ⟨96796669553524029910891607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64531113035682686607261071 96796669553524029910891607)
              ·
                refine ⟨145195004330286044866337411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96796669553524029910891607 145195004330286044866337411)
                ·
                  refine ⟨217792506495429067299506117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145195004330286044866337411 217792506495429067299506117)
                  ·
                    refine ⟨40836094967892950118657397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 217792506495429067299506117 40836094967892950118657397)
                    ·
                      refine ⟨3828383903239964073624131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40836094967892950118657397 3828383903239964073624131)
                      ·
                        rfl

theorem cell23_7455751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_7455751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455751 prefixEnd_7455751 := by exact prefixLift 7455751
  have htrace : WordTrace (prefixWord ++ tailWord_7455751) baseStart_7455751 baseEnd_7455751 := by
    simpa [prefixWord, tailWord_7455751, baseEnd_7455751] using wordTrace_append hprefix tailTrace_7455751
  have hstable : (prefixWord ++ tailWord_7455751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455751).length < 2 ^ (prefixWord ++ tailWord_7455751).sum := by decide
  have hdescent : baseEnd_7455751 < baseStart_7455751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455762 : List Nat := [3, 2, 5, 1, 1, 2, 9]
def baseStart_7455762 : Nat := 118140960795 + 7455762 * 2 ^ 59
def prefixEnd_7455762 : Nat := 4983230072969 + 3 ^ 40 * 7455762 * 2
def baseEnd_7455762 : Nat := 47264068537372389266501

theorem tailTrace_7455762 : CollatzResearch.WordTrace tailWord_7455762 prefixEnd_7455762 47264068537372389266501 := by
  unfold tailWord_7455762
  simp only [CollatzResearch.WordTrace]
  refine ⟨67983495103763772904678385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181289320276703394412475693 67983495103763772904678385)
  ·
    refine ⟨50987621327822829678508789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67983495103763772904678385 50987621327822829678508789)
    ·
      refine ⟨4780089499483390282360199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50987621327822829678508789 4780089499483390282360199)
      ·
        refine ⟨7170134249225085423540299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4780089499483390282360199 7170134249225085423540299)
        ·
          refine ⟨10755201373837628135310449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7170134249225085423540299 10755201373837628135310449)
          ·
            refine ⟨8066401030378221101482837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10755201373837628135310449 8066401030378221101482837)
            ·
              refine ⟨47264068537372389266501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8066401030378221101482837 47264068537372389266501)
              ·
                rfl

theorem cell23_7455762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 9].length) (baseStart_7455762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455762 prefixEnd_7455762 := by exact prefixLift 7455762
  have htrace : WordTrace (prefixWord ++ tailWord_7455762) baseStart_7455762 baseEnd_7455762 := by
    simpa [prefixWord, tailWord_7455762, baseEnd_7455762] using wordTrace_append hprefix tailTrace_7455762
  have hstable : (prefixWord ++ tailWord_7455762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455762).length < 2 ^ (prefixWord ++ tailWord_7455762).sum := by decide
  have hdescent : baseEnd_7455762 < baseStart_7455762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455781 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 1, 3, 5]
def baseStart_7455781 : Nat := 118140960795 + 7455781 * 2 ^ 59
def prefixEnd_7455781 : Nat := 4983230072969 + 3 ^ 40 * 7455781 * 2
def baseEnd_7455781 : Nat := 3828399307659598956248993

theorem tailTrace_7455781 : CollatzResearch.WordTrace tailWord_7455781 prefixEnd_7455781 3828399307659598956248993 := by
  unfold tailWord_7455781
  simp only [CollatzResearch.WordTrace]
  refine ⟨271934673401986257863655197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181289782267990838575770131 271934673401986257863655197)
  ·
    refine ⟨101975502525744846698870699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271934673401986257863655197 101975502525744846698870699)
    ·
      refine ⟨152963253788617270048306049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101975502525744846698870699 152963253788617270048306049)
      ·
        refine ⟨114722440341462952536229537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152963253788617270048306049 114722440341462952536229537)
        ·
          refine ⟨86041830256097214402172153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114722440341462952536229537 86041830256097214402172153)
          ·
            refine ⟨64531372692072910801629115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86041830256097214402172153 64531372692072910801629115)
            ·
              refine ⟨96797059038109366202443673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64531372692072910801629115 96797059038109366202443673)
              ·
                refine ⟨72597794278582024651832755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96797059038109366202443673 72597794278582024651832755)
                ·
                  refine ⟨108896691417873036977749133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72597794278582024651832755 108896691417873036977749133)
                  ·
                    refine ⟨40836259281702388866655925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108896691417873036977749133 40836259281702388866655925)
                    ·
                      refine ⟨3828399307659598956248993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40836259281702388866655925 3828399307659598956248993)
                      ·
                        rfl

theorem cell23_7455781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_7455781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455781 prefixEnd_7455781 := by exact prefixLift 7455781
  have htrace : WordTrace (prefixWord ++ tailWord_7455781) baseStart_7455781 baseEnd_7455781 := by
    simpa [prefixWord, tailWord_7455781, baseEnd_7455781] using wordTrace_append hprefix tailTrace_7455781
  have hstable : (prefixWord ++ tailWord_7455781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455781).length < 2 ^ (prefixWord ++ tailWord_7455781).sum := by decide
  have hdescent : baseEnd_7455781 < baseStart_7455781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455791 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 4]
def baseStart_7455791 : Nat := 118140960795 + 7455791 * 2 ^ 59
def prefixEnd_7455791 : Nat := 4983230072969 + 3 ^ 40 * 7455791 * 2
def baseEnd_7455791 : Nat := 3828404442466143917123947

theorem tailTrace_7455791 : CollatzResearch.WordTrace tailWord_7455791 prefixEnd_7455791 3828404442466143917123947 := by
  unfold tailWord_7455791
  simp only [CollatzResearch.WordTrace]
  refine ⟨271935038131950029571519227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181290025421300019714346151 271935038131950029571519227)
  ·
    refine ⟨407902557197925044357278841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271935038131950029571519227 407902557197925044357278841)
    ·
      refine ⟨305926917898443783267959131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407902557197925044357278841 305926917898443783267959131)
      ·
        refine ⟨458890376847665674901938697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305926917898443783267959131 458890376847665674901938697)
        ·
          refine ⟨344167782635749256176454023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 458890376847665674901938697 344167782635749256176454023)
          ·
            refine ⟨516251673953623884264681035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344167782635749256176454023 516251673953623884264681035)
            ·
              refine ⟨774377510930435826397021553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516251673953623884264681035 774377510930435826397021553)
              ·
                refine ⟨580783133197826869797766165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 774377510930435826397021553 580783133197826869797766165)
                ·
                  refine ⟨27224209368648134521770289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 580783133197826869797766165 27224209368648134521770289)
                  ·
                    refine ⟨20418157026486100891327717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27224209368648134521770289 20418157026486100891327717)
                    ·
                      refine ⟨3828404442466143917123947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20418157026486100891327717 3828404442466143917123947)
                      ·
                        rfl

theorem cell23_7455791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 4].length) (baseStart_7455791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455791 prefixEnd_7455791 := by exact prefixLift 7455791
  have htrace : WordTrace (prefixWord ++ tailWord_7455791) baseStart_7455791 baseEnd_7455791 := by
    simpa [prefixWord, tailWord_7455791, baseEnd_7455791] using wordTrace_append hprefix tailTrace_7455791
  have hstable : (prefixWord ++ tailWord_7455791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455791).length < 2 ^ (prefixWord ++ tailWord_7455791).sum := by decide
  have hdescent : baseEnd_7455791 < baseStart_7455791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455831 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 3, 7]
def baseStart_7455831 : Nat := 118140960795 + 7455831 * 2 ^ 59
def prefixEnd_7455831 : Nat := 4983230072969 + 3 ^ 40 * 7455831 * 2
def baseEnd_7455831 : Nat := 1276141660564107920207921

theorem tailTrace_7455831 : CollatzResearch.WordTrace tailWord_7455831 prefixEnd_7455831 1276141660564107920207921 := by
  unfold tailWord_7455831
  simp only [CollatzResearch.WordTrace]
  refine ⟨271936497051805116402975347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181290998034536744268650231 271936497051805116402975347)
  ·
    refine ⟨407904745577707674604463021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271936497051805116402975347 407904745577707674604463021)
    ·
      refine ⟨152964279591640377976673633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407904745577707674604463021 152964279591640377976673633)
      ·
        refine ⟨114723209693730283482505225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152964279591640377976673633 114723209693730283482505225)
        ·
          refine ⟨86042407270297712611878919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114723209693730283482505225 86042407270297712611878919)
          ·
            refine ⟨129063610905446568917818379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86042407270297712611878919 129063610905446568917818379)
            ·
              refine ⟨193595416358169853376727569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129063610905446568917818379 193595416358169853376727569)
              ·
                refine ⟨145196562268627390032545677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193595416358169853376727569 145196562268627390032545677)
                ·
                  refine ⟨54448710850735271262204629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145196562268627390032545677 54448710850735271262204629)
                  ·
                    refine ⟨1276141660564107920207921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54448710850735271262204629 1276141660564107920207921)
                    ·
                      rfl

theorem cell23_7455831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_7455831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455831 prefixEnd_7455831 := by exact prefixLift 7455831
  have htrace : WordTrace (prefixWord ++ tailWord_7455831) baseStart_7455831 baseEnd_7455831 := by
    simpa [prefixWord, tailWord_7455831, baseEnd_7455831] using wordTrace_append hprefix tailTrace_7455831
  have hstable : (prefixWord ++ tailWord_7455831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455831).length < 2 ^ (prefixWord ++ tailWord_7455831).sum := by decide
  have hdescent : baseEnd_7455831 < baseStart_7455831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455868 : List Nat := [2, 2, 2, 1, 1, 3, 3, 1, 1, 3, 4]
def baseStart_7455868 : Nat := 118140960795 + 7455868 * 2 ^ 59
def prefixEnd_7455868 : Nat := 4983230072969 + 3 ^ 40 * 7455868 * 2
def baseEnd_7455868 : Nat := 3828443980476540115861093

theorem tailTrace_7455868 : CollatzResearch.WordTrace tailWord_7455868 prefixEnd_7455868 3828443980476540115861093 := by
  unfold tailWord_7455868
  simp only [CollatzResearch.WordTrace]
  refine ⟨135968923276335535861036129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181291897701780714481381505 135968923276335535861036129)
  ·
    refine ⟨101976692457251651895777097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135968923276335535861036129 101976692457251651895777097)
    ·
      refine ⟨76482519342938738921832823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101976692457251651895777097 76482519342938738921832823)
      ·
        refine ⟨114723779014408108382749235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76482519342938738921832823 114723779014408108382749235)
        ·
          refine ⟨172085668521612162574123853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114723779014408108382749235 172085668521612162574123853)
          ·
            refine ⟨64532125695604560965296445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172085668521612162574123853 64532125695604560965296445)
            ·
              refine ⟨24199547135851710361986167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64532125695604560965296445 24199547135851710361986167)
              ·
                refine ⟨36299320703777565542979251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24199547135851710361986167 36299320703777565542979251)
                ·
                  refine ⟨54448981055666348314468877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36299320703777565542979251 54448981055666348314468877)
                  ·
                    refine ⟨20418367895874880617925829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54448981055666348314468877 20418367895874880617925829)
                    ·
                      refine ⟨3828443980476540115861093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20418367895874880617925829 3828443980476540115861093)
                      ·
                        rfl

theorem cell23_7455868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_7455868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455868 prefixEnd_7455868 := by exact prefixLift 7455868
  have htrace : WordTrace (prefixWord ++ tailWord_7455868) baseStart_7455868 baseEnd_7455868 := by
    simpa [prefixWord, tailWord_7455868, baseEnd_7455868] using wordTrace_append hprefix tailTrace_7455868
  have hstable : (prefixWord ++ tailWord_7455868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455868).length < 2 ^ (prefixWord ++ tailWord_7455868).sum := by decide
  have hdescent : baseEnd_7455868 < baseStart_7455868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455895 : List Nat := [1, 1, 3, 3, 3, 1, 1, 3, 3, 4]
def baseStart_7455895 : Nat := 118140960795 + 7455895 * 2 ^ 59
def prefixEnd_7455895 : Nat := 4983230072969 + 3 ^ 40 * 7455895 * 2
def baseEnd_7455895 : Nat := 1276152614818070503407823

theorem tailTrace_7455895 : CollatzResearch.WordTrace tailWord_7455895 prefixEnd_7455895 1276152614818070503407823 := by
  unfold tailWord_7455895
  simp only [CollatzResearch.WordTrace]
  refine ⟨271938831323573255333305139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181292554215715503555536759 271938831323573255333305139)
  ·
    refine ⟨407908246985359882999957709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271938831323573255333305139 407908246985359882999957709)
    ·
      refine ⟨152965592619509956124984141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407908246985359882999957709 152965592619509956124984141)
      ·
        refine ⟨57362097232316233546869053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152965592619509956124984141 57362097232316233546869053)
        ·
          refine ⟨21510786462118587580075895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57362097232316233546869053 21510786462118587580075895)
          ·
            refine ⟨32266179693177881370113843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21510786462118587580075895 32266179693177881370113843)
            ·
              refine ⟨48399269539766822055170765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32266179693177881370113843 48399269539766822055170765)
              ·
                refine ⟨18149726077412558270689037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48399269539766822055170765 18149726077412558270689037)
                ·
                  refine ⟨6806147279029709351508389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18149726077412558270689037 6806147279029709351508389)
                  ·
                    refine ⟨1276152614818070503407823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6806147279029709351508389 1276152614818070503407823)
                    ·
                      rfl

theorem cell23_7455895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3, 4].length) (baseStart_7455895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455895 prefixEnd_7455895 := by exact prefixLift 7455895
  have htrace : WordTrace (prefixWord ++ tailWord_7455895) baseStart_7455895 baseEnd_7455895 := by
    simpa [prefixWord, tailWord_7455895, baseEnd_7455895] using wordTrace_append hprefix tailTrace_7455895
  have hstable : (prefixWord ++ tailWord_7455895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455895).length < 2 ^ (prefixWord ++ tailWord_7455895).sum := by decide
  have hdescent : baseEnd_7455895 < baseStart_7455895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455929 : List Nat := [1, 2, 1, 4, 1, 5, 1, 3, 1, 4]
def baseStart_7455929 : Nat := 118140960795 + 7455929 * 2 ^ 59
def prefixEnd_7455929 : Nat := 4983230072969 + 3 ^ 40 * 7455929 * 2
def baseEnd_7455929 : Nat := 1276158434265488125732771

theorem tailTrace_7455929 : CollatzResearch.WordTrace tailWord_7455929 prefixEnd_7455929 1276158434265488125732771 := by
  unfold tailWord_7455929
  simp only [CollatzResearch.WordTrace]
  refine ⟨271940071405450079140042841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181293380936966719426695227 271940071405450079140042841)
  ·
    refine ⟨203955053554087559355032131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271940071405450079140042841 203955053554087559355032131)
    ·
      refine ⟨305932580331131339032548197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203955053554087559355032131 305932580331131339032548197)
      ·
        refine ⟨57362358812087126068602787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305932580331131339032548197 57362358812087126068602787)
        ·
          refine ⟨86043538218130689102904181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57362358812087126068602787 86043538218130689102904181)
          ·
            refine ⟨8066581707949752103397267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86043538218130689102904181 8066581707949752103397267)
            ·
              refine ⟨12099872561924628155095901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8066581707949752103397267 12099872561924628155095901)
              ·
                refine ⟨4537452210721735558160963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12099872561924628155095901 4537452210721735558160963)
                ·
                  refine ⟨6806178316082603337241445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4537452210721735558160963 6806178316082603337241445)
                  ·
                    refine ⟨1276158434265488125732771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6806178316082603337241445 1276158434265488125732771)
                    ·
                      rfl

theorem cell23_7455929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3, 1, 4].length) (baseStart_7455929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455929 prefixEnd_7455929 := by exact prefixLift 7455929
  have htrace : WordTrace (prefixWord ++ tailWord_7455929) baseStart_7455929 baseEnd_7455929 := by
    simpa [prefixWord, tailWord_7455929, baseEnd_7455929] using wordTrace_append hprefix tailTrace_7455929
  have hstable : (prefixWord ++ tailWord_7455929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455929).length < 2 ^ (prefixWord ++ tailWord_7455929).sum := by decide
  have hdescent : baseEnd_7455929 < baseStart_7455929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7455935 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 5, 1, 3]
def baseStart_7455935 : Nat := 118140960795 + 7455935 * 2 ^ 59
def prefixEnd_7455935 : Nat := 4983230072969 + 3 ^ 40 * 7455935 * 2
def baseEnd_7455935 : Nat := 3828478383680391353723285

theorem tailTrace_7455935 : CollatzResearch.WordTrace tailWord_7455935 prefixEnd_7455935 3828478383680391353723285 := by
  unfold tailWord_7455935
  simp only [CollatzResearch.WordTrace]
  refine ⟨271940290243428342164761259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181293526828952228109840839 271940290243428342164761259)
  ·
    refine ⟨407910435365142513247141889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271940290243428342164761259 407910435365142513247141889)
    ·
      refine ⟨305932826523856884935356417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407910435365142513247141889 305932826523856884935356417)
      ·
        refine ⟨229449619892892663701517313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305932826523856884935356417 229449619892892663701517313)
        ·
          refine ⟨172087214919669497776137985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229449619892892663701517313 172087214919669497776137985)
          ·
            refine ⟨129065411189752123332103489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172087214919669497776137985 129065411189752123332103489)
            ·
              refine ⟨96799058392314092499077617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129065411189752123332103489 96799058392314092499077617)
              ·
                refine ⟨72599293794235569374308213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96799058392314092499077617 72599293794235569374308213)
                ·
                  refine ⟨6806183793209584628841395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72599293794235569374308213 6806183793209584628841395)
                  ·
                    refine ⟨10209275689814376943262093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6806183793209584628841395 10209275689814376943262093)
                    ·
                      refine ⟨3828478383680391353723285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10209275689814376943262093 3828478383680391353723285)
                      ·
                        rfl

theorem cell23_7455935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5, 1, 3].length) (baseStart_7455935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7455935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7455935 prefixEnd_7455935 := by exact prefixLift 7455935
  have htrace : WordTrace (prefixWord ++ tailWord_7455935) baseStart_7455935 baseEnd_7455935 := by
    simpa [prefixWord, tailWord_7455935, baseEnd_7455935] using wordTrace_append hprefix tailTrace_7455935
  have hstable : (prefixWord ++ tailWord_7455935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7455935).length < 2 ^ (prefixWord ++ tailWord_7455935).sum := by decide
  have hdescent : baseEnd_7455935 < baseStart_7455935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7455935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456030 : List Nat := [4, 3, 2, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_7456030 : Nat := 118140960795 + 7456030 * 2 ^ 59
def prefixEnd_7456030 : Nat := 4983230072969 + 3 ^ 40 * 7456030 * 2
def baseEnd_7456030 : Nat := 3828527164342568482035349

theorem tailTrace_7456030 : CollatzResearch.WordTrace tailWord_7456030 prefixEnd_7456030 3828527164342568482035349 := by
  unfold tailWord_7456030
  simp only [CollatzResearch.WordTrace]
  refine ⟨33992969397260521673683693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181295836785389448926313029 33992969397260521673683693)
  ·
    refine ⟨12747363523972695627631385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33992969397260521673683693 12747363523972695627631385)
    ·
      refine ⟨9560522642979521720723539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12747363523972695627631385 9560522642979521720723539)
      ·
        refine ⟨14340783964469282581085309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9560522642979521720723539 14340783964469282581085309)
        ·
          refine ⟨5377793986675980967906991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14340783964469282581085309 5377793986675980967906991)
          ·
            refine ⟨8066690980013971451860487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5377793986675980967906991 8066690980013971451860487)
            ·
              refine ⟨12100036470020957177790731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8066690980013971451860487 12100036470020957177790731)
              ·
                refine ⟨18150054705031435766686097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12100036470020957177790731 18150054705031435766686097)
                ·
                  refine ⟨13612541028773576825014573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18150054705031435766686097 13612541028773576825014573)
                  ·
                    refine ⟨5104702885790091309380465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13612541028773576825014573 5104702885790091309380465)
                    ·
                      refine ⟨3828527164342568482035349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5104702885790091309380465 3828527164342568482035349)
                      ·
                        rfl

theorem cell23_7456030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_7456030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456030 prefixEnd_7456030 := by exact prefixLift 7456030
  have htrace : WordTrace (prefixWord ++ tailWord_7456030) baseStart_7456030 baseEnd_7456030 := by
    simpa [prefixWord, tailWord_7456030, baseEnd_7456030] using wordTrace_append hprefix tailTrace_7456030
  have hstable : (prefixWord ++ tailWord_7456030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456030).length < 2 ^ (prefixWord ++ tailWord_7456030).sum := by decide
  have hdescent : baseEnd_7456030 < baseStart_7456030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456032 : List Nat := [2, 1, 1, 5, 3, 1, 3, 7]
def baseStart_7456032 : Nat := 118140960795 + 7456032 * 2 ^ 59
def prefixEnd_7456032 : Nat := 4983230072969 + 3 ^ 40 * 7456032 * 2
def baseEnd_7456032 : Nat := 141797340418662128674457

theorem tailTrace_7456032 : CollatzResearch.WordTrace tailWord_7456032 prefixEnd_7456032 141797340418662128674457 := by
  unfold tailWord_7456032
  simp only [CollatzResearch.WordTrace]
  refine ⟨135971914062038463865521175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181295885416051285154028233 135971914062038463865521175)
  ·
    refine ⟨203957871093057695798281763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135971914062038463865521175 203957871093057695798281763)
    ·
      refine ⟨305936806639586543697422645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203957871093057695798281763 305936806639586543697422645)
      ·
        refine ⟨28681575622461238471633373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 305936806639586543697422645 28681575622461238471633373)
        ·
          refine ⟨10755590858422964426862515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28681575622461238471633373 10755590858422964426862515)
          ·
            refine ⟨16133386287634446640293773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10755590858422964426862515 16133386287634446640293773)
            ·
              refine ⟨6050019857862917490110165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16133386287634446640293773 6050019857862917490110165)
              ·
                refine ⟨141797340418662128674457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6050019857862917490110165 141797340418662128674457)
                ·
                  rfl

theorem cell23_7456032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 7].length) (baseStart_7456032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456032 prefixEnd_7456032 := by exact prefixLift 7456032
  have htrace : WordTrace (prefixWord ++ tailWord_7456032) baseStart_7456032 baseEnd_7456032 := by
    simpa [prefixWord, tailWord_7456032, baseEnd_7456032] using wordTrace_append hprefix tailTrace_7456032
  have hstable : (prefixWord ++ tailWord_7456032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456032).length < 2 ^ (prefixWord ++ tailWord_7456032).sum := by decide
  have hdescent : baseEnd_7456032 < baseStart_7456032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456070 : List Nat := [6, 1, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_7456070 : Nat := 118140960795 + 7456070 * 2 ^ 59
def prefixEnd_7456070 : Nat := 4983230072969 + 3 ^ 40 * 7456070 * 2
def baseEnd_7456070 : Nat := 1276182567856249441845055

theorem tailTrace_7456070 : CollatzResearch.WordTrace tailWord_7456070 prefixEnd_7456070 1276182567856249441845055 := by
  unfold tailWord_7456070
  simp only [CollatzResearch.WordTrace]
  refine ⟨8498287940560601881903927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 181296809398626173480617109 8498287940560601881903927)
  ·
    refine ⟨12747431910840902822855891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8498287940560601881903927 12747431910840902822855891)
    ·
      refine ⟨19121147866261354234283837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12747431910840902822855891 19121147866261354234283837)
      ·
        refine ⟨7170430449848007837856439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19121147866261354234283837 7170430449848007837856439)
        ·
          refine ⟨10755645674772011756784659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7170430449848007837856439 10755645674772011756784659)
          ·
            refine ⟨16133468512158017635176989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10755645674772011756784659 16133468512158017635176989)
            ·
              refine ⟨6050050692059256613191371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16133468512158017635176989 6050050692059256613191371)
              ·
                refine ⟨9075076038088884919787057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6050050692059256613191371 9075076038088884919787057)
                ·
                  refine ⟨6806307028566663689840293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9075076038088884919787057 6806307028566663689840293)
                  ·
                    refine ⟨1276182567856249441845055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6806307028566663689840293 1276182567856249441845055)
                    ·
                      rfl

theorem cell23_7456070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_7456070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456070 prefixEnd_7456070 := by exact prefixLift 7456070
  have htrace : WordTrace (prefixWord ++ tailWord_7456070) baseStart_7456070 baseEnd_7456070 := by
    simpa [prefixWord, tailWord_7456070, baseEnd_7456070] using wordTrace_append hprefix tailTrace_7456070
  have hstable : (prefixWord ++ tailWord_7456070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456070).length < 2 ^ (prefixWord ++ tailWord_7456070).sum := by decide
  have hdescent : baseEnd_7456070 < baseStart_7456070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456076 : List Nat := [2, 2, 1, 3, 2, 3, 3, 1, 2, 1, 3]
def baseStart_7456076 : Nat := 118140960795 + 7456076 * 2 ^ 59
def prefixEnd_7456076 : Nat := 4983230072969 + 3 ^ 40 * 7456076 * 2
def baseEnd_7456076 : Nat := 3828550784452675302060137

theorem tailTrace_7456076 : CollatzResearch.WordTrace tailWord_7456076 prefixEnd_7456076 3828550784452675302060137 := by
  unfold tailWord_7456076
  simp only [CollatzResearch.WordTrace]
  refine ⟨135972716467958761622822041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181296955290611682163762721 135972716467958761622822041)
  ·
    refine ⟨101979537350969071217116531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135972716467958761622822041 101979537350969071217116531)
    ·
      refine ⟨152969306026453606825674797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101979537350969071217116531 152969306026453606825674797)
      ·
        refine ⟨57363489759920102559628049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152969306026453606825674797 57363489759920102559628049)
        ·
          refine ⟨43022617319940076919721037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57363489759920102559628049 43022617319940076919721037)
          ·
            refine ⟨16133481494977528844895389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43022617319940076919721037 16133481494977528844895389)
            ·
              refine ⟨6050055560616573316835771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16133481494977528844895389 6050055560616573316835771)
              ·
                refine ⟨9075083340924859975253657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6050055560616573316835771 9075083340924859975253657)
                ·
                  refine ⟨6806312505693644981440243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9075083340924859975253657 6806312505693644981440243)
                  ·
                    refine ⟨10209468758540467472160365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6806312505693644981440243 10209468758540467472160365)
                    ·
                      refine ⟨3828550784452675302060137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10209468758540467472160365 3828550784452675302060137)
                      ·
                        rfl

theorem cell23_7456076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_7456076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456076 prefixEnd_7456076 := by exact prefixLift 7456076
  have htrace : WordTrace (prefixWord ++ tailWord_7456076) baseStart_7456076 baseEnd_7456076 := by
    simpa [prefixWord, tailWord_7456076, baseEnd_7456076] using wordTrace_append hprefix tailTrace_7456076
  have hstable : (prefixWord ++ tailWord_7456076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456076).length < 2 ^ (prefixWord ++ tailWord_7456076).sum := by decide
  have hdescent : baseEnd_7456076 < baseStart_7456076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456099 : List Nat := [1, 1, 1, 5, 2, 2, 1, 2, 4, 2, 2]
def baseStart_7456099 : Nat := 118140960795 + 7456099 * 2 ^ 59
def prefixEnd_7456099 : Nat := 4983230072969 + 3 ^ 40 * 7456099 * 2
def baseEnd_7456099 : Nat := 3828562594507728712072531

theorem tailTrace_7456099 : CollatzResearch.WordTrace tailWord_7456099 prefixEnd_7456099 3828562594507728712072531 := by
  unfold tailWord_7456099
  simp only [CollatzResearch.WordTrace]
  refine ⟨271946271814834198173731351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181297514543222798782487567 271946271814834198173731351)
  ·
    refine ⟨407919407722251297260597027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271946271814834198173731351 407919407722251297260597027)
    ·
      refine ⟨611879111583376945890895541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407919407722251297260597027 611879111583376945890895541)
      ·
        refine ⟨57363666710941588677271457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 611879111583376945890895541 57363666710941588677271457)
        ·
          refine ⟨43022750033206191507953593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57363666710941588677271457 43022750033206191507953593)
          ·
            refine ⟨32267062524904643630965195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43022750033206191507953593 32267062524904643630965195)
            ·
              refine ⟨48400593787356965446447793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32267062524904643630965195 48400593787356965446447793)
              ·
                refine ⟨36300445340517724084835845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48400593787356965446447793 36300445340517724084835845)
                ·
                  refine ⟨6806333501347073265906721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36300445340517724084835845 6806333501347073265906721)
                  ·
                    refine ⟨5104750126010304949430041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6806333501347073265906721 5104750126010304949430041)
                    ·
                      refine ⟨3828562594507728712072531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5104750126010304949430041 3828562594507728712072531)
                      ·
                        rfl

theorem cell23_7456099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_7456099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456099 prefixEnd_7456099 := by exact prefixLift 7456099
  have htrace : WordTrace (prefixWord ++ tailWord_7456099) baseStart_7456099 baseEnd_7456099 := by
    simpa [prefixWord, tailWord_7456099, baseEnd_7456099] using wordTrace_append hprefix tailTrace_7456099
  have hstable : (prefixWord ++ tailWord_7456099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456099).length < 2 ^ (prefixWord ++ tailWord_7456099).sum := by decide
  have hdescent : baseEnd_7456099 < baseStart_7456099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456162 : List Nat := [3, 3, 1, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_7456162 : Nat := 118140960795 + 7456162 * 2 ^ 59
def prefixEnd_7456162 : Nat := 4983230072969 + 3 ^ 40 * 7456162 * 2
def baseEnd_7456162 : Nat := 3828594943788961965584741

theorem tailTrace_7456162 : CollatzResearch.WordTrace tailWord_7456162 prefixEnd_7456162 3828594943788961965584741 := by
  unfold tailWord_7456162
  simp only [CollatzResearch.WordTrace]
  refine ⟨67987142403401489983318685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181299046409070639955516493 67987142403401489983318685)
  ·
    refine ⟨25495178401275558743744507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67987142403401489983318685 25495178401275558743744507)
    ·
      refine ⟨38242767601913338115616761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25495178401275558743744507 38242767601913338115616761)
      ·
        refine ⟨28682075701435003586712571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38242767601913338115616761 28682075701435003586712571)
        ·
          refine ⟨43023113552152505380068857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28682075701435003586712571 43023113552152505380068857)
          ·
            refine ⟨32267335164114379035051643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43023113552152505380068857 32267335164114379035051643)
            ·
              refine ⟨48401002746171568552577465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32267335164114379035051643 48401002746171568552577465)
              ·
                refine ⟨36300752059628676414433099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48401002746171568552577465 36300752059628676414433099)
                ·
                  refine ⟨54451128089443014621649649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36300752059628676414433099 54451128089443014621649649)
                  ·
                    refine ⟨40838346067082260966237237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54451128089443014621649649 40838346067082260966237237)
                    ·
                      refine ⟨3828594943788961965584741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40838346067082260966237237 3828594943788961965584741)
                      ·
                        rfl

theorem cell23_7456162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_7456162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456162 prefixEnd_7456162 := by exact prefixLift 7456162
  have htrace : WordTrace (prefixWord ++ tailWord_7456162) baseStart_7456162 baseEnd_7456162 := by
    simpa [prefixWord, tailWord_7456162, baseEnd_7456162] using wordTrace_append hprefix tailTrace_7456162
  have hstable : (prefixWord ++ tailWord_7456162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456162).length < 2 ^ (prefixWord ++ tailWord_7456162).sum := by decide
  have hdescent : baseEnd_7456162 < baseStart_7456162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456172 : List Nat := [2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 4]
def baseStart_7456172 : Nat := 118140960795 + 7456172 * 2 ^ 59
def prefixEnd_7456172 : Nat := 4983230072969 + 3 ^ 40 * 7456172 * 2
def baseEnd_7456172 : Nat := 3828600078595506926459695

theorem tailTrace_7456172 : CollatzResearch.WordTrace tailWord_7456172 prefixEnd_7456172 3828600078595506926459695 := by
  unfold tailWord_7456172
  simp only [CollatzResearch.WordTrace]
  refine ⟨135974467171784865820569385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181299289562379821094092513 135974467171784865820569385)
  ·
    refine ⟨101980850378838649365427039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135974467171784865820569385 101980850378838649365427039)
    ·
      refine ⟨152971275568257974048140559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101980850378838649365427039 152971275568257974048140559)
      ·
        refine ⟨229456913352386961072210839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152971275568257974048140559 229456913352386961072210839)
        ·
          refine ⟨344185370028580441608316259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229456913352386961072210839 344185370028580441608316259)
          ·
            refine ⟨516278055042870662412474389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344185370028580441608316259 516278055042870662412474389)
            ·
              refine ⟨24200533830134562300584737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 516278055042870662412474389 24200533830134562300584737)
              ·
                refine ⟨18150400372600921725438553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24200533830134562300584737 18150400372600921725438553)
                ·
                  refine ⟨13612800279450691294078915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18150400372600921725438553 13612800279450691294078915)
                  ·
                    refine ⟨20419200419176036941118373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13612800279450691294078915 20419200419176036941118373)
                    ·
                      refine ⟨3828600078595506926459695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20419200419176036941118373 3828600078595506926459695)
                      ·
                        rfl

theorem cell23_7456172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_7456172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456172 prefixEnd_7456172 := by exact prefixLift 7456172
  have htrace : WordTrace (prefixWord ++ tailWord_7456172) baseStart_7456172 baseEnd_7456172 := by
    simpa [prefixWord, tailWord_7456172, baseEnd_7456172] using wordTrace_append hprefix tailTrace_7456172
  have hstable : (prefixWord ++ tailWord_7456172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456172).length < 2 ^ (prefixWord ++ tailWord_7456172).sum := by decide
  have hdescent : baseEnd_7456172 < baseStart_7456172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456173 : List Nat := [1, 5, 2, 2, 1, 3, 2, 2, 5]
def baseStart_7456173 : Nat := 118140960795 + 7456173 * 2 ^ 59
def prefixEnd_7456173 : Nat := 4983230072969 + 3 ^ 40 * 7456173 * 2
def baseEnd_7456173 : Nat := 425400065786240158060799

theorem tailTrace_7456173 : CollatzResearch.WordTrace tailWord_7456173 prefixEnd_7456173 425400065786240158060799 := by
  unfold tailWord_7456173
  simp only [CollatzResearch.WordTrace]
  refine ⟨271948970816566108811925173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181299313877710739207950115 271948970816566108811925173)
  ·
    refine ⟨25495216014053072701117985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 271948970816566108811925173 25495216014053072701117985)
    ·
      refine ⟨19121412010539804525838489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25495216014053072701117985 19121412010539804525838489)
      ·
        refine ⟨14341059007904853394378867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19121412010539804525838489 14341059007904853394378867)
        ·
          refine ⟨21511588511857280091568301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14341059007904853394378867 21511588511857280091568301)
          ·
            refine ⟨8066845691946480034338113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21511588511857280091568301 8066845691946480034338113)
            ·
              refine ⟨6050134268959860025753585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8066845691946480034338113 6050134268959860025753585)
              ·
                refine ⟨4537600701719895019315189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6050134268959860025753585 4537600701719895019315189)
                ·
                  refine ⟨425400065786240158060799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4537600701719895019315189 425400065786240158060799)
                  ·
                    rfl

theorem cell23_7456173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_7456173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456173 prefixEnd_7456173 := by exact prefixLift 7456173
  have htrace : WordTrace (prefixWord ++ tailWord_7456173) baseStart_7456173 baseEnd_7456173 := by
    simpa [prefixWord, tailWord_7456173, baseEnd_7456173] using wordTrace_append hprefix tailTrace_7456173
  have hstable : (prefixWord ++ tailWord_7456173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456173).length < 2 ^ (prefixWord ++ tailWord_7456173).sum := by decide
  have hdescent : baseEnd_7456173 < baseStart_7456173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456189 : List Nat := [1, 4, 1, 2, 2, 1, 3, 1, 2, 4, 2]
def baseStart_7456189 : Nat := 118140960795 + 7456189 * 2 ^ 59
def prefixEnd_7456189 : Nat := 4983230072969 + 3 ^ 40 * 7456189 * 2
def baseEnd_7456189 : Nat := 3828608807766633359947117

theorem tailTrace_7456189 : CollatzResearch.WordTrace tailWord_7456189 prefixEnd_7456189 3828608807766633359947117 := by
  unfold tailWord_7456189
  simp only [CollatzResearch.WordTrace]
  refine ⟨271949554384508143544507621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181299702923005429029671747 271949554384508143544507621)
  ·
    refine ⟨50990541447095276914595179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271949554384508143544507621 50990541447095276914595179)
    ·
      refine ⟨76485812170642915371892769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50990541447095276914595179 76485812170642915371892769)
      ·
        refine ⟨57364359127982186528919577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76485812170642915371892769 57364359127982186528919577)
        ·
          refine ⟨43023269345986639896689683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57364359127982186528919577 43023269345986639896689683)
          ·
            refine ⟨64534904018979959845034525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43023269345986639896689683 64534904018979959845034525)
            ·
              refine ⟨24200589007117484941887947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64534904018979959845034525 24200589007117484941887947)
              ·
                refine ⟨36300883510676227412831921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24200589007117484941887947 36300883510676227412831921)
                ·
                  refine ⟨27225662633007170559623941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36300883510676227412831921 27225662633007170559623941)
                  ·
                    refine ⟨5104811743688844479929489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27225662633007170559623941 5104811743688844479929489)
                    ·
                      refine ⟨3828608807766633359947117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5104811743688844479929489 3828608807766633359947117)
                      ·
                        rfl

theorem cell23_7456189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_7456189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456189 prefixEnd_7456189 := by exact prefixLift 7456189
  have htrace : WordTrace (prefixWord ++ tailWord_7456189) baseStart_7456189 baseEnd_7456189 := by
    simpa [prefixWord, tailWord_7456189, baseEnd_7456189] using wordTrace_append hprefix tailTrace_7456189
  have hstable : (prefixWord ++ tailWord_7456189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456189).length < 2 ^ (prefixWord ++ tailWord_7456189).sum := by decide
  have hdescent : baseEnd_7456189 < baseStart_7456189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456192 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 3]
def baseStart_7456192 : Nat := 118140960795 + 7456192 * 2 ^ 59
def prefixEnd_7456192 : Nat := 4983230072969 + 3 ^ 40 * 7456192 * 2
def baseEnd_7456192 : Nat := 3828610348208596848209603

theorem tailTrace_7456192 : CollatzResearch.WordTrace tailWord_7456192 prefixEnd_7456192 3828610348208596848209603 := by
  unfold tailWord_7456192
  simp only [CollatzResearch.WordTrace]
  refine ⟨135974831901748637528433415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181299775868998183371244553 135974831901748637528433415)
  ·
    refine ⟨203962247852622956292650123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135974831901748637528433415 203962247852622956292650123)
    ·
      refine ⟨305943371778934434438975185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203962247852622956292650123 305943371778934434438975185)
      ·
        refine ⟨229457528834200825829231389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305943371778934434438975185 229457528834200825829231389)
        ·
          refine ⟨86046573312825309685961771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229457528834200825829231389 86046573312825309685961771)
          ·
            refine ⟨129069859969237964528942657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86046573312825309685961771 129069859969237964528942657)
            ·
              refine ⟨96802394976928473396706993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129069859969237964528942657 96802394976928473396706993)
              ·
                refine ⟨72601796232696355047530245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96802394976928473396706993 72601796232696355047530245)
                ·
                  refine ⟨13612836793630566571411921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72601796232696355047530245 13612836793630566571411921)
                  ·
                    refine ⟨10209627595222924928558941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13612836793630566571411921 10209627595222924928558941)
                    ·
                      refine ⟨3828610348208596848209603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10209627595222924928558941 3828610348208596848209603)
                      ·
                        rfl

theorem cell23_7456192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 3].length) (baseStart_7456192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456192 prefixEnd_7456192 := by exact prefixLift 7456192
  have htrace : WordTrace (prefixWord ++ tailWord_7456192) baseStart_7456192 baseEnd_7456192 := by
    simpa [prefixWord, tailWord_7456192, baseEnd_7456192] using wordTrace_append hprefix tailTrace_7456192
  have hstable : (prefixWord ++ tailWord_7456192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456192).length < 2 ^ (prefixWord ++ tailWord_7456192).sum := by decide
  have hdescent : baseEnd_7456192 < baseStart_7456192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456215 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 6]
def baseStart_7456215 : Nat := 118140960795 + 7456215 * 2 ^ 59
def prefixEnd_7456215 : Nat := 4983230072969 + 3 ^ 40 * 7456215 * 2
def baseEnd_7456215 : Nat := 3828622158263650258221997

theorem tailTrace_7456215 : CollatzResearch.WordTrace tailWord_7456215 prefixEnd_7456215 3828622158263650258221997 := by
  unfold tailWord_7456215
  simp only [CollatzResearch.WordTrace]
  refine ⟨271950502682413949984954099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181300335121609299989969399 271950502682413949984954099)
  ·
    refine ⟨407925754023620924977431149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271950502682413949984954099 407925754023620924977431149)
    ·
      refine ⟨152972157758857846866536681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407925754023620924977431149 152972157758857846866536681)
      ·
        refine ⟨114729118319143385149902511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152972157758857846866536681 114729118319143385149902511)
        ·
          refine ⟨172093677478715077724853767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114729118319143385149902511 172093677478715077724853767)
          ·
            refine ⟨258140516218072616587280651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172093677478715077724853767 258140516218072616587280651)
            ·
              refine ⟨387210774327108924880920977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258140516218072616587280651 387210774327108924880920977)
              ·
                refine ⟨290408080745331693660690733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387210774327108924880920977 290408080745331693660690733)
                ·
                  refine ⟨108903030279499385122759025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 290408080745331693660690733 108903030279499385122759025)
                  ·
                    refine ⟨81677272709624538842069269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108903030279499385122759025 81677272709624538842069269)
                    ·
                      refine ⟨3828622158263650258221997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81677272709624538842069269 3828622158263650258221997)
                      ·
                        rfl

theorem cell23_7456215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_7456215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456215 prefixEnd_7456215 := by exact prefixLift 7456215
  have htrace : WordTrace (prefixWord ++ tailWord_7456215) baseStart_7456215 baseEnd_7456215 := by
    simpa [prefixWord, tailWord_7456215, baseEnd_7456215] using wordTrace_append hprefix tailTrace_7456215
  have hstable : (prefixWord ++ tailWord_7456215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456215).length < 2 ^ (prefixWord ++ tailWord_7456215).sum := by decide
  have hdescent : baseEnd_7456215 < baseStart_7456215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456229 : List Nat := [1, 3, 1, 5, 1, 1, 3, 2, 6]
def baseStart_7456229 : Nat := 118140960795 + 7456229 * 2 ^ 59
def prefixEnd_7456229 : Nat := 4983230072969 + 3 ^ 40 * 7456229 * 2
def baseEnd_7456229 : Nat := 425403260776979244827437

theorem tailTrace_7456229 : CollatzResearch.WordTrace tailWord_7456229 prefixEnd_7456229 425403260776979244827437 := by
  unfold tailWord_7456229
  simp only [CollatzResearch.WordTrace]
  refine ⟨271951013304363230375963741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181300675536242153583975827 271951013304363230375963741)
  ·
    refine ⟨101981629989136211390986403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271951013304363230375963741 101981629989136211390986403)
    ·
      refine ⟨152972444983704317086479605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101981629989136211390986403 152972444983704317086479605)
      ·
        refine ⟨14341166717222279726857463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152972444983704317086479605 14341166717222279726857463)
        ·
          refine ⟨21511750075833419590286195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14341166717222279726857463 21511750075833419590286195)
          ·
            refine ⟨32267625113750129385429293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21511750075833419590286195 32267625113750129385429293)
            ·
              refine ⟨12100359417656298519535985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32267625113750129385429293 12100359417656298519535985)
              ·
                refine ⟨9075269563242223889651989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12100359417656298519535985 9075269563242223889651989)
                ·
                  refine ⟨425403260776979244827437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9075269563242223889651989 425403260776979244827437)
                  ·
                    rfl

theorem cell23_7456229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 6].length) (baseStart_7456229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456229 prefixEnd_7456229 := by exact prefixLift 7456229
  have htrace : WordTrace (prefixWord ++ tailWord_7456229) baseStart_7456229 baseEnd_7456229 := by
    simpa [prefixWord, tailWord_7456229, baseEnd_7456229] using wordTrace_append hprefix tailTrace_7456229
  have hstable : (prefixWord ++ tailWord_7456229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456229).length < 2 ^ (prefixWord ++ tailWord_7456229).sum := by decide
  have hdescent : baseEnd_7456229 < baseStart_7456229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456235 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 7]
def baseStart_7456235 : Nat := 118140960795 + 7456235 * 2 ^ 59
def prefixEnd_7456235 : Nat := 4983230072969 + 3 ^ 40 * 7456235 * 2
def baseEnd_7456235 : Nat := 3828632427876740179971905

theorem tailTrace_7456235 : CollatzResearch.WordTrace tailWord_7456235 prefixEnd_7456235 3828632427876740179971905 := by
  unfold tailWord_7456235
  simp only [CollatzResearch.WordTrace]
  refine ⟨271951232142341493400682159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181300821428227662267121439 271951232142341493400682159)
  ·
    refine ⟨407926848213512240101023239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271951232142341493400682159 407926848213512240101023239)
    ·
      refine ⟨611890272320268360151534859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407926848213512240101023239 611890272320268360151534859)
      ·
        refine ⟨917835408480402540227302289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611890272320268360151534859 917835408480402540227302289)
        ·
          refine ⟨688376556360301905170476717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 917835408480402540227302289 688376556360301905170476717)
          ·
            refine ⟨258141208635113214438928769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 688376556360301905170476717 258141208635113214438928769)
            ·
              refine ⟨193605906476334910829196577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258141208635113214438928769 193605906476334910829196577)
              ·
                refine ⟨145204429857251183121897433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193605906476334910829196577 145204429857251183121897433)
                ·
                  refine ⟨108903322392938387341423075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145204429857251183121897433 108903322392938387341423075)
                  ·
                    refine ⟨163354983589407581012134613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108903322392938387341423075 163354983589407581012134613)
                    ·
                      refine ⟨3828632427876740179971905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163354983589407581012134613 3828632427876740179971905)
                      ·
                        rfl

theorem cell23_7456235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 7].length) (baseStart_7456235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456235 prefixEnd_7456235 := by exact prefixLift 7456235
  have htrace : WordTrace (prefixWord ++ tailWord_7456235) baseStart_7456235 baseEnd_7456235 := by
    simpa [prefixWord, tailWord_7456235, baseEnd_7456235] using wordTrace_append hprefix tailTrace_7456235
  have hstable : (prefixWord ++ tailWord_7456235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456235).length < 2 ^ (prefixWord ++ tailWord_7456235).sum := by decide
  have hdescent : baseEnd_7456235 < baseStart_7456235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456239 : List Nat := [1, 1, 2, 1, 4, 1, 3, 3, 3, 1, 3]
def baseStart_7456239 : Nat := 118140960795 + 7456239 * 2 ^ 59
def prefixEnd_7456239 : Nat := 4983230072969 + 3 ^ 40 * 7456239 * 2
def baseEnd_7456239 : Nat := 3828634481799358164321887

theorem tailTrace_7456239 : CollatzResearch.WordTrace tailWord_7456239 prefixEnd_7456239 3828634481799358164321887 := by
  unfold tailWord_7456239
  simp only [CollatzResearch.WordTrace]
  refine ⟨271951378034327002083827771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181300918689551334722551847 271951378034327002083827771)
  ·
    refine ⟨407927067051490503125741657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271951378034327002083827771 407927067051490503125741657)
    ·
      refine ⟨305945300288617877344306243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407927067051490503125741657 305945300288617877344306243)
      ·
        refine ⟨458917950432926816016459365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305945300288617877344306243 458917950432926816016459365)
        ·
          refine ⟨86047115706173778003086131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 458917950432926816016459365 86047115706173778003086131)
          ·
            refine ⟨129070673559260667004629197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86047115706173778003086131 129070673559260667004629197)
            ·
              refine ⟨48401502584722750126735949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129070673559260667004629197 48401502584722750126735949)
              ·
                refine ⟨18150563469271031297525981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48401502584722750126735949 18150563469271031297525981)
                ·
                  refine ⟨6806461300976636736572243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18150563469271031297525981 6806461300976636736572243)
                  ·
                    refine ⟨10209691951464955104858365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6806461300976636736572243 10209691951464955104858365)
                    ·
                      refine ⟨3828634481799358164321887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10209691951464955104858365 3828634481799358164321887)
                      ·
                        rfl

theorem cell23_7456239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3, 1, 3].length) (baseStart_7456239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456239 prefixEnd_7456239 := by exact prefixLift 7456239
  have htrace : WordTrace (prefixWord ++ tailWord_7456239) baseStart_7456239 baseEnd_7456239 := by
    simpa [prefixWord, tailWord_7456239, baseEnd_7456239] using wordTrace_append hprefix tailTrace_7456239
  have hstable : (prefixWord ++ tailWord_7456239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456239).length < 2 ^ (prefixWord ++ tailWord_7456239).sum := by decide
  have hdescent : baseEnd_7456239 < baseStart_7456239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456246 : List Nat := [5, 1, 1, 1, 2, 3, 3, 1, 6]
def baseStart_7456246 : Nat := 118140960795 + 7456246 * 2 ^ 59
def prefixEnd_7456246 : Nat := 4983230072969 + 3 ^ 40 * 7456246 * 2
def baseEnd_7456246 : Nat := 425404230684882181881595

theorem tailTrace_7456246 : CollatzResearch.WordTrace tailWord_7456246 prefixEnd_7456246 425404230684882181881595 := by
  unfold tailWord_7456246
  simp only [CollatzResearch.WordTrace]
  refine ⟨16996977084081352642458287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181301088896867761519555061 16996977084081352642458287)
  ·
    refine ⟨25495465626122028963687431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16996977084081352642458287 25495465626122028963687431)
    ·
      refine ⟨38243198439183043445531147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25495465626122028963687431 38243198439183043445531147)
      ·
        refine ⟨57364797658774565168296721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38243198439183043445531147 57364797658774565168296721)
        ·
          refine ⟨43023598244080923876222541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57364797658774565168296721 43023598244080923876222541)
          ·
            refine ⟨16133849341530346453583453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43023598244080923876222541 16133849341530346453583453)
            ·
              refine ⟨6050193503073879920093795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16133849341530346453583453 6050193503073879920093795)
              ·
                refine ⟨9075290254610819880140693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6050193503073879920093795 9075290254610819880140693)
                ·
                  refine ⟨425404230684882181881595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9075290254610819880140693 425404230684882181881595)
                  ·
                    rfl

theorem cell23_7456246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_7456246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456246 prefixEnd_7456246 := by exact prefixLift 7456246
  have htrace : WordTrace (prefixWord ++ tailWord_7456246) baseStart_7456246 baseEnd_7456246 := by
    simpa [prefixWord, tailWord_7456246, baseEnd_7456246] using wordTrace_append hprefix tailTrace_7456246
  have hstable : (prefixWord ++ tailWord_7456246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456246).length < 2 ^ (prefixWord ++ tailWord_7456246).sum := by decide
  have hdescent : baseEnd_7456246 < baseStart_7456246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456289 : List Nat := [1, 2, 3, 2, 2, 2, 2, 1, 4, 4]
def baseStart_7456289 : Nat := 118140960795 + 7456289 * 2 ^ 59
def prefixEnd_7456289 : Nat := 4983230072969 + 3 ^ 40 * 7456289 * 2
def baseEnd_7456289 : Nat := 1276220051944027656232219

theorem tailTrace_7456289 : CollatzResearch.WordTrace tailWord_7456289 prefixEnd_7456289 1276220051944027656232219 := by
  unfold tailWord_7456289
  simp only [CollatzResearch.WordTrace]
  refine ⟨271953201684145860623147921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181302134456097240415431947 271953201684145860623147921)
  ·
    refine ⟨203964901263109395467360941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271953201684145860623147921 203964901263109395467360941)
    ·
      refine ⟨76486837973666023300260353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203964901263109395467360941 76486837973666023300260353)
      ·
        refine ⟨57365128480249517475195265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76486837973666023300260353 57365128480249517475195265)
        ·
          refine ⟨43023846360187138106396449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57365128480249517475195265 43023846360187138106396449)
          ·
            refine ⟨32267884770140353579797337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43023846360187138106396449 32267884770140353579797337)
            ·
              refine ⟨24200913577605265184848003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32267884770140353579797337 24200913577605265184848003)
              ·
                refine ⟨36301370366407897777272005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24200913577605265184848003 36301370366407897777272005)
                ·
                  refine ⟨6806506943701480833238501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36301370366407897777272005 6806506943701480833238501)
                  ·
                    refine ⟨1276220051944027656232219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6806506943701480833238501 1276220051944027656232219)
                    ·
                      rfl

theorem cell23_7456289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_7456289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456289 prefixEnd_7456289 := by exact prefixLift 7456289
  have htrace : WordTrace (prefixWord ++ tailWord_7456289) baseStart_7456289 baseEnd_7456289 := by
    simpa [prefixWord, tailWord_7456289, baseEnd_7456289] using wordTrace_append hprefix tailTrace_7456289
  have hstable : (prefixWord ++ tailWord_7456289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456289).length < 2 ^ (prefixWord ++ tailWord_7456289).sum := by decide
  have hdescent : baseEnd_7456289 < baseStart_7456289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456310 : List Nat := [5, 1, 2, 1, 4, 1, 1, 2, 1, 5]
def baseStart_7456310 : Nat := 118140960795 + 7456310 * 2 ^ 59
def prefixEnd_7456310 : Nat := 4983230072969 + 3 ^ 40 * 7456310 * 2
def baseEnd_7456310 : Nat := 1276223646308609128844687

theorem tailTrace_7456310 : CollatzResearch.WordTrace tailWord_7456310 prefixEnd_7456310 1276223646308609128844687 := by
  unfold tailWord_7456310
  simp only [CollatzResearch.WordTrace]
  refine ⟨16997122976066861325603899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181302645078046520806441589 16997122976066861325603899)
  ·
    refine ⟨25495684464100291988405849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16997122976066861325603899 25495684464100291988405849)
    ·
      refine ⟨19121763348075218991304387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25495684464100291988405849 19121763348075218991304387)
      ·
        refine ⟨28682645022112828486956581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19121763348075218991304387 28682645022112828486956581)
        ·
          refine ⟨5377995941646155341304359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28682645022112828486956581 5377995941646155341304359)
          ·
            refine ⟨8066993912469233011956539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5377995941646155341304359 8066993912469233011956539)
            ·
              refine ⟨12100490868703849517934809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8066993912469233011956539 12100490868703849517934809)
              ·
                refine ⟨9075368151527887138451107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12100490868703849517934809 9075368151527887138451107)
                ·
                  refine ⟨13613052227291830707676661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9075368151527887138451107 13613052227291830707676661)
                  ·
                    refine ⟨1276223646308609128844687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13613052227291830707676661 1276223646308609128844687)
                    ·
                      rfl

theorem cell23_7456310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_7456310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456310 prefixEnd_7456310 := by exact prefixLift 7456310
  have htrace : WordTrace (prefixWord ++ tailWord_7456310) baseStart_7456310 baseEnd_7456310 := by
    simpa [prefixWord, tailWord_7456310, baseEnd_7456310] using wordTrace_append hprefix tailTrace_7456310
  have hstable : (prefixWord ++ tailWord_7456310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456310).length < 2 ^ (prefixWord ++ tailWord_7456310).sum := by decide
  have hdescent : baseEnd_7456310 < baseStart_7456310 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456316 : List Nat := [2, 2, 2, 2, 4, 1, 1, 1, 3, 2, 3]
def baseStart_7456316 : Nat := 118140960795 + 7456316 * 2 ^ 59
def prefixEnd_7456316 : Nat := 4983230072969 + 3 ^ 40 * 7456316 * 2
def baseEnd_7456316 : Nat := 3828674019809754363059033

theorem tailTrace_7456316 : CollatzResearch.WordTrace tailWord_7456316 prefixEnd_7456316 3828674019809754363059033 := by
  unfold tailWord_7456316
  simp only [CollatzResearch.WordTrace]
  refine ⟨135977093227524022117190401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181302790970032029489587201 135977093227524022117190401)
  ·
    refine ⟨101982819920643016587892801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135977093227524022117190401 101982819920643016587892801)
    ·
      refine ⟨76487114940482262440919601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101982819920643016587892801 76487114940482262440919601)
      ·
        refine ⟨57365336205361696830689701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76487114940482262440919601 57365336205361696830689701)
        ·
          refine ⟨10756000538505318155754319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57365336205361696830689701 10756000538505318155754319)
          ·
            refine ⟨16134000807757977233631479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10756000538505318155754319 16134000807757977233631479)
            ·
              refine ⟨24201001211636965850447219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16134000807757977233631479 24201001211636965850447219)
              ·
                refine ⟨36301501817455448775670829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24201001211636965850447219 36301501817455448775670829)
                ·
                  refine ⟨13613063181545793290876561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36301501817455448775670829 13613063181545793290876561)
                  ·
                    refine ⟨10209797386159344968157421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13613063181545793290876561 10209797386159344968157421)
                    ·
                      refine ⟨3828674019809754363059033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10209797386159344968157421 3828674019809754363059033)
                      ·
                        rfl

theorem cell23_7456316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_7456316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456316 prefixEnd_7456316 := by exact prefixLift 7456316
  have htrace : WordTrace (prefixWord ++ tailWord_7456316) baseStart_7456316 baseEnd_7456316 := by
    simpa [prefixWord, tailWord_7456316, baseEnd_7456316] using wordTrace_append hprefix tailTrace_7456316
  have hstable : (prefixWord ++ tailWord_7456316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456316).length < 2 ^ (prefixWord ++ tailWord_7456316).sum := by decide
  have hdescent : baseEnd_7456316 < baseStart_7456316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456329 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 6, 1, 3]
def baseStart_7456329 : Nat := 118140960795 + 7456329 * 2 ^ 59
def prefixEnd_7456329 : Nat := 4983230072969 + 3 ^ 40 * 7456329 * 2
def baseEnd_7456329 : Nat := 3828680695058262812196473

theorem tailTrace_7456329 : CollatzResearch.WordTrace tailWord_7456329 prefixEnd_7456329 3828680695058262812196473 := by
  unfold tailWord_7456329
  simp only [CollatzResearch.WordTrace]
  refine ⟨271954660604000947454604041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181303107069333964969736027 271954660604000947454604041)
  ·
    refine ⟨203965995453000710590953031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271954660604000947454604041 203965995453000710590953031)
    ·
      refine ⟨305948993179501065886429547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203965995453000710590953031 305948993179501065886429547)
      ·
        refine ⟨458923489769251598829644321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305948993179501065886429547 458923489769251598829644321)
        ·
          refine ⟨344192617326938699122233241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 458923489769251598829644321 344192617326938699122233241)
          ·
            refine ⟨258144462995204024341674931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344192617326938699122233241 258144462995204024341674931)
            ·
              refine ⟨387216694492806036512512397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258144462995204024341674931 387216694492806036512512397)
              ·
                refine ⟨145206260434802263692192149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 387216694492806036512512397 145206260434802263692192149)
                ·
                  refine ⟨6806543457881356110571507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 145206260434802263692192149 6806543457881356110571507)
                  ·
                    refine ⟨10209815186822034165857261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6806543457881356110571507 10209815186822034165857261)
                    ·
                      refine ⟨3828680695058262812196473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10209815186822034165857261 3828680695058262812196473)
                      ·
                        rfl

theorem cell23_7456329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6, 1, 3].length) (baseStart_7456329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456329 prefixEnd_7456329 := by exact prefixLift 7456329
  have htrace : WordTrace (prefixWord ++ tailWord_7456329) baseStart_7456329 baseEnd_7456329 := by
    simpa [prefixWord, tailWord_7456329, baseEnd_7456329] using wordTrace_append hprefix tailTrace_7456329
  have hstable : (prefixWord ++ tailWord_7456329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456329).length < 2 ^ (prefixWord ++ tailWord_7456329).sum := by decide
  have hdescent : baseEnd_7456329 < baseStart_7456329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456333 : List Nat := [1, 6, 1, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_7456333 : Nat := 118140960795 + 7456333 * 2 ^ 59
def prefixEnd_7456333 : Nat := 4983230072969 + 3 ^ 40 * 7456333 * 2
def baseEnd_7456333 : Nat := 3828682748980880796546455

theorem tailTrace_7456333 : CollatzResearch.WordTrace tailWord_7456333 prefixEnd_7456333 3828682748980880796546455 := by
  unfold tailWord_7456333
  simp only [CollatzResearch.WordTrace]
  refine ⟨271954806495986456137749653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181303204330657637425166435 271954806495986456137749653)
  ·
    refine ⟨12747881554499365131457015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 271954806495986456137749653 12747881554499365131457015)
    ·
      refine ⟨19121822331749047697185523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12747881554499365131457015 19121822331749047697185523)
      ·
        refine ⟨28682733497623571545778285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19121822331749047697185523 28682733497623571545778285)
        ·
          refine ⟨10756025061608839329666857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28682733497623571545778285 10756025061608839329666857)
          ·
            refine ⟨8067018796206629497250143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10756025061608839329666857 8067018796206629497250143)
            ·
              refine ⟨12100528194309944245875215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8067018796206629497250143 12100528194309944245875215)
              ·
                refine ⟨18150792291464916368812823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12100528194309944245875215 18150792291464916368812823)
                ·
                  refine ⟨27226188437197374553219235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18150792291464916368812823 27226188437197374553219235)
                  ·
                    refine ⟨40839282655796061829828853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27226188437197374553219235 40839282655796061829828853)
                    ·
                      refine ⟨3828682748980880796546455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40839282655796061829828853 3828682748980880796546455)
                      ·
                        rfl

theorem cell23_7456333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_7456333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456333 prefixEnd_7456333 := by exact prefixLift 7456333
  have htrace : WordTrace (prefixWord ++ tailWord_7456333) baseStart_7456333 baseEnd_7456333 := by
    simpa [prefixWord, tailWord_7456333, baseEnd_7456333] using wordTrace_append hprefix tailTrace_7456333
  have hstable : (prefixWord ++ tailWord_7456333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456333).length < 2 ^ (prefixWord ++ tailWord_7456333).sum := by decide
  have hdescent : baseEnd_7456333 < baseStart_7456333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456356 : List Nat := [2, 3, 1, 1, 2, 3, 1, 2, 3, 3, 2]
def baseStart_7456356 : Nat := 118140960795 + 7456356 * 2 ^ 59
def prefixEnd_7456356 : Nat := 4983230072969 + 3 ^ 40 * 7456356 * 2
def baseEnd_7456356 : Nat := 3828694559035934206558849

theorem tailTrace_7456356 : CollatzResearch.WordTrace tailWord_7456356 prefixEnd_7456356 3828694559035934206558849 := by
  unfold tailWord_7456356
  simp only [CollatzResearch.WordTrace]
  refine ⟨135977822687451565532918461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181303763583268754043891281 135977822687451565532918461)
  ·
    refine ⟨50991683507794337074844423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135977822687451565532918461 50991683507794337074844423)
    ·
      refine ⟨76487525261691505612266635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50991683507794337074844423 76487525261691505612266635)
      ·
        refine ⟨114731287892537258418399953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76487525261691505612266635 114731287892537258418399953)
        ·
          refine ⟨86048465919402943813799965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114731287892537258418399953 86048465919402943813799965)
          ·
            refine ⟨32268174719776103930174987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86048465919402943813799965 32268174719776103930174987)
            ·
              refine ⟨48402262079664155895262481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32268174719776103930174987 48402262079664155895262481)
              ·
                refine ⟨36301696559748116921446861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48402262079664155895262481 36301696559748116921446861)
                ·
                  refine ⟨13613136209905543845542573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36301696559748116921446861 13613136209905543845542573)
                  ·
                    refine ⟨5104926078714578942078465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13613136209905543845542573 5104926078714578942078465)
                    ·
                      refine ⟨3828694559035934206558849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5104926078714578942078465 3828694559035934206558849)
                      ·
                        rfl

theorem cell23_7456356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 3, 3, 2].length) (baseStart_7456356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456356 prefixEnd_7456356 := by exact prefixLift 7456356
  have htrace : WordTrace (prefixWord ++ tailWord_7456356) baseStart_7456356 baseEnd_7456356 := by
    simpa [prefixWord, tailWord_7456356, baseEnd_7456356] using wordTrace_append hprefix tailTrace_7456356
  have hstable : (prefixWord ++ tailWord_7456356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456356).length < 2 ^ (prefixWord ++ tailWord_7456356).sum := by decide
  have hdescent : baseEnd_7456356 < baseStart_7456356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456373 : List Nat := [1, 3, 4, 2, 1, 1, 2, 1, 3, 3, 2]
def baseStart_7456373 : Nat := 118140960795 + 7456373 * 2 ^ 59
def prefixEnd_7456373 : Nat := 4983230072969 + 3 ^ 40 * 7456373 * 2
def baseEnd_7456373 : Nat := 3828703288207060640046271

theorem tailTrace_7456373 : CollatzResearch.WordTrace tailWord_7456373 prefixEnd_7456373 3828703288207060640046271 := by
  unfold tailWord_7456373
  simp only [CollatzResearch.WordTrace]
  refine ⟨271956265415841542969205773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181304176943894361979470515 271956265415841542969205773)
  ·
    refine ⟨101983599530940578613452165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271956265415841542969205773 101983599530940578613452165)
    ·
      refine ⟨19121924912051358490022281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101983599530940578613452165 19121924912051358490022281)
      ·
        refine ⟨14341443684038518867516711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19121924912051358490022281 14341443684038518867516711)
        ·
          refine ⟨21512165526057778301275067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14341443684038518867516711 21512165526057778301275067)
          ·
            refine ⟨32268248289086667451912601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21512165526057778301275067 32268248289086667451912601)
            ·
              refine ⟨24201186216815000588934451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32268248289086667451912601 24201186216815000588934451)
              ·
                refine ⟨36301779325222500883401677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24201186216815000588934451 36301779325222500883401677)
                ·
                  refine ⟨13613167246958437831275629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36301779325222500883401677 13613167246958437831275629)
                  ·
                    refine ⟨5104937717609414186728361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13613167246958437831275629 5104937717609414186728361)
                    ·
                      refine ⟨3828703288207060640046271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5104937717609414186728361 3828703288207060640046271)
                      ·
                        rfl

theorem cell23_7456373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_7456373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456373 prefixEnd_7456373 := by exact prefixLift 7456373
  have htrace : WordTrace (prefixWord ++ tailWord_7456373) baseStart_7456373 baseEnd_7456373 := by
    simpa [prefixWord, tailWord_7456373, baseEnd_7456373] using wordTrace_append hprefix tailTrace_7456373
  have hstable : (prefixWord ++ tailWord_7456373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456373).length < 2 ^ (prefixWord ++ tailWord_7456373).sum := by decide
  have hdescent : baseEnd_7456373 < baseStart_7456373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456419 : List Nat := [1, 1, 1, 4, 1, 1, 3, 3, 2, 3, 3]
def baseStart_7456419 : Nat := 118140960795 + 7456419 * 2 ^ 59
def prefixEnd_7456419 : Nat := 4983230072969 + 3 ^ 40 * 7456419 * 2
def baseEnd_7456419 : Nat := 3828726908317167460071059

theorem tailTrace_7456419 : CollatzResearch.WordTrace tailWord_7456419 prefixEnd_7456419 3828726908317167460071059 := by
  unfold tailWord_7456419
  simp only [CollatzResearch.WordTrace]
  refine ⟨271957943173674892825380311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181305295449116595216920207 271957943173674892825380311)
  ·
    refine ⟨407936914760512339238070467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271957943173674892825380311 407936914760512339238070467)
    ·
      refine ⟨611905372140768508857105701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407936914760512339238070467 611905372140768508857105701)
      ·
        refine ⟨114732257276394095410707319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 611905372140768508857105701 114732257276394095410707319)
        ·
          refine ⟨172098385914591143116060979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114732257276394095410707319 172098385914591143116060979)
          ·
            refine ⟨258147578871886714674091469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172098385914591143116060979 258147578871886714674091469)
            ·
              refine ⟨96805342076957518002784301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258147578871886714674091469 96805342076957518002784301)
              ·
                refine ⟨36302003278859069251044113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96805342076957518002784301 36302003278859069251044113)
                ·
                  refine ⟨27226502459144301938283085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36302003278859069251044113 27226502459144301938283085)
                  ·
                    refine ⟨10209938422179113226856157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27226502459144301938283085 10209938422179113226856157)
                    ·
                      refine ⟨3828726908317167460071059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10209938422179113226856157 3828726908317167460071059)
                      ·
                        rfl

theorem cell23_7456419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_7456419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456419 prefixEnd_7456419 := by exact prefixLift 7456419
  have htrace : WordTrace (prefixWord ++ tailWord_7456419) baseStart_7456419 baseEnd_7456419 := by
    simpa [prefixWord, tailWord_7456419, baseEnd_7456419] using wordTrace_append hprefix tailTrace_7456419
  have hstable : (prefixWord ++ tailWord_7456419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456419).length < 2 ^ (prefixWord ++ tailWord_7456419).sum := by decide
  have hdescent : baseEnd_7456419 < baseStart_7456419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456424 : List Nat := [2, 1, 7, 1, 1, 1, 2, 2, 1, 3, 2]
def baseStart_7456424 : Nat := 118140960795 + 7456424 * 2 ^ 59
def prefixEnd_7456424 : Nat := 4983230072969 + 3 ^ 40 * 7456424 * 2
def baseEnd_7456424 : Nat := 3828729475720439940508537

theorem tailTrace_7456424 : CollatzResearch.WordTrace tailWord_7456424 prefixEnd_7456424 3828729475720439940508537 := by
  unfold tailWord_7456424
  simp only [CollatzResearch.WordTrace]
  refine ⟨135979062769328389339656163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181305417025771185786208217 135979062769328389339656163)
  ·
    refine ⟨203968594153992584009484245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135979062769328389339656163 203968594153992584009484245)
    ·
      refine ⟨4780513925484201187722287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 203968594153992584009484245 4780513925484201187722287)
      ·
        refine ⟨7170770888226301781583431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4780513925484201187722287 7170770888226301781583431)
        ·
          refine ⟨10756156332339452672375147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7170770888226301781583431 10756156332339452672375147)
          ·
            refine ⟨16134234498509179008562721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10756156332339452672375147 16134234498509179008562721)
            ·
              refine ⟨12100675873881884256422041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16134234498509179008562721 12100675873881884256422041)
              ·
                refine ⟨9075506905411413192316531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12100675873881884256422041 9075506905411413192316531)
                ·
                  refine ⟨13613260358117119788474797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9075506905411413192316531 13613260358117119788474797)
                  ·
                    refine ⟨5104972634293919920678049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13613260358117119788474797 5104972634293919920678049)
                    ·
                      refine ⟨3828729475720439940508537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5104972634293919920678049 3828729475720439940508537)
                      ·
                        rfl

theorem cell23_7456424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_7456424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456424 prefixEnd_7456424 := by exact prefixLift 7456424
  have htrace : WordTrace (prefixWord ++ tailWord_7456424) baseStart_7456424 baseEnd_7456424 := by
    simpa [prefixWord, tailWord_7456424, baseEnd_7456424] using wordTrace_append hprefix tailTrace_7456424
  have hstable : (prefixWord ++ tailWord_7456424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456424).length < 2 ^ (prefixWord ++ tailWord_7456424).sum := by decide
  have hdescent : baseEnd_7456424 < baseStart_7456424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456439 : List Nat := [1, 1, 3, 1, 5, 1, 2, 1, 1, 7]
def baseStart_7456439 : Nat := 118140960795 + 7456439 * 2 ^ 59
def prefixEnd_7456439 : Nat := 4983230072969 + 3 ^ 40 * 7456439 * 2
def baseEnd_7456439 : Nat := 1276245725976752460606989

theorem tailTrace_7456439 : CollatzResearch.WordTrace tailWord_7456439 prefixEnd_7456439 1276245725976752460606989 := by
  unfold tailWord_7456439
  simp only [CollatzResearch.WordTrace]
  refine ⟨271958672633602436241108371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181305781755734957494072247 271958672633602436241108371)
  ·
    refine ⟨407938008950403654361662557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271958672633602436241108371 407938008950403654361662557)
    ·
      refine ⟨152976753356401370385623459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407938008950403654361662557 152976753356401370385623459)
      ·
        refine ⟨229465130034602055578435189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152976753356401370385623459 229465130034602055578435189)
        ·
          refine ⟨21512355940743942710478299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 229465130034602055578435189 21512355940743942710478299)
          ·
            refine ⟨32268533911115914065717449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21512355940743942710478299 32268533911115914065717449)
            ·
              refine ⟨24201400433336935549288087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32268533911115914065717449 24201400433336935549288087)
              ·
                refine ⟨36302100650005403323932131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24201400433336935549288087 36302100650005403323932131)
                ·
                  refine ⟨54453150975008104985898197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36302100650005403323932131 54453150975008104985898197)
                  ·
                    refine ⟨1276245725976752460606989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54453150975008104985898197 1276245725976752460606989)
                    ·
                      rfl

theorem cell23_7456439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 7].length) (baseStart_7456439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456439 prefixEnd_7456439 := by exact prefixLift 7456439
  have htrace : WordTrace (prefixWord ++ tailWord_7456439) baseStart_7456439 baseEnd_7456439 := by
    simpa [prefixWord, tailWord_7456439, baseEnd_7456439] using wordTrace_append hprefix tailTrace_7456439
  have hstable : (prefixWord ++ tailWord_7456439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456439).length < 2 ^ (prefixWord ++ tailWord_7456439).sum := by decide
  have hdescent : baseEnd_7456439 < baseStart_7456439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456460 : List Nat := [2, 2, 1, 5, 2, 1, 3, 2, 5]
def baseStart_7456460 : Nat := 118140960795 + 7456460 * 2 ^ 59
def prefixEnd_7456460 : Nat := 4983230072969 + 3 ^ 40 * 7456460 * 2
def baseEnd_7456460 : Nat := 425416440113777977739819

theorem tailTrace_7456460 : CollatzResearch.WordTrace tailWord_7456460 prefixEnd_7456460 425416440113777977739819 := by
  unfold tailWord_7456460
  simp only [CollatzResearch.WordTrace]
  refine ⟨135979719283263178413811417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181306292377684237885081889 135979719283263178413811417)
  ·
    refine ⟨101984789462447383810358563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135979719283263178413811417 101984789462447383810358563)
    ·
      refine ⟨152977184193671075715537845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101984789462447383810358563 152977184193671075715537845)
      ·
        refine ⟨14341611018156663348331673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152977184193671075715537845 14341611018156663348331673)
        ·
          refine ⟨10756208263617497511248755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14341611018156663348331673 10756208263617497511248755)
          ·
            refine ⟨16134312395426246266873133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10756208263617497511248755 16134312395426246266873133)
            ·
              refine ⟨6050367148284842350077425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16134312395426246266873133 6050367148284842350077425)
              ·
                refine ⟨4537775361213631762558069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6050367148284842350077425 4537775361213631762558069)
                ·
                  refine ⟨425416440113777977739819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4537775361213631762558069 425416440113777977739819)
                  ·
                    rfl

theorem cell23_7456460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2, 5].length) (baseStart_7456460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456460 prefixEnd_7456460 := by exact prefixLift 7456460
  have htrace : WordTrace (prefixWord ++ tailWord_7456460) baseStart_7456460 baseEnd_7456460 := by
    simpa [prefixWord, tailWord_7456460, baseEnd_7456460] using wordTrace_append hprefix tailTrace_7456460
  have hstable : (prefixWord ++ tailWord_7456460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456460).length < 2 ^ (prefixWord ++ tailWord_7456460).sum := by decide
  have hdescent : baseEnd_7456460 < baseStart_7456460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456466 : List Nat := [3, 2, 2, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_7456466 : Nat := 118140960795 + 7456466 * 2 ^ 59
def prefixEnd_7456466 : Nat := 4983230072969 + 3 ^ 40 * 7456466 * 2
def baseEnd_7456466 : Nat := 3828751041907928776183343

theorem tailTrace_7456466 : CollatzResearch.WordTrace tailWord_7456466 prefixEnd_7456466 3828751041907928776183343 := by
  unfold tailWord_7456466
  simp only [CollatzResearch.WordTrace]
  refine ⟨67989914351126154963085313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181306438269669746568227501 67989914351126154963085313)
  ·
    refine ⟨50992435763344616222313985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67989914351126154963085313 50992435763344616222313985)
    ·
      refine ⟨38244326822508462166735489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50992435763344616222313985 38244326822508462166735489)
      ·
        refine ⟨28683245116881346625051617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38244326822508462166735489 28683245116881346625051617)
        ·
          refine ⟨21512433837661009968788713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28683245116881346625051617 21512433837661009968788713)
          ·
            refine ⟨16134325378245757476591535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21512433837661009968788713 16134325378245757476591535)
            ·
              refine ⟨24201488067368636214887303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16134325378245757476591535 24201488067368636214887303)
              ·
                refine ⟨36302232101052954322330955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24201488067368636214887303 36302232101052954322330955)
                ·
                  refine ⟨54453348151579431483496433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36302232101052954322330955 54453348151579431483496433)
                  ·
                    refine ⟨40840011113684573612622325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54453348151579431483496433 40840011113684573612622325)
                    ·
                      refine ⟨3828751041907928776183343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40840011113684573612622325 3828751041907928776183343)
                      ·
                        rfl

theorem cell23_7456466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_7456466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456466 prefixEnd_7456466 := by exact prefixLift 7456466
  have htrace : WordTrace (prefixWord ++ tailWord_7456466) baseStart_7456466 baseEnd_7456466 := by
    simpa [prefixWord, tailWord_7456466, baseEnd_7456466] using wordTrace_append hprefix tailTrace_7456466
  have hstable : (prefixWord ++ tailWord_7456466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456466).length < 2 ^ (prefixWord ++ tailWord_7456466).sum := by decide
  have hdescent : baseEnd_7456466 < baseStart_7456466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456493 : List Nat := [1, 5, 1, 2, 1, 3, 2, 1, 2, 1, 4]
def baseStart_7456493 : Nat := 118140960795 + 7456493 * 2 ^ 59
def prefixEnd_7456493 : Nat := 4983230072969 + 3 ^ 40 * 7456493 * 2
def baseEnd_7456493 : Nat := 3828764905885600170545719

theorem tailTrace_7456493 : CollatzResearch.WordTrace tailWord_7456493 prefixEnd_7456493 3828764905885600170545719 := by
  unfold tailWord_7456493
  simp only [CollatzResearch.WordTrace]
  refine ⟨271960642175406803463574133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181307094783604535642382755 271960642175406803463574133)
  ·
    refine ⟨25496310203944387824710075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 271960642175406803463574133 25496310203944387824710075)
    ·
      refine ⟨38244465305916581737065113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25496310203944387824710075 38244465305916581737065113)
      ·
        refine ⟨28683348979437436302798835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38244465305916581737065113 28683348979437436302798835)
        ·
          refine ⟨43025023469156154454198253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28683348979437436302798835 43025023469156154454198253)
          ·
            refine ⟨16134383800933557920324345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43025023469156154454198253 16134383800933557920324345)
            ·
              refine ⟨12100787850700168440243259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16134383800933557920324345 12100787850700168440243259)
              ·
                refine ⟨18151181776050252660364889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12100787850700168440243259 18151181776050252660364889)
                ·
                  refine ⟨13613386332037689495273667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18151181776050252660364889 13613386332037689495273667)
                  ·
                    refine ⟨20420079498056534242910501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13613386332037689495273667 20420079498056534242910501)
                    ·
                      refine ⟨3828764905885600170545719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20420079498056534242910501 3828764905885600170545719)
                      ·
                        rfl

theorem cell23_7456493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_7456493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456493 prefixEnd_7456493 := by exact prefixLift 7456493
  have htrace : WordTrace (prefixWord ++ tailWord_7456493) baseStart_7456493 baseEnd_7456493 := by
    simpa [prefixWord, tailWord_7456493, baseEnd_7456493] using wordTrace_append hprefix tailTrace_7456493
  have hstable : (prefixWord ++ tailWord_7456493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456493).length < 2 ^ (prefixWord ++ tailWord_7456493).sum := by decide
  have hdescent : baseEnd_7456493 < baseStart_7456493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456516 : List Nat := [2, 3, 2, 2, 1, 2, 1, 4, 6]
def baseStart_7456516 : Nat := 118140960795 + 7456516 * 2 ^ 59
def prefixEnd_7456516 : Nat := 4983230072969 + 3 ^ 40 * 7456516 * 2
def baseEnd_7456516 : Nat := 425419635104517064506457

theorem tailTrace_7456516 : CollatzResearch.WordTrace tailWord_7456516 prefixEnd_7456516 425419635104517064506457 := by
  unfold tailWord_7456516
  simp only [CollatzResearch.WordTrace]
  refine ⟨135980740527161739195830701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181307654036215652261107601 135980740527161739195830701)
  ·
    refine ⟨50992777697685652198436513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135980740527161739195830701 50992777697685652198436513)
    ·
      refine ⟨38244583273264239148827385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50992777697685652198436513 38244583273264239148827385)
      ·
        refine ⟨28683437454948179361620539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38244583273264239148827385 28683437454948179361620539)
        ·
          refine ⟨43025156182422269042430809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28683437454948179361620539 43025156182422269042430809)
          ·
            refine ⟨32268867136816701781823107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43025156182422269042430809 32268867136816701781823107)
            ·
              refine ⟨48403300705225052672734661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32268867136816701781823107 48403300705225052672734661)
              ·
                refine ⟨9075618882229697376137749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48403300705225052672734661 9075618882229697376137749)
                ·
                  refine ⟨425419635104517064506457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9075618882229697376137749 425419635104517064506457)
                  ·
                    rfl

theorem cell23_7456516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 6].length) (baseStart_7456516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456516 prefixEnd_7456516 := by exact prefixLift 7456516
  have htrace : WordTrace (prefixWord ++ tailWord_7456516) baseStart_7456516 baseEnd_7456516 := by
    simpa [prefixWord, tailWord_7456516, baseEnd_7456516] using wordTrace_append hprefix tailTrace_7456516
  have hstable : (prefixWord ++ tailWord_7456516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456516).length < 2 ^ (prefixWord ++ tailWord_7456516).sum := by decide
  have hdescent : baseEnd_7456516 < baseStart_7456516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456543 : List Nat := [1, 1, 2, 4, 2, 1, 3, 2, 3, 1, 3]
def baseStart_7456543 : Nat := 118140960795 + 7456543 * 2 ^ 59
def prefixEnd_7456543 : Nat := 4983230072969 + 3 ^ 40 * 7456543 * 2
def baseEnd_7456543 : Nat := 3828790579918324974920489

theorem tailTrace_7456543 : CollatzResearch.WordTrace tailWord_7456543 prefixEnd_7456543 3828790579918324974920489 := by
  unfold tailWord_7456543
  simp only [CollatzResearch.WordTrace]
  refine ⟨271962465825225662002894283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181308310550150441335262855 271962465825225662002894283)
  ·
    refine ⟨407943698737838493004341425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271962465825225662002894283 407943698737838493004341425)
    ·
      refine ⟨305957774053378869753256069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407943698737838493004341425 305957774053378869753256069)
      ·
        refine ⟨57367082635008538078735513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305957774053378869753256069 57367082635008538078735513)
        ·
          refine ⟨43025311976256403559051635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57367082635008538078735513 43025311976256403559051635)
          ·
            refine ⟨64537967964384605338577453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43025311976256403559051635 64537967964384605338577453)
            ·
              refine ⟨24201737986644227001966545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64537967964384605338577453 24201737986644227001966545)
              ·
                refine ⟨18151303489983170251474909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24201737986644227001966545 18151303489983170251474909)
                ·
                  refine ⟨6806738808743688844303091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18151303489983170251474909 6806738808743688844303091)
                  ·
                    refine ⟨10210108213115533266454637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6806738808743688844303091 10210108213115533266454637)
                    ·
                      refine ⟨3828790579918324974920489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10210108213115533266454637 3828790579918324974920489)
                      ·
                        rfl

theorem cell23_7456543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_7456543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456543 prefixEnd_7456543 := by exact prefixLift 7456543
  have htrace : WordTrace (prefixWord ++ tailWord_7456543) baseStart_7456543 baseEnd_7456543 := by
    simpa [prefixWord, tailWord_7456543, baseEnd_7456543] using wordTrace_append hprefix tailTrace_7456543
  have hstable : (prefixWord ++ tailWord_7456543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456543).length < 2 ^ (prefixWord ++ tailWord_7456543).sum := by decide
  have hdescent : baseEnd_7456543 < baseStart_7456543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456546 : List Nat := [3, 3, 1, 1, 2, 1, 1, 3, 3, 5]
def baseStart_7456546 : Nat := 118140960795 + 7456546 * 2 ^ 59
def prefixEnd_7456546 : Nat := 4983230072969 + 3 ^ 40 * 7456546 * 2
def baseEnd_7456546 : Nat := 1276264040120096154394325

theorem tailTrace_7456546 : CollatzResearch.WordTrace tailWord_7456546 prefixEnd_7456546 1276264040120096154394325 := by
  unfold tailWord_7456546
  simp only [CollatzResearch.WordTrace]
  refine ⟨67990643811053698378813373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181308383496143195676835661 67990643811053698378813373)
  ·
    refine ⟨25496491429145136892055015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67990643811053698378813373 25496491429145136892055015)
    ·
      refine ⟨38244737143717705338082523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25496491429145136892055015 38244737143717705338082523)
      ·
        refine ⟨57367105715576558007123785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38244737143717705338082523 57367105715576558007123785)
        ·
          refine ⟨43025329286682418505342839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57367105715576558007123785 43025329286682418505342839)
          ·
            refine ⟨64537993930023627758014259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43025329286682418505342839 64537993930023627758014259)
            ·
              refine ⟨96806990895035441637021389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64537993930023627758014259 96806990895035441637021389)
              ·
                refine ⟨36302621585638290613883021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96806990895035441637021389 36302621585638290613883021)
                ·
                  refine ⟨13613483094614358980206133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36302621585638290613883021 13613483094614358980206133)
                  ·
                    refine ⟨1276264040120096154394325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13613483094614358980206133 1276264040120096154394325)
                    ·
                      rfl

theorem cell23_7456546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_7456546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456546 prefixEnd_7456546 := by exact prefixLift 7456546
  have htrace : WordTrace (prefixWord ++ tailWord_7456546) baseStart_7456546 baseEnd_7456546 := by
    simpa [prefixWord, tailWord_7456546, baseEnd_7456546] using wordTrace_append hprefix tailTrace_7456546
  have hstable : (prefixWord ++ tailWord_7456546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456546).length < 2 ^ (prefixWord ++ tailWord_7456546).sum := by decide
  have hdescent : baseEnd_7456546 < baseStart_7456546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456563 : List Nat := [1, 1, 1, 2, 7, 1, 1, 3, 1, 5]
def baseStart_7456563 : Nat := 118140960795 + 7456563 * 2 ^ 59
def prefixEnd_7456563 : Nat := 4983230072969 + 3 ^ 40 * 7456563 * 2
def baseEnd_7456563 : Nat := 1276266949843804965556799

theorem tailTrace_7456563 : CollatzResearch.WordTrace tailWord_7456563 prefixEnd_7456563 1276266949843804965556799 := by
  unfold tailWord_7456563
  simp only [CollatzResearch.WordTrace]
  refine ⟨271963195285153205418622343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181308796856768803612414895 271963195285153205418622343)
  ·
    refine ⟨407944792927729808127933515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271963195285153205418622343 407944792927729808127933515)
    ·
      refine ⟨611917189391594712191900273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407944792927729808127933515 611917189391594712191900273)
      ·
        refine ⟨458937892043696034143925205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 611917189391594712191900273 458937892043696034143925205)
        ·
          refine ⟨10756356844774125800248247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 458937892043696034143925205 10756356844774125800248247)
          ·
            refine ⟨16134535267161188700372371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10756356844774125800248247 16134535267161188700372371)
            ·
              refine ⟨24201802900741783050558557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16134535267161188700372371 24201802900741783050558557)
              ·
                refine ⟨9075676087778168643959459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24201802900741783050558557 9075676087778168643959459)
                ·
                  refine ⟨13613514131667252965939189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9075676087778168643959459 13613514131667252965939189)
                  ·
                    refine ⟨1276266949843804965556799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13613514131667252965939189 1276266949843804965556799)
                    ·
                      rfl

theorem cell23_7456563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 5].length) (baseStart_7456563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456563 prefixEnd_7456563 := by exact prefixLift 7456563
  have htrace : WordTrace (prefixWord ++ tailWord_7456563) baseStart_7456563 baseEnd_7456563 := by
    simpa [prefixWord, tailWord_7456563, baseEnd_7456563] using wordTrace_append hprefix tailTrace_7456563
  have hstable : (prefixWord ++ tailWord_7456563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456563).length < 2 ^ (prefixWord ++ tailWord_7456563).sum := by decide
  have hdescent : baseEnd_7456563 < baseStart_7456563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456586 : List Nat := [3, 1, 2, 1, 1, 1, 5, 2, 1, 1, 5]
def baseStart_7456586 : Nat := 118140960795 + 7456586 * 2 ^ 59
def prefixEnd_7456586 : Nat := 4983230072969 + 3 ^ 40 * 7456586 * 2
def baseEnd_7456586 : Nat := 3828812659586468306682791

theorem tailTrace_7456586 : CollatzResearch.WordTrace tailWord_7456586 prefixEnd_7456586 3828812659586468306682791 := by
  unfold tailWord_7456586
  simp only [CollatzResearch.WordTrace]
  refine ⟨67991008541017470086677403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181309356109379920231139741 67991008541017470086677403)
  ·
    refine ⟨101986512811526205130016105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67991008541017470086677403 101986512811526205130016105)
    ·
      refine ⟨76489884608644653847512079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101986512811526205130016105 76489884608644653847512079)
      ·
        refine ⟨114734826912966980771268119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76489884608644653847512079 114734826912966980771268119)
        ·
          refine ⟨172102240369450471156902179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114734826912966980771268119 172102240369450471156902179)
          ·
            refine ⟨258153360554175706735353269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172102240369450471156902179 258153360554175706735353269)
            ·
              refine ⟨24201877551953972506439369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 258153360554175706735353269 24201877551953972506439369)
              ·
                refine ⟨18151408163965479379829527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24201877551953972506439369 18151408163965479379829527)
                ·
                  refine ⟨27227112245948219069744291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18151408163965479379829527 27227112245948219069744291)
                  ·
                    refine ⟨40840668368922328604616437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27227112245948219069744291 40840668368922328604616437)
                    ·
                      refine ⟨3828812659586468306682791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40840668368922328604616437 3828812659586468306682791)
                      ·
                        rfl

theorem cell23_7456586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_7456586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456586 prefixEnd_7456586 := by exact prefixLift 7456586
  have htrace : WordTrace (prefixWord ++ tailWord_7456586) baseStart_7456586 baseEnd_7456586 := by
    simpa [prefixWord, tailWord_7456586, baseEnd_7456586] using wordTrace_append hprefix tailTrace_7456586
  have hstable : (prefixWord ++ tailWord_7456586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456586).length < 2 ^ (prefixWord ++ tailWord_7456586).sum := by decide
  have hdescent : baseEnd_7456586 < baseStart_7456586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456593 : List Nat := [1, 2, 2, 1, 5, 3, 1, 1, 1, 6]
def baseStart_7456593 : Nat := 118140960795 + 7456593 * 2 ^ 59
def prefixEnd_7456593 : Nat := 4983230072969 + 3 ^ 40 * 7456593 * 2
def baseEnd_7456593 : Nat := 1276272084650349926431753

theorem tailTrace_7456593 : CollatzResearch.WordTrace tailWord_7456593 prefixEnd_7456593 1276272084650349926431753 := by
  unfold tailWord_7456593
  simp only [CollatzResearch.WordTrace]
  refine ⟨271964289475044520542214433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181309526316696347028142955 271964289475044520542214433)
  ·
    refine ⟨203973217106283390406660825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271964289475044520542214433 203973217106283390406660825)
    ·
      refine ⟨152979912829712542804995619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203973217106283390406660825 152979912829712542804995619)
      ·
        refine ⟨229469869244568814207493429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152979912829712542804995619 229469869244568814207493429)
        ·
          refine ⟨21512800241678326331952509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 229469869244568814207493429 21512800241678326331952509)
          ·
            refine ⟨8067300090629372374482191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21512800241678326331952509 8067300090629372374482191)
            ·
              refine ⟨12100950135944058561723287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8067300090629372374482191 12100950135944058561723287)
              ·
                refine ⟨18151425203916087842584931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12100950135944058561723287 18151425203916087842584931)
                ·
                  refine ⟨27227137805874131763877397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18151425203916087842584931 27227137805874131763877397)
                  ·
                    refine ⟨1276272084650349926431753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27227137805874131763877397 1276272084650349926431753)
                    ·
                      rfl

theorem cell23_7456593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 6].length) (baseStart_7456593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456593 prefixEnd_7456593 := by exact prefixLift 7456593
  have htrace : WordTrace (prefixWord ++ tailWord_7456593) baseStart_7456593 baseEnd_7456593 := by
    simpa [prefixWord, tailWord_7456593, baseEnd_7456593] using wordTrace_append hprefix tailTrace_7456593
  have hstable : (prefixWord ++ tailWord_7456593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456593).length < 2 ^ (prefixWord ++ tailWord_7456593).sum := by decide
  have hdescent : baseEnd_7456593 < baseStart_7456593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456619 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 1, 9]
def baseStart_7456619 : Nat := 118140960795 + 7456619 * 2 ^ 59
def prefixEnd_7456619 : Nat := 4983230072969 + 3 ^ 40 * 7456619 * 2
def baseEnd_7456619 : Nat := 1276276534816022225856713

theorem tailTrace_7456619 : CollatzResearch.WordTrace tailWord_7456619 prefixEnd_7456619 1276276534816022225856713 := by
  unfold tailWord_7456619
  simp only [CollatzResearch.WordTrace]
  refine ⟨271965237772950326982660911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181310158515300217988440607 271965237772950326982660911)
  ·
    refine ⟨407947856659425490473991367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271965237772950326982660911 407947856659425490473991367)
    ·
      refine ⟨611921784989138235710987051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407947856659425490473991367 611921784989138235710987051)
      ·
        refine ⟨917882677483707353566480577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611921784989138235710987051 917882677483707353566480577)
        ·
          refine ⟨688412008112780515174860433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 917882677483707353566480577 688412008112780515174860433)
          ·
            refine ⟨516309006084585386381145325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 688412008112780515174860433 516309006084585386381145325)
            ·
              refine ⟨193615877281719519892929497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 516309006084585386381145325 193615877281719519892929497)
              ·
                refine ⟨145211907961289639919697123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193615877281719519892929497 145211907961289639919697123)
                ·
                  refine ⟨217817861941934459879545685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145211907961289639919697123 217817861941934459879545685)
                  ·
                    refine ⟨1276276534816022225856713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 217817861941934459879545685 1276276534816022225856713)
                    ·
                      rfl

theorem cell23_7456619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 9].length) (baseStart_7456619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456619 prefixEnd_7456619 := by exact prefixLift 7456619
  have htrace : WordTrace (prefixWord ++ tailWord_7456619) baseStart_7456619 baseEnd_7456619 := by
    simpa [prefixWord, tailWord_7456619, baseEnd_7456619] using wordTrace_append hprefix tailTrace_7456619
  have hstable : (prefixWord ++ tailWord_7456619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456619).length < 2 ^ (prefixWord ++ tailWord_7456619).sum := by decide
  have hdescent : baseEnd_7456619 < baseStart_7456619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456633 : List Nat := [1, 2, 1, 3, 2, 2, 1, 3, 4, 1, 3]
def baseStart_7456633 : Nat := 118140960795 + 7456633 * 2 ^ 59
def prefixEnd_7456633 : Nat := 4983230072969 + 3 ^ 40 * 7456633 * 2
def baseEnd_7456633 : Nat := 3828836793177229622795075

theorem tailTrace_7456633 : CollatzResearch.WordTrace tailWord_7456633 prefixEnd_7456633 3828836793177229622795075 := by
  unfold tailWord_7456633
  simp only [CollatzResearch.WordTrace]
  refine ⟨271965748394899607373670553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181310498929933071582447035 271965748394899607373670553)
  ·
    refine ⟨203974311296174705530252915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271965748394899607373670553 203974311296174705530252915)
    ·
      refine ⟨305961466944262058295379373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203974311296174705530252915 305961466944262058295379373)
      ·
        refine ⟨114735550104098271860767265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305961466944262058295379373 114735550104098271860767265)
        ·
          refine ⟨86051662578073703895575449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114735550104098271860767265 86051662578073703895575449)
          ·
            refine ⟨64538746933555277921681587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86051662578073703895575449 64538746933555277921681587)
            ·
              refine ⟨96808120400332916882522381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64538746933555277921681587 96808120400332916882522381)
              ·
                refine ⟨36303045150124843830945893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96808120400332916882522381 36303045150124843830945893)
                ·
                  refine ⟨6806820965648408218302355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36303045150124843830945893 6806820965648408218302355)
                  ·
                    refine ⟨10210231448472612327453533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6806820965648408218302355 10210231448472612327453533)
                    ·
                      refine ⟨3828836793177229622795075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10210231448472612327453533 3828836793177229622795075)
                      ·
                        rfl

theorem cell23_7456633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_7456633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456633 prefixEnd_7456633 := by exact prefixLift 7456633
  have htrace : WordTrace (prefixWord ++ tailWord_7456633) baseStart_7456633 baseEnd_7456633 := by
    simpa [prefixWord, tailWord_7456633, baseEnd_7456633] using wordTrace_append hprefix tailTrace_7456633
  have hstable : (prefixWord ++ tailWord_7456633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456633).length < 2 ^ (prefixWord ++ tailWord_7456633).sum := by decide
  have hdescent : baseEnd_7456633 < baseStart_7456633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456654 : List Nat := [4, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3]
def baseStart_7456654 : Nat := 118140960795 + 7456654 * 2 ^ 59
def prefixEnd_7456654 : Nat := 4983230072969 + 3 ^ 40 * 7456654 * 2
def baseEnd_7456654 : Nat := 3828847576270974040632479

theorem tailTrace_7456654 : CollatzResearch.WordTrace tailWord_7456654 prefixEnd_7456654 3828847576270974040632479 := by
  unfold tailWord_7456654
  simp only [CollatzResearch.WordTrace]
  refine ⟨33995814290977940995023127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181311009551882351973456677 33995814290977940995023127)
  ·
    refine ⟨50993721436466911492534691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33995814290977940995023127 50993721436466911492534691)
    ·
      refine ⟨76490582154700367238802037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50993721436466911492534691 76490582154700367238802037)
      ·
        refine ⟨7170992077003159428637691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76490582154700367238802037 7170992077003159428637691)
        ·
          refine ⟨10756488115504739142956537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7170992077003159428637691 10756488115504739142956537)
          ·
            refine ⟨8067366086628554357217403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10756488115504739142956537 8067366086628554357217403)
            ·
              refine ⟨12101049129942831535826105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8067366086628554357217403 12101049129942831535826105)
              ·
                refine ⟨9075786847457123651869579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12101049129942831535826105 9075786847457123651869579)
                ·
                  refine ⟨13613680271185685477804369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9075786847457123651869579 13613680271185685477804369)
                  ·
                    refine ⟨10210260203389264108353277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13613680271185685477804369 10210260203389264108353277)
                    ·
                      refine ⟨3828847576270974040632479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10210260203389264108353277 3828847576270974040632479)
                      ·
                        rfl

theorem cell23_7456654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_7456654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456654 prefixEnd_7456654 := by exact prefixLift 7456654
  have htrace : WordTrace (prefixWord ++ tailWord_7456654) baseStart_7456654 baseEnd_7456654 := by
    simpa [prefixWord, tailWord_7456654, baseEnd_7456654] using wordTrace_append hprefix tailTrace_7456654
  have hstable : (prefixWord ++ tailWord_7456654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456654).length < 2 ^ (prefixWord ++ tailWord_7456654).sum := by decide
  have hdescent : baseEnd_7456654 < baseStart_7456654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456690 : List Nat := [3, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2]
def baseStart_7456690 : Nat := 118140960795 + 7456690 * 2 ^ 59
def prefixEnd_7456690 : Nat := 4983230072969 + 3 ^ 40 * 7456690 * 2
def baseEnd_7456690 : Nat := 3828866061574535899782313

theorem tailTrace_7456690 : CollatzResearch.WordTrace tailWord_7456690 prefixEnd_7456690 3828866061574535899782313 := by
  unfold tailWord_7456690
  simp only [CollatzResearch.WordTrace]
  refine ⟨67991956838923276527123881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181311884903795404072330349 67991956838923276527123881)
  ·
    refine ⟨50993967629192457395342911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67991956838923276527123881 50993967629192457395342911)
    ·
      refine ⟨76490951443788686093014367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50993967629192457395342911 76490951443788686093014367)
      ·
        refine ⟨114736427165683029139521551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76490951443788686093014367 114736427165683029139521551)
        ·
          refine ⟨172104640748524543709282327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114736427165683029139521551 172104640748524543709282327)
          ·
            refine ⟨258156961122786815563923491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172104640748524543709282327 258156961122786815563923491)
            ·
              refine ⟨387235441684180223345885237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258156961122786815563923491 387235441684180223345885237)
              ·
                refine ⟨36303322657891895938676741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 387235441684180223345885237 36303322657891895938676741)
                ·
                  refine ⟨6806872998354730488501889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36303322657891895938676741 6806872998354730488501889)
                  ·
                    refine ⟨5105154748766047866376417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6806872998354730488501889 5105154748766047866376417)
                    ·
                      refine ⟨3828866061574535899782313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5105154748766047866376417 3828866061574535899782313)
                      ·
                        rfl

theorem cell23_7456690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2].length) (baseStart_7456690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456690 prefixEnd_7456690 := by exact prefixLift 7456690
  have htrace : WordTrace (prefixWord ++ tailWord_7456690) baseStart_7456690 baseEnd_7456690 := by
    simpa [prefixWord, tailWord_7456690, baseEnd_7456690] using wordTrace_append hprefix tailTrace_7456690
  have hstable : (prefixWord ++ tailWord_7456690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456690).length < 2 ^ (prefixWord ++ tailWord_7456690).sum := by decide
  have hdescent : baseEnd_7456690 < baseStart_7456690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456693 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 2, 4, 3]
def baseStart_7456693 : Nat := 118140960795 + 7456693 * 2 ^ 59
def prefixEnd_7456693 : Nat := 4983230072969 + 3 ^ 40 * 7456693 * 2
def baseEnd_7456693 : Nat := 3828867602016499388044799

theorem tailTrace_7456693 : CollatzResearch.WordTrace tailWord_7456693 prefixEnd_7456693 3828867602016499388044799 := by
  unfold tailWord_7456693
  simp only [CollatzResearch.WordTrace]
  refine ⟨271967936774682237620854733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181311957849788158413903155 271967936774682237620854733)
  ·
    refine ⟨101987976290505839107820525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271967936774682237620854733 101987976290505839107820525)
    ·
      refine ⟨38245491108939689665432697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101987976290505839107820525 38245491108939689665432697)
      ·
        refine ⟨28684118331704767249074523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38245491108939689665432697 28684118331704767249074523)
        ·
          refine ⟨43026177497557150873611785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28684118331704767249074523 43026177497557150873611785)
          ·
            refine ⟨32269633123167863155208839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43026177497557150873611785 32269633123167863155208839)
            ·
              refine ⟨48404449684751794732813259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32269633123167863155208839 48404449684751794732813259)
              ·
                refine ⟨72606674527127692099219889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48404449684751794732813259 72606674527127692099219889)
                ·
                  refine ⟨54455005895345769074414917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72606674527127692099219889 54455005895345769074414917)
                  ·
                    refine ⟨10210313605377331701452797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54455005895345769074414917 10210313605377331701452797)
                    ·
                      refine ⟨3828867602016499388044799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10210313605377331701452797 3828867602016499388044799)
                      ·
                        rfl

theorem cell23_7456693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_7456693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456693 prefixEnd_7456693 := by exact prefixLift 7456693
  have htrace : WordTrace (prefixWord ++ tailWord_7456693) baseStart_7456693 baseEnd_7456693 := by
    simpa [prefixWord, tailWord_7456693, baseEnd_7456693] using wordTrace_append hprefix tailTrace_7456693
  have hstable : (prefixWord ++ tailWord_7456693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456693).length < 2 ^ (prefixWord ++ tailWord_7456693).sum := by decide
  have hdescent : baseEnd_7456693 < baseStart_7456693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456696 : List Nat := [2, 1, 2, 1, 2, 3, 2, 3, 7]
def baseStart_7456696 : Nat := 118140960795 + 7456696 * 2 ^ 59
def prefixEnd_7456696 : Nat := 4983230072969 + 3 ^ 40 * 7456696 * 2
def baseEnd_7456696 : Nat := 425429904717606986256365

theorem tailTrace_7456696 : CollatzResearch.WordTrace tailWord_7456696 prefixEnd_7456696 425429904717606986256365 := by
  unfold tailWord_7456696
  simp only [CollatzResearch.WordTrace]
  refine ⟨135984023096835684566606971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181312030795780912755475961 135984023096835684566606971)
  ·
    refine ⟨203976034645253526849910457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135984023096835684566606971 203976034645253526849910457)
    ·
      refine ⟨152982025983940145137432843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203976034645253526849910457 152982025983940145137432843)
      ·
        refine ⟨229473038975910217706149265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152982025983940145137432843 229473038975910217706149265)
        ·
          refine ⟨172104779231932663279611949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229473038975910217706149265 172104779231932663279611949)
          ·
            refine ⟨64539292211974748729854481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172104779231932663279611949 64539292211974748729854481)
            ·
              refine ⟨48404469158981061547390861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64539292211974748729854481 48404469158981061547390861)
              ·
                refine ⟨18151675934617898080271573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48404469158981061547390861 18151675934617898080271573)
                ·
                  refine ⟨425429904717606986256365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18151675934617898080271573 425429904717606986256365)
                  ·
                    rfl

theorem cell23_7456696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 7].length) (baseStart_7456696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456696 prefixEnd_7456696 := by exact prefixLift 7456696
  have htrace : WordTrace (prefixWord ++ tailWord_7456696) baseStart_7456696 baseEnd_7456696 := by
    simpa [prefixWord, tailWord_7456696, baseEnd_7456696] using wordTrace_append hprefix tailTrace_7456696
  have hstable : (prefixWord ++ tailWord_7456696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456696).length < 2 ^ (prefixWord ++ tailWord_7456696).sum := by decide
  have hdescent : baseEnd_7456696 < baseStart_7456696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456700 : List Nat := [2, 2, 2, 5, 1, 1, 1, 1, 2, 6]
def baseStart_7456700 : Nat := 118140960795 + 7456700 * 2 ^ 59
def prefixEnd_7456700 : Nat := 4983230072969 + 3 ^ 40 * 7456700 * 2
def baseEnd_7456700 : Nat := 1276290398793693620219089

theorem tailTrace_7456700 : CollatzResearch.WordTrace tailWord_7456700 prefixEnd_7456700 1276290398793693620219089 := by
  unfold tailWord_7456700
  simp only [CollatzResearch.WordTrace]
  refine ⟨135984096042828438908179777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181312128057104585210906369 135984096042828438908179777)
  ·
    refine ⟨101988072032121329181134833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135984096042828438908179777 101988072032121329181134833)
    ·
      refine ⟨76491054024090996885851125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101988072032121329181134833 76491054024090996885851125)
      ·
        refine ⟨7171036314758530958048543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76491054024090996885851125 7171036314758530958048543)
        ·
          refine ⟨10756554472137796437072815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7171036314758530958048543 10756554472137796437072815)
          ·
            refine ⟨16134831708206694655609223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10756554472137796437072815 16134831708206694655609223)
            ·
              refine ⟨24202247562310041983413835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16134831708206694655609223 24202247562310041983413835)
              ·
                refine ⟨36303371343465062975120753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24202247562310041983413835 36303371343465062975120753)
                ·
                  refine ⟨27227528507598797231340565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36303371343465062975120753 27227528507598797231340565)
                  ·
                    refine ⟨1276290398793693620219089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27227528507598797231340565 1276290398793693620219089)
                    ·
                      rfl

theorem cell23_7456700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_7456700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456700 prefixEnd_7456700 := by exact prefixLift 7456700
  have htrace : WordTrace (prefixWord ++ tailWord_7456700) baseStart_7456700 baseEnd_7456700 := by
    simpa [prefixWord, tailWord_7456700, baseEnd_7456700] using wordTrace_append hprefix tailTrace_7456700
  have hstable : (prefixWord ++ tailWord_7456700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456700).length < 2 ^ (prefixWord ++ tailWord_7456700).sum := by decide
  have hdescent : baseEnd_7456700 < baseStart_7456700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456736 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 5]
def baseStart_7456736 : Nat := 118140960795 + 7456736 * 2 ^ 59
def prefixEnd_7456736 : Nat := 4983230072969 + 3 ^ 40 * 7456736 * 2
def baseEnd_7456736 : Nat := 3828889681684642719807101

theorem tailTrace_7456736 : CollatzResearch.WordTrace tailWord_7456736 prefixEnd_7456736 3828889681684642719807101 := by
  unfold tailWord_7456736
  simp only [CollatzResearch.WordTrace]
  refine ⟨135984752556763227982335031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181313003409017637309780041 135984752556763227982335031)
  ·
    refine ⟨203977128835144841973502547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135984752556763227982335031 203977128835144841973502547)
    ·
      refine ⟨305965693252717262960253821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203977128835144841973502547 305965693252717262960253821)
      ·
        refine ⟨114737134969768973610095183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305965693252717262960253821 114737134969768973610095183)
        ·
          refine ⟨172105702454653460415142775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114737134969768973610095183 172105702454653460415142775)
          ·
            refine ⟨258158553681980190622714163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172105702454653460415142775 258158553681980190622714163)
            ·
              refine ⟨387237830522970285934071245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258158553681980190622714163 387237830522970285934071245)
              ·
                refine ⟨145214186446113857225276717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 387237830522970285934071245 145214186446113857225276717)
                ·
                  refine ⟨54455319917292696459478769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145214186446113857225276717 54455319917292696459478769)
                  ·
                    refine ⟨40841489937969522344609077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54455319917292696459478769 40841489937969522344609077)
                    ·
                      refine ⟨3828889681684642719807101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40841489937969522344609077 3828889681684642719807101)
                      ·
                        rfl

theorem cell23_7456736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_7456736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456736 prefixEnd_7456736 := by exact prefixLift 7456736
  have htrace : WordTrace (prefixWord ++ tailWord_7456736) baseStart_7456736 baseEnd_7456736 := by
    simpa [prefixWord, tailWord_7456736, baseEnd_7456736] using wordTrace_append hprefix tailTrace_7456736
  have hstable : (prefixWord ++ tailWord_7456736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456736).length < 2 ^ (prefixWord ++ tailWord_7456736).sum := by decide
  have hdescent : baseEnd_7456736 < baseStart_7456736 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456803 : List Nat := [1, 1, 1, 4, 3, 1, 2, 4, 6]
def baseStart_7456803 : Nat := 118140960795 + 7456803 * 2 ^ 59
def prefixEnd_7456803 : Nat := 4983230072969 + 3 ^ 40 * 7456803 * 2
def baseEnd_7456803 : Nat := 425436009432054884185477

theorem tailTrace_7456803 : CollatzResearch.WordTrace tailWord_7456803 prefixEnd_7456803 425436009432054884185477 := by
  unfold tailWord_7456803
  simp only [CollatzResearch.WordTrace]
  refine ⟨271971948804283726407359063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181314632536189150938239375 271971948804283726407359063)
  ·
    refine ⟨407957923206425589611038595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271971948804283726407359063 407957923206425589611038595)
    ·
      refine ⟨611936884809638384416557893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407957923206425589611038595 611936884809638384416557893)
      ·
        refine ⟨114738165901807197078104605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 611936884809638384416557893 114738165901807197078104605)
        ·
          refine ⟨43026812213177698904289227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114738165901807197078104605 43026812213177698904289227)
          ·
            refine ⟨64540218319766548356433841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43026812213177698904289227 64540218319766548356433841)
            ·
              refine ⟨48405163739824911267325381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64540218319766548356433841 48405163739824911267325381)
              ·
                refine ⟨9075968201217170862623509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48405163739824911267325381 9075968201217170862623509)
                ·
                  refine ⟨425436009432054884185477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9075968201217170862623509 425436009432054884185477)
                  ·
                    rfl

theorem cell23_7456803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 6].length) (baseStart_7456803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456803 prefixEnd_7456803 := by exact prefixLift 7456803
  have htrace : WordTrace (prefixWord ++ tailWord_7456803) baseStart_7456803 baseEnd_7456803 := by
    simpa [prefixWord, tailWord_7456803, baseEnd_7456803] using wordTrace_append hprefix tailTrace_7456803
  have hstable : (prefixWord ++ tailWord_7456803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456803).length < 2 ^ (prefixWord ++ tailWord_7456803).sum := by decide
  have hdescent : baseEnd_7456803 < baseStart_7456803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456854 : List Nat := [5, 2, 2, 1, 1, 2, 2, 2, 6]
def baseStart_7456854 : Nat := 118140960795 + 7456854 * 2 ^ 59
def prefixEnd_7456854 : Nat := 4983230072969 + 3 ^ 40 * 7456854 * 2
def baseEnd_7456854 : Nat := 425438919155763695347951

theorem tailTrace_7456854 : CollatzResearch.WordTrace tailWord_7456854 prefixEnd_7456854 425438919155763695347951 := by
  unfold tailWord_7456854
  simp only [CollatzResearch.WordTrace]
  refine ⟨16998363057943685132341601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181315872618065974744977077 16998363057943685132341601)
  ·
    refine ⟨12748772293457763849256201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16998363057943685132341601 12748772293457763849256201)
    ·
      refine ⟨9561579220093322886942151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12748772293457763849256201 9561579220093322886942151)
      ·
        refine ⟨14342368830139984330413227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9561579220093322886942151 14342368830139984330413227)
        ·
          refine ⟨21513553245209976495619841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14342368830139984330413227 21513553245209976495619841)
          ·
            refine ⟨16135164933907482371714881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21513553245209976495619841 16135164933907482371714881)
            ·
              refine ⟨12101373700430611778786161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16135164933907482371714881 12101373700430611778786161)
              ·
                refine ⟨9076030275322958834089621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12101373700430611778786161 9076030275322958834089621)
                ·
                  refine ⟨425438919155763695347951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9076030275322958834089621 425438919155763695347951)
                  ·
                    rfl

theorem cell23_7456854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_7456854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456854 prefixEnd_7456854 := by exact prefixLift 7456854
  have htrace : WordTrace (prefixWord ++ tailWord_7456854) baseStart_7456854 baseEnd_7456854 := by
    simpa [prefixWord, tailWord_7456854, baseEnd_7456854] using wordTrace_append hprefix tailTrace_7456854
  have hstable : (prefixWord ++ tailWord_7456854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456854).length < 2 ^ (prefixWord ++ tailWord_7456854).sum := by decide
  have hdescent : baseEnd_7456854 < baseStart_7456854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456864 : List Nat := [2, 1, 1, 3, 2, 4, 1, 4, 1, 1, 3]
def baseStart_7456864 : Nat := 118140960795 + 7456864 * 2 ^ 59
def prefixEnd_7456864 : Nat := 4983230072969 + 3 ^ 40 * 7456864 * 2
def baseEnd_7456864 : Nat := 3828955407208418219006513

theorem tailTrace_7456864 : CollatzResearch.WordTrace tailWord_7456864 prefixEnd_7456864 3828955407208418219006513 := by
  unfold tailWord_7456864
  simp only [CollatzResearch.WordTrace]
  refine ⟨135987086828531366912664823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181316115771375155883553097 135987086828531366912664823)
  ·
    refine ⟨203980630242797050368997235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135987086828531366912664823 203980630242797050368997235)
    ·
      refine ⟨305970945364195575553495853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203980630242797050368997235 305970945364195575553495853)
      ·
        refine ⟨114739104511573340832560945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305970945364195575553495853 114739104511573340832560945)
        ·
          refine ⟨86054328383680005624420709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114739104511573340832560945 86054328383680005624420709)
          ·
            refine ⟨16135186571940001054578883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86054328383680005624420709 16135186571940001054578883)
            ·
              refine ⟨24202779857910001581868325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16135186571940001054578883 24202779857910001581868325)
              ·
                refine ⟨4538021223358125296600311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24202779857910001581868325 4538021223358125296600311)
                ·
                  refine ⟨6807031835037187944900467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4538021223358125296600311 6807031835037187944900467)
                  ·
                    refine ⟨10210547752555781917350701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6807031835037187944900467 10210547752555781917350701)
                    ·
                      refine ⟨3828955407208418219006513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10210547752555781917350701 3828955407208418219006513)
                      ·
                        rfl

theorem cell23_7456864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4, 1, 1, 3].length) (baseStart_7456864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456864 prefixEnd_7456864 := by exact prefixLift 7456864
  have htrace : WordTrace (prefixWord ++ tailWord_7456864) baseStart_7456864 baseEnd_7456864 := by
    simpa [prefixWord, tailWord_7456864, baseEnd_7456864] using wordTrace_append hprefix tailTrace_7456864
  have hstable : (prefixWord ++ tailWord_7456864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456864).length < 2 ^ (prefixWord ++ tailWord_7456864).sum := by decide
  have hdescent : baseEnd_7456864 < baseStart_7456864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456873 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 3, 1, 5]
def baseStart_7456873 : Nat := 118140960795 + 7456873 * 2 ^ 59
def prefixEnd_7456873 : Nat := 4983230072969 + 3 ^ 40 * 7456873 * 2
def baseEnd_7456873 : Nat := 3828960028534308683793971

theorem tailTrace_7456873 : CollatzResearch.WordTrace tailWord_7456873 prefixEnd_7456873 3828960028534308683793971 := by
  unfold tailWord_7456873
  simp only [CollatzResearch.WordTrace]
  refine ⟨271974501914030128362407273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181316334609353418908271515 271974501914030128362407273)
  ·
    refine ⟨203980876435522596271805455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271974501914030128362407273 203980876435522596271805455)
    ·
      refine ⟨305971314653283894407708183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203980876435522596271805455 305971314653283894407708183)
      ·
        refine ⟨458956971979925841611562275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305971314653283894407708183 458956971979925841611562275)
        ·
          refine ⟨688435457969888762417343413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458956971979925841611562275 688435457969888762417343413)
          ·
            refine ⟨64540824184677071476625945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 688435457969888762417343413 64540824184677071476625945)
            ·
              refine ⟨48405618138507803607469459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64540824184677071476625945 48405618138507803607469459)
              ·
                refine ⟨72608427207761705411204189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48405618138507803607469459 72608427207761705411204189)
                ·
                  refine ⟨27228160202910639529201571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72608427207761705411204189 27228160202910639529201571)
                  ·
                    refine ⟨40842240304365959293802357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27228160202910639529201571 40842240304365959293802357)
                    ·
                      refine ⟨3828960028534308683793971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40842240304365959293802357 3828960028534308683793971)
                      ·
                        rfl

theorem cell23_7456873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 1, 5].length) (baseStart_7456873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456873 prefixEnd_7456873 := by exact prefixLift 7456873
  have htrace : WordTrace (prefixWord ++ tailWord_7456873) baseStart_7456873 baseEnd_7456873 := by
    simpa [prefixWord, tailWord_7456873, baseEnd_7456873] using wordTrace_append hprefix tailTrace_7456873
  have hstable : (prefixWord ++ tailWord_7456873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456873).length < 2 ^ (prefixWord ++ tailWord_7456873).sum := by decide
  have hdescent : baseEnd_7456873 < baseStart_7456873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7456880 : List Nat := [2, 1, 1, 1, 5, 3, 2, 1, 1, 6]
def baseStart_7456880 : Nat := 118140960795 + 7456880 * 2 ^ 59
def prefixEnd_7456880 : Nat := 4983230072969 + 3 ^ 40 * 7456880 * 2
def baseEnd_7456880 : Nat := 1276321207632963385468813

theorem tailTrace_7456880 : CollatzResearch.WordTrace tailWord_7456880 prefixEnd_7456880 1276321207632963385468813 := by
  unfold tailWord_7456880
  simp only [CollatzResearch.WordTrace]
  refine ⟨135987378612502384278956047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181316504816669845705274729 135987378612502384278956047)
  ·
    refine ⟨203981067918753576418434071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135987378612502384278956047 203981067918753576418434071)
    ·
      refine ⟨305971601878130364627651107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203981067918753576418434071 305971601878130364627651107)
      ·
        refine ⟨458957402817195546941476661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305971601878130364627651107 458957402817195546941476661)
        ·
          refine ⟨43027256514112082525763437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 458957402817195546941476661 43027256514112082525763437)
          ·
            refine ⟨16135221192792030947161289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43027256514112082525763437 16135221192792030947161289)
            ·
              refine ⟨12101415894594023210370967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16135221192792030947161289 12101415894594023210370967)
              ·
                refine ⟨18152123841891034815556451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12101415894594023210370967 18152123841891034815556451)
                ·
                  refine ⟨27228185762836552223334677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18152123841891034815556451 27228185762836552223334677)
                  ·
                    refine ⟨1276321207632963385468813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27228185762836552223334677 1276321207632963385468813)
                    ·
                      rfl

theorem cell23_7456880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 1, 6].length) (baseStart_7456880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7456880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7456880 prefixEnd_7456880 := by exact prefixLift 7456880
  have htrace : WordTrace (prefixWord ++ tailWord_7456880) baseStart_7456880 baseEnd_7456880 := by
    simpa [prefixWord, tailWord_7456880, baseEnd_7456880] using wordTrace_append hprefix tailTrace_7456880
  have hstable : (prefixWord ++ tailWord_7456880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7456880).length < 2 ^ (prefixWord ++ tailWord_7456880).sum := by decide
  have hdescent : baseEnd_7456880 < baseStart_7456880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7456880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
