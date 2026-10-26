import V185TrunkScan23Chunk0296

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1756212 : List Nat := [2, 5, 1, 2, 1, 3, 2, 2, 1, 2, 2]
def baseStart_1756212 : Nat := 118140960795 + 1756212 * 2 ^ 59
def prefixEnd_1756212 : Nat := 4983230072969 + 3 ^ 40 * 1756212 * 2
def baseEnd_1756212 : Nat := 901780887193988046173335

theorem tailTrace_1756212 : CollatzResearch.WordTrace tailWord_1756212 prefixEnd_1756212 901780887193988046173335 := by
  unfold tailWord_1756212
  simp only [CollatzResearch.WordTrace]
  refine ⟨32027156956775667987747445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42702875942367557316996593 32027156956775667987747445)
  ·
    refine ⟨3002545964697718873851323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32027156956775667987747445 3002545964697718873851323)
    ·
      refine ⟨4503818947046578310776985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3002545964697718873851323 4503818947046578310776985)
      ·
        refine ⟨3377864210284933733082739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4503818947046578310776985 3377864210284933733082739)
        ·
          refine ⟨5066796315427400599624109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3377864210284933733082739 5066796315427400599624109)
          ·
            refine ⟨1900048618285275224859041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5066796315427400599624109 1900048618285275224859041)
            ·
              refine ⟨1425036463713956418644281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1900048618285275224859041 1425036463713956418644281)
              ·
                refine ⟨1068777347785467313983211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1425036463713956418644281 1068777347785467313983211)
                ·
                  refine ⟨1603166021678200970974817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1068777347785467313983211 1603166021678200970974817)
                  ·
                    refine ⟨1202374516258650728231113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1603166021678200970974817 1202374516258650728231113)
                    ·
                      refine ⟨901780887193988046173335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1202374516258650728231113 901780887193988046173335)
                      ·
                        rfl

theorem cell23_1756212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_1756212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756212 prefixEnd_1756212 := by exact prefixLift 1756212
  have htrace : WordTrace (prefixWord ++ tailWord_1756212) baseStart_1756212 baseEnd_1756212 := by
    simpa [prefixWord, tailWord_1756212, baseEnd_1756212] using wordTrace_append hprefix tailTrace_1756212
  have hstable : (prefixWord ++ tailWord_1756212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756212).length < 2 ^ (prefixWord ++ tailWord_1756212).sum := by decide
  have hdescent : baseEnd_1756212 < baseStart_1756212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756257 : List Nat := [1, 2, 3, 1, 1, 2, 3, 5, 5]
def baseStart_1756257 : Nat := 118140960795 + 1756257 * 2 ^ 59
def prefixEnd_1756257 : Nat := 4983230072969 + 3 ^ 40 * 1756257 * 2
def baseEnd_1756257 : Nat := 100200443758160041123403

theorem tailTrace_1756257 : CollatzResearch.WordTrace tailWord_1756257 prefixEnd_1756257 100200443758160041123403 := by
  unfold tailWord_1756257
  simp only [CollatzResearch.WordTrace]
  refine ⟨64055955198388308660883025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42703970132258872440588683 64055955198388308660883025)
  ·
    refine ⟨48041966398791231495662269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64055955198388308660883025 48041966398791231495662269)
    ·
      refine ⟨18015737399546711810873351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48041966398791231495662269 18015737399546711810873351)
      ·
        refine ⟨27023606099320067716310027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18015737399546711810873351 27023606099320067716310027)
        ·
          refine ⟨40535409148980101574465041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27023606099320067716310027 40535409148980101574465041)
          ·
            refine ⟨30401556861735076180848781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40535409148980101574465041 30401556861735076180848781)
            ·
              refine ⟨11400583823150653567818293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30401556861735076180848781 11400583823150653567818293)
              ·
                refine ⟨1068804733420373771982965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11400583823150653567818293 1068804733420373771982965)
                ·
                  refine ⟨100200443758160041123403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1068804733420373771982965 100200443758160041123403)
                  ·
                    rfl

theorem cell23_1756257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5, 5].length) (baseStart_1756257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756257 prefixEnd_1756257 := by exact prefixLift 1756257
  have htrace : WordTrace (prefixWord ++ tailWord_1756257) baseStart_1756257 baseEnd_1756257 := by
    simpa [prefixWord, tailWord_1756257, baseEnd_1756257] using wordTrace_append hprefix tailTrace_1756257
  have hstable : (prefixWord ++ tailWord_1756257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756257).length < 2 ^ (prefixWord ++ tailWord_1756257).sum := by decide
  have hdescent : baseEnd_1756257 < baseStart_1756257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756280 : List Nat := [2, 1, 2, 1, 1, 1, 4, 3, 1, 2, 5]
def baseStart_1756280 : Nat := 118140960795 + 1756280 * 2 ^ 59
def prefixEnd_1756280 : Nat := 4983230072969 + 3 ^ 40 * 1756280 * 2
def baseEnd_1756280 : Nat := 901815803878493780123021

theorem tailTrace_1756280 : CollatzResearch.WordTrace tailWord_1756280 prefixEnd_1756280 901815803878493780123021 := by
  unfold tailWord_1756280
  simp only [CollatzResearch.WordTrace]
  refine ⟨32028397038652491794485147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42704529384869989059313529 32028397038652491794485147)
  ·
    refine ⟨48042595557978737691727721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32028397038652491794485147 48042595557978737691727721)
    ·
      refine ⟨36031946668484053268795791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48042595557978737691727721 36031946668484053268795791)
      ·
        refine ⟨54047920002726079903193687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36031946668484053268795791 54047920002726079903193687)
        ·
          refine ⟨81071880004089119854790531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54047920002726079903193687 81071880004089119854790531)
          ·
            refine ⟨121607820006133679782185797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81071880004089119854790531 121607820006133679782185797)
            ·
              refine ⟨22801466251150064959159837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121607820006133679782185797 22801466251150064959159837)
              ·
                refine ⟨8550549844181274359684939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22801466251150064959159837 8550549844181274359684939)
                ·
                  refine ⟨12825824766271911539527409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8550549844181274359684939 12825824766271911539527409)
                  ·
                    refine ⟨9619368574703933654645557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12825824766271911539527409 9619368574703933654645557)
                    ·
                      refine ⟨901815803878493780123021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9619368574703933654645557 901815803878493780123021)
                      ·
                        rfl

theorem cell23_1756280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_1756280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756280 prefixEnd_1756280 := by exact prefixLift 1756280
  have htrace : WordTrace (prefixWord ++ tailWord_1756280) baseStart_1756280 baseEnd_1756280 := by
    simpa [prefixWord, tailWord_1756280, baseEnd_1756280] using wordTrace_append hprefix tailTrace_1756280
  have hstable : (prefixWord ++ tailWord_1756280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756280).length < 2 ^ (prefixWord ++ tailWord_1756280).sum := by decide
  have hdescent : baseEnd_1756280 < baseStart_1756280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756307 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 1, 6, 2]
def baseStart_1756307 : Nat := 118140960795 + 1756307 * 2 ^ 59
def prefixEnd_1756307 : Nat := 4983230072969 + 3 ^ 40 * 1756307 * 2
def baseEnd_1756307 : Nat := 901829667856165174485397

theorem tailTrace_1756307 : CollatzResearch.WordTrace tailWord_1756307 prefixEnd_1756307 901829667856165174485397 := by
  unfold tailWord_1756307
  simp only [CollatzResearch.WordTrace]
  refine ⟨64057778848207167200203175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42705185898804778133468783 64057778848207167200203175)
  ·
    refine ⟨96086668272310750800304763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64057778848207167200203175 96086668272310750800304763)
    ·
      refine ⟨144130002408466126200457145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96086668272310750800304763 144130002408466126200457145)
      ·
        refine ⟨108097501806349594650342859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144130002408466126200457145 108097501806349594650342859)
        ·
          refine ⟨162146252709524391975514289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108097501806349594650342859 162146252709524391975514289)
          ·
            refine ⟨121609689532143293981635717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162146252709524391975514289 121609689532143293981635717)
            ·
              refine ⟨22801816787276867621556697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121609689532143293981635717 22801816787276867621556697)
              ·
                refine ⟨17101362590457650716167523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22801816787276867621556697 17101362590457650716167523)
                ·
                  refine ⟨25652043885686476074251285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17101362590457650716167523 25652043885686476074251285)
                  ·
                    refine ⟨1202439557141553565980529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25652043885686476074251285 1202439557141553565980529)
                    ·
                      refine ⟨901829667856165174485397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1202439557141553565980529 901829667856165174485397)
                      ·
                        rfl

theorem cell23_1756307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 6, 2].length) (baseStart_1756307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756307 prefixEnd_1756307 := by exact prefixLift 1756307
  have htrace : WordTrace (prefixWord ++ tailWord_1756307) baseStart_1756307 baseEnd_1756307 := by
    simpa [prefixWord, tailWord_1756307, baseEnd_1756307] using wordTrace_append hprefix tailTrace_1756307
  have hstable : (prefixWord ++ tailWord_1756307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756307).length < 2 ^ (prefixWord ++ tailWord_1756307).sum := by decide
  have hdescent : baseEnd_1756307 < baseStart_1756307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756324 : List Nat := [2, 3, 1, 2, 3, 2, 1, 2, 2, 1, 4]
def baseStart_1756324 : Nat := 118140960795 + 1756324 * 2 ^ 59
def prefixEnd_1756324 : Nat := 4983230072969 + 3 ^ 40 * 1756324 * 2
def baseEnd_1756324 : Nat := 901838397027291607972819

theorem tailTrace_1756324 : CollatzResearch.WordTrace tailWord_1756324 prefixEnd_1756324 901838397027291607972819 := by
  unfold tailWord_1756324
  simp only [CollatzResearch.WordTrace]
  refine ⟨32029199444572789551786013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42705599259430386069048017 32029199444572789551786013)
  ·
    refine ⟨12010949791714796081919755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32029199444572789551786013 12010949791714796081919755)
    ·
      refine ⟨18016424687572194122879633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12010949791714796081919755 18016424687572194122879633)
      ·
        refine ⟨13512318515679145592159725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18016424687572194122879633 13512318515679145592159725)
        ·
          refine ⟨5067119443379679597059897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13512318515679145592159725 5067119443379679597059897)
          ·
            refine ⟨3800339582534759697794923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5067119443379679597059897 3800339582534759697794923)
            ·
              refine ⟨5700509373802139546692385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3800339582534759697794923 5700509373802139546692385)
              ·
                refine ⟨4275382030351604660019289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5700509373802139546692385 4275382030351604660019289)
                ·
                  refine ⟨3206536522763703495014467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4275382030351604660019289 3206536522763703495014467)
                  ·
                    refine ⟨4809804784145555242521701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3206536522763703495014467 4809804784145555242521701)
                    ·
                      refine ⟨901838397027291607972819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4809804784145555242521701 901838397027291607972819)
                      ·
                        rfl

theorem cell23_1756324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_1756324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756324 prefixEnd_1756324 := by exact prefixLift 1756324
  have htrace : WordTrace (prefixWord ++ tailWord_1756324) baseStart_1756324 baseEnd_1756324 := by
    simpa [prefixWord, tailWord_1756324, baseEnd_1756324] using wordTrace_append hprefix tailTrace_1756324
  have hstable : (prefixWord ++ tailWord_1756324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756324).length < 2 ^ (prefixWord ++ tailWord_1756324).sum := by decide
  have hdescent : baseEnd_1756324 < baseStart_1756324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756381 : List Nat := [1, 4, 3, 2, 2, 1, 2, 2, 6]
def baseStart_1756381 : Nat := 118140960795 + 1756381 * 2 ^ 59
def prefixEnd_1756381 : Nat := 4983230072969 + 3 ^ 40 * 1756381 * 2
def baseEnd_1756381 : Nat := 100207518380510876106673

theorem tailTrace_1756381 : CollatzResearch.WordTrace tailWord_1756381 prefixEnd_1756381 100207518380510876106673 := by
  unfold tailWord_1756381
  simp only [CollatzResearch.WordTrace]
  refine ⟨64060477849939077838396997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42706985233292718558931331 64060477849939077838396997)
  ·
    refine ⟨12011339596863577094699437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64060477849939077838396997 12011339596863577094699437)
    ·
      refine ⟨4504252348823841410512289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12011339596863577094699437 4504252348823841410512289)
      ·
        refine ⟨3378189261617881057884217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4504252348823841410512289 3378189261617881057884217)
        ·
          refine ⟨2533641946213410793413163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3378189261617881057884217 2533641946213410793413163)
          ·
            refine ⟨3800462919320116190119745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2533641946213410793413163 3800462919320116190119745)
            ·
              refine ⟨2850347189490087142589809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3800462919320116190119745 2850347189490087142589809)
              ·
                refine ⟨2137760392117565356942357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2850347189490087142589809 2137760392117565356942357)
                ·
                  refine ⟨100207518380510876106673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2137760392117565356942357 100207518380510876106673)
                  ·
                    rfl

theorem cell23_1756381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 6].length) (baseStart_1756381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756381 prefixEnd_1756381 := by exact prefixLift 1756381
  have htrace : WordTrace (prefixWord ++ tailWord_1756381) baseStart_1756381 baseEnd_1756381 := by
    simpa [prefixWord, tailWord_1756381, baseEnd_1756381] using wordTrace_append hprefix tailTrace_1756381
  have hstable : (prefixWord ++ tailWord_1756381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756381).length < 2 ^ (prefixWord ++ tailWord_1756381).sum := by decide
  have hdescent : baseEnd_1756381 < baseStart_1756381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756418 : List Nat := [3, 4, 1, 1, 3, 1, 1, 1, 1, 5, 2]
def baseStart_1756418 : Nat := 118140960795 + 1756418 * 2 ^ 59
def prefixEnd_1756418 : Nat := 4983230072969 + 3 ^ 40 * 1756418 * 2
def baseEnd_1756418 : Nat := 901886664208814240197387

theorem tailTrace_1756418 : CollatzResearch.WordTrace tailWord_1756418 prefixEnd_1756418 901886664208814240197387 := by
  unfold tailWord_1756418
  simp only [CollatzResearch.WordTrace]
  refine ⟨16015456837701258289373477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42707884900536688771662605 16015456837701258289373477)
  ·
    refine ⟨3002898157068985929257527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16015456837701258289373477 3002898157068985929257527)
    ·
      refine ⟨4504347235603478893886291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3002898157068985929257527 4504347235603478893886291)
      ·
        refine ⟨6756520853405218340829437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4504347235603478893886291 6756520853405218340829437)
        ·
          refine ⟨2533695320026956877811039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6756520853405218340829437 2533695320026956877811039)
          ·
            refine ⟨3800542980040435316716559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2533695320026956877811039 3800542980040435316716559)
            ·
              refine ⟨5700814470060652975074839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3800542980040435316716559 5700814470060652975074839)
              ·
                refine ⟨8551221705090979462612259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5700814470060652975074839 8551221705090979462612259)
                ·
                  refine ⟨12826832557636469193918389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8551221705090979462612259 12826832557636469193918389)
                  ·
                    refine ⟨1202515552278418986929849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12826832557636469193918389 1202515552278418986929849)
                    ·
                      refine ⟨901886664208814240197387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1202515552278418986929849 901886664208814240197387)
                      ·
                        rfl

theorem cell23_1756418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_1756418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756418 prefixEnd_1756418 := by exact prefixLift 1756418
  have htrace : WordTrace (prefixWord ++ tailWord_1756418) baseStart_1756418 baseEnd_1756418 := by
    simpa [prefixWord, tailWord_1756418, baseEnd_1756418] using wordTrace_append hprefix tailTrace_1756418
  have hstable : (prefixWord ++ tailWord_1756418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756418).length < 2 ^ (prefixWord ++ tailWord_1756418).sum := by decide
  have hdescent : baseEnd_1756418 < baseStart_1756418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756461 : List Nat := [1, 5, 3, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_1756461 : Nat := 118140960795 + 1756461 * 2 ^ 59
def prefixEnd_1756461 : Nat := 4983230072969 + 3 ^ 40 * 1756461 * 2
def baseEnd_1756461 : Nat := 901908743876957571959689

theorem tailTrace_1756461 : CollatzResearch.WordTrace tailWord_1756461 prefixEnd_1756461 901908743876957571959689 := by
  unfold tailWord_1756461
  simp only [CollatzResearch.WordTrace]
  refine ⟨64063395689649251501309237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42708930459766167667539491 64063395689649251501309237)
  ·
    refine ⟨6005943345904617328247741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64063395689649251501309237 6005943345904617328247741)
    ·
      refine ⟨2252228754714231498092903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6005943345904617328247741 2252228754714231498092903)
      ·
        refine ⟨3378343132071347247139355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2252228754714231498092903 3378343132071347247139355)
        ·
          refine ⟨5067514698107020870709033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3378343132071347247139355 5067514698107020870709033)
          ·
            refine ⟨3800636023580265653031775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5067514698107020870709033 3800636023580265653031775)
            ·
              refine ⟨5700954035370398479547663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3800636023580265653031775 5700954035370398479547663)
              ·
                refine ⟨8551431053055597719321495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5700954035370398479547663 8551431053055597719321495)
                ·
                  refine ⟨12827146579583396578982243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8551431053055597719321495 12827146579583396578982243)
                  ·
                    refine ⟨19240719869375094868473365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12827146579583396578982243 19240719869375094868473365)
                    ·
                      refine ⟨901908743876957571959689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19240719869375094868473365 901908743876957571959689)
                      ·
                        rfl

theorem cell23_1756461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_1756461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756461 prefixEnd_1756461 := by exact prefixLift 1756461
  have htrace : WordTrace (prefixWord ++ tailWord_1756461) baseStart_1756461 baseEnd_1756461 := by
    simpa [prefixWord, tailWord_1756461, baseEnd_1756461] using wordTrace_append hprefix tailTrace_1756461
  have hstable : (prefixWord ++ tailWord_1756461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756461).length < 2 ^ (prefixWord ++ tailWord_1756461).sum := by decide
  have hdescent : baseEnd_1756461 < baseStart_1756461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756468 : List Nat := [2, 5, 1, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_1756468 : Nat := 118140960795 + 1756468 * 2 ^ 59
def prefixEnd_1756468 : Nat := 4983230072969 + 3 ^ 40 * 1756468 * 2
def baseEnd_1756468 : Nat := 901912338241539044572157

theorem tailTrace_1756468 : CollatzResearch.WordTrace tailWord_1756468 prefixEnd_1756468 901912338241539044572157 := by
  unfold tailWord_1756468
  simp only [CollatzResearch.WordTrace]
  refine ⟨32031825500311945848407029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42709100667082594464542705 32031825500311945848407029)
  ·
    refine ⟨3002983640654244923288159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32031825500311945848407029 3002983640654244923288159)
    ·
      refine ⟨4504475460981367384932239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3002983640654244923288159 4504475460981367384932239)
      ·
        refine ⟨6756713191472051077398359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4504475460981367384932239 6756713191472051077398359)
        ·
          refine ⟨10135069787208076616097539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6756713191472051077398359 10135069787208076616097539)
          ·
            refine ⟨15202604680812114924146309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10135069787208076616097539 15202604680812114924146309)
            ·
              refine ⟨2850488377652271548277433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15202604680812114924146309 2850488377652271548277433)
              ·
                refine ⟨2137866283239203661208075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2850488377652271548277433 2137866283239203661208075)
                ·
                  refine ⟨3206799424858805491812113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2137866283239203661208075 3206799424858805491812113)
                  ·
                    refine ⟨2405099568644104118859085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3206799424858805491812113 2405099568644104118859085)
                    ·
                      refine ⟨901912338241539044572157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2405099568644104118859085 901912338241539044572157)
                      ·
                        rfl

theorem cell23_1756468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_1756468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756468 prefixEnd_1756468 := by exact prefixLift 1756468
  have htrace : WordTrace (prefixWord ++ tailWord_1756468) baseStart_1756468 baseEnd_1756468 := by
    simpa [prefixWord, tailWord_1756468, baseEnd_1756468] using wordTrace_append hprefix tailTrace_1756468
  have hstable : (prefixWord ++ tailWord_1756468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756468).length < 2 ^ (prefixWord ++ tailWord_1756468).sum := by decide
  have hdescent : baseEnd_1756468 < baseStart_1756468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756509 : List Nat := [1, 4, 5, 1, 1, 2, 2, 1, 2, 4]
def baseStart_1756509 : Nat := 118140960795 + 1756509 * 2 ^ 59
def prefixEnd_1756509 : Nat := 4983230072969 + 3 ^ 40 * 1756509 * 2
def baseEnd_1756509 : Nat := 300644463649457794719823

theorem tailTrace_1756509 : CollatzResearch.WordTrace tailWord_1756509 prefixEnd_1756509 300644463649457794719823 := by
  unfold tailWord_1756509
  simp only [CollatzResearch.WordTrace]
  refine ⟨64065146393475355699056581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42710097595650237132704387 64065146393475355699056581)
  ·
    refine ⟨12012214948776629193573109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64065146393475355699056581 12012214948776629193573109)
    ·
      refine ⟨1126145151447808986897479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12012214948776629193573109 1126145151447808986897479)
      ·
        refine ⟨1689217727171713480346219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1126145151447808986897479 1689217727171713480346219)
        ·
          refine ⟨2533826590757570220519329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1689217727171713480346219 2533826590757570220519329)
          ·
            refine ⟨1900369943068177665389497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2533826590757570220519329 1900369943068177665389497)
            ·
              refine ⟨1425277457301133249042123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1900369943068177665389497 1425277457301133249042123)
              ·
                refine ⟨2137916185951699873563185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1425277457301133249042123 2137916185951699873563185)
                ·
                  refine ⟨1603437139463774905172389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2137916185951699873563185 1603437139463774905172389)
                  ·
                    refine ⟨300644463649457794719823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1603437139463774905172389 300644463649457794719823)
                    ·
                      rfl

theorem cell23_1756509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_1756509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756509 prefixEnd_1756509 := by exact prefixLift 1756509
  have htrace : WordTrace (prefixWord ++ tailWord_1756509) baseStart_1756509 baseEnd_1756509 := by
    simpa [prefixWord, tailWord_1756509, baseEnd_1756509] using wordTrace_append hprefix tailTrace_1756509
  have hstable : (prefixWord ++ tailWord_1756509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756509).length < 2 ^ (prefixWord ++ tailWord_1756509).sum := by decide
  have hdescent : baseEnd_1756509 < baseStart_1756509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756514 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 1, 8]
def baseStart_1756514 : Nat := 118140960795 + 1756514 * 2 ^ 59
def prefixEnd_1756514 : Nat := 4983230072969 + 3 ^ 40 * 1756514 * 2
def baseEnd_1756514 : Nat := 300645319450548621532315

theorem tailTrace_1756514 : CollatzResearch.WordTrace tailWord_1756514 prefixEnd_1756514 300645319450548621532315 := by
  unfold tailWord_1756514
  simp only [CollatzResearch.WordTrace]
  refine ⟨16016332189614310388247149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42710219172304827701992397 16016332189614310388247149)
  ·
    refine ⟨6006124571105366395592681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16016332189614310388247149 6006124571105366395592681)
    ·
      refine ⟨4504593428329024796694511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6006124571105366395592681 4504593428329024796694511)
      ·
        refine ⟨6756890142493537195041767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4504593428329024796694511 6756890142493537195041767)
        ·
          refine ⟨10135335213740305792562651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6756890142493537195041767 10135335213740305792562651)
          ·
            refine ⟨15203002820610458688843977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10135335213740305792562651 15203002820610458688843977)
            ·
              refine ⟨11402252115457844016632983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15203002820610458688843977 11402252115457844016632983)
              ·
                refine ⟨17103378173186766024949475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11402252115457844016632983 17103378173186766024949475)
                ·
                  refine ⟨25655067259780149037424213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17103378173186766024949475 25655067259780149037424213)
                  ·
                    refine ⟨300645319450548621532315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25655067259780149037424213 300645319450548621532315)
                    ·
                      rfl

theorem cell23_1756514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_1756514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756514 prefixEnd_1756514 := by exact prefixLift 1756514
  have htrace : WordTrace (prefixWord ++ tailWord_1756514) baseStart_1756514 baseEnd_1756514 := by
    simpa [prefixWord, tailWord_1756514, baseEnd_1756514] using wordTrace_append hprefix tailTrace_1756514
  have hstable : (prefixWord ++ tailWord_1756514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756514).length < 2 ^ (prefixWord ++ tailWord_1756514).sum := by decide
  have hdescent : baseEnd_1756514 < baseStart_1756514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756515 : List Nat := [1, 1, 1, 5, 2, 4, 2, 1, 2, 1, 3]
def baseStart_1756515 : Nat := 118140960795 + 1756515 * 2 ^ 59
def prefixEnd_1756515 : Nat := 4983230072969 + 3 ^ 40 * 1756515 * 2
def baseEnd_1756515 : Nat := 901936471832300360684441

theorem tailTrace_1756515 : CollatzResearch.WordTrace tailWord_1756515 prefixEnd_1756515 901936471832300360684441 := by
  unfold tailWord_1756515
  simp only [CollatzResearch.WordTrace]
  refine ⟨64065365231453618723774999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42710243487635745815849999 64065365231453618723774999)
  ·
    refine ⟨96098047847180428085662499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64065365231453618723774999 96098047847180428085662499)
    ·
      refine ⟨144147071770770642128493749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96098047847180428085662499 144147071770770642128493749)
      ·
        refine ⟨13513787978509747699546289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144147071770770642128493749 13513787978509747699546289)
        ·
          refine ⟨10135340983882310774659717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13513787978509747699546289 10135340983882310774659717)
          ·
            refine ⟨1900376434477933270248697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10135340983882310774659717 1900376434477933270248697)
            ·
              refine ⟨1425282325858449952686523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1900376434477933270248697 1425282325858449952686523)
              ·
                refine ⟨2137923488787674929029785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1425282325858449952686523 2137923488787674929029785)
                ·
                  refine ⟨1603442616590756196772339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2137923488787674929029785 1603442616590756196772339)
                  ·
                    refine ⟨2405163924886134295158509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1603442616590756196772339 2405163924886134295158509)
                    ·
                      refine ⟨901936471832300360684441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2405163924886134295158509 901936471832300360684441)
                      ·
                        rfl

theorem cell23_1756515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_1756515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756515 prefixEnd_1756515 := by exact prefixLift 1756515
  have htrace : WordTrace (prefixWord ++ tailWord_1756515) baseStart_1756515 baseEnd_1756515 := by
    simpa [prefixWord, tailWord_1756515, baseEnd_1756515] using wordTrace_append hprefix tailTrace_1756515
  have hstable : (prefixWord ++ tailWord_1756515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756515).length < 2 ^ (prefixWord ++ tailWord_1756515).sum := by decide
  have hdescent : baseEnd_1756515 < baseStart_1756515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756521 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 6, 2, 2]
def baseStart_1756521 : Nat := 118140960795 + 1756521 * 2 ^ 59
def prefixEnd_1756521 : Nat := 4983230072969 + 3 ^ 40 * 1756521 * 2
def baseEnd_1756521 : Nat := 901939552716227337209413

theorem tailTrace_1756521 : CollatzResearch.WordTrace tailWord_1756521 prefixEnd_1756521 901939552716227337209413 := by
  unfold tailWord_1756521
  simp only [CollatzResearch.WordTrace]
  refine ⟨64065584069431881748493417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42710389379621254498995611 64065584069431881748493417)
  ·
    refine ⟨48049188052073911311370063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64065584069431881748493417 48049188052073911311370063)
    ·
      refine ⟨72073782078110866967055095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48049188052073911311370063 72073782078110866967055095)
      ·
        refine ⟨108110673117166300450582643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72073782078110866967055095 108110673117166300450582643)
        ·
          refine ⟨162166009675749450675873965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108110673117166300450582643 162166009675749450675873965)
          ·
            refine ⟨60812253628406044003452737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162166009675749450675873965 60812253628406044003452737)
            ·
              refine ⟨45609190221304533002589553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60812253628406044003452737 45609190221304533002589553)
              ·
                refine ⟨34206892665978399751942165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45609190221304533002589553 34206892665978399751942165)
                ·
                  refine ⟨1603448093717737488372289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 34206892665978399751942165 1603448093717737488372289)
                  ·
                    refine ⟨1202586070288303116279217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1603448093717737488372289 1202586070288303116279217)
                    ·
                      refine ⟨901939552716227337209413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1202586070288303116279217 901939552716227337209413)
                      ·
                        rfl

theorem cell23_1756521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6, 2, 2].length) (baseStart_1756521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756521 prefixEnd_1756521 := by exact prefixLift 1756521
  have htrace : WordTrace (prefixWord ++ tailWord_1756521) baseStart_1756521 baseEnd_1756521 := by
    simpa [prefixWord, tailWord_1756521, baseEnd_1756521] using wordTrace_append hprefix tailTrace_1756521
  have hstable : (prefixWord ++ tailWord_1756521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756521).length < 2 ^ (prefixWord ++ tailWord_1756521).sum := by decide
  have hdescent : baseEnd_1756521 < baseStart_1756521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756524 : List Nat := [2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 5]
def baseStart_1756524 : Nat := 118140960795 + 1756524 * 2 ^ 59
def prefixEnd_1756524 : Nat := 4983230072969 + 3 ^ 40 * 1756524 * 2
def baseEnd_1756524 : Nat := 901941093158190825471899

theorem tailTrace_1756524 : CollatzResearch.WordTrace tailWord_1756524 prefixEnd_1756524 901941093158190825471899 := by
  unfold tailWord_1756524
  simp only [CollatzResearch.WordTrace]
  refine ⟨32032846744210506630426313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42710462325614008840568417 32032846744210506630426313)
  ·
    refine ⟨24024635058157879972819735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32032846744210506630426313 24024635058157879972819735)
    ·
      refine ⟨36036952587236819959229603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24024635058157879972819735 36036952587236819959229603)
      ·
        refine ⟨54055428880855229938844405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36036952587236819959229603 54055428880855229938844405)
        ·
          refine ⟨5067696457580177806766663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54055428880855229938844405 5067696457580177806766663)
          ·
            refine ⟨7601544686370266710149995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5067696457580177806766663 7601544686370266710149995)
            ·
              refine ⟨11402317029555400065224993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7601544686370266710149995 11402317029555400065224993)
              ·
                refine ⟨8551737772166550048918745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11402317029555400065224993 8551737772166550048918745)
                ·
                  refine ⟨6413803329124912536689059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8551737772166550048918745 6413803329124912536689059)
                  ·
                    refine ⟨9620704993687368805033589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6413803329124912536689059 9620704993687368805033589)
                    ·
                      refine ⟨901941093158190825471899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9620704993687368805033589 901941093158190825471899)
                      ·
                        rfl

theorem cell23_1756524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_1756524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756524 prefixEnd_1756524 := by exact prefixLift 1756524
  have htrace : WordTrace (prefixWord ++ tailWord_1756524) baseStart_1756524 baseEnd_1756524 := by
    simpa [prefixWord, tailWord_1756524, baseEnd_1756524] using wordTrace_append hprefix tailTrace_1756524
  have hstable : (prefixWord ++ tailWord_1756524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756524).length < 2 ^ (prefixWord ++ tailWord_1756524).sum := by decide
  have hdescent : baseEnd_1756524 < baseStart_1756524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756525 : List Nat := [1, 5, 1, 1, 1, 5, 1, 2, 1, 3, 2]
def baseStart_1756525 : Nat := 118140960795 + 1756525 * 2 ^ 59
def prefixEnd_1756525 : Nat := 4983230072969 + 3 ^ 40 * 1756525 * 2
def baseEnd_1756525 : Nat := 901941606638845321559395

theorem tailTrace_1756525 : CollatzResearch.WordTrace tailWord_1756525 prefixEnd_1756525 901941606638845321559395 := by
  unfold tailWord_1756525
  simp only [CollatzResearch.WordTrace]
  refine ⟨64065729961417390431639029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42710486640944926954426019 64065729961417390431639029)
  ·
    refine ⟨6006162183882880352966159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64065729961417390431639029 6006162183882880352966159)
    ·
      refine ⟨9009243275824320529449239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6006162183882880352966159 9009243275824320529449239)
      ·
        refine ⟨13513864913736480794173859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9009243275824320529449239 13513864913736480794173859)
        ·
          refine ⟨20270797370604721191260789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13513864913736480794173859 20270797370604721191260789)
          ·
            refine ⟨1900387253494192611680699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20270797370604721191260789 1900387253494192611680699)
            ·
              refine ⟨2850580880241288917521049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1900387253494192611680699 2850580880241288917521049)
              ·
                refine ⟨2137935660180966688140787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2850580880241288917521049 2137935660180966688140787)
                ·
                  refine ⟨3206903490271450032211181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2137935660180966688140787 3206903490271450032211181)
                  ·
                    refine ⟨1202588808851793762079193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3206903490271450032211181 1202588808851793762079193)
                    ·
                      refine ⟨901941606638845321559395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1202588808851793762079193 901941606638845321559395)
                      ·
                        rfl

theorem cell23_1756525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_1756525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756525 prefixEnd_1756525 := by exact prefixLift 1756525
  have htrace : WordTrace (prefixWord ++ tailWord_1756525) baseStart_1756525 baseEnd_1756525 := by
    simpa [prefixWord, tailWord_1756525, baseEnd_1756525] using wordTrace_append hprefix tailTrace_1756525
  have hstable : (prefixWord ++ tailWord_1756525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756525).length < 2 ^ (prefixWord ++ tailWord_1756525).sum := by decide
  have hdescent : baseEnd_1756525 < baseStart_1756525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756527 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 9]
def baseStart_1756527 : Nat := 118140960795 + 1756527 * 2 ^ 59
def prefixEnd_1756527 : Nat := 4983230072969 + 3 ^ 40 * 1756527 * 2
def baseEnd_1756527 : Nat := 100215848177794923748265

theorem tailTrace_1756527 : CollatzResearch.WordTrace tailWord_1756527 prefixEnd_1756527 100215848177794923748265 := by
  unfold tailWord_1756527
  simp only [CollatzResearch.WordTrace]
  refine ⟨64065802907410144773211835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42710535271606763182141223 64065802907410144773211835)
  ·
    refine ⟨96098704361115217159817753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64065802907410144773211835 96098704361115217159817753)
    ·
      refine ⟨72074028270836412869863315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96098704361115217159817753 72074028270836412869863315)
      ·
        refine ⟨108111042406254619304794973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72074028270836412869863315 108111042406254619304794973)
        ·
          refine ⟨40541640902345482239298115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108111042406254619304794973 40541640902345482239298115)
          ·
            refine ⟨60812461353518223358947173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40541640902345482239298115 60812461353518223358947173)
            ·
              refine ⟨11402336503784666879802595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60812461353518223358947173 11402336503784666879802595)
              ·
                refine ⟨17103504755677000319703893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11402336503784666879802595 17103504755677000319703893)
                ·
                  refine ⟨100215848177794923748265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17103504755677000319703893 100215848177794923748265)
                  ·
                    rfl

theorem cell23_1756527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 9].length) (baseStart_1756527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756527 prefixEnd_1756527 := by exact prefixLift 1756527
  have htrace : WordTrace (prefixWord ++ tailWord_1756527) baseStart_1756527 baseEnd_1756527 := by
    simpa [prefixWord, tailWord_1756527, baseEnd_1756527] using wordTrace_append hprefix tailTrace_1756527
  have hstable : (prefixWord ++ tailWord_1756527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756527).length < 2 ^ (prefixWord ++ tailWord_1756527).sum := by decide
  have hdescent : baseEnd_1756527 < baseStart_1756527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756611 : List Nat := [1, 1, 1, 3, 1, 1, 5, 2, 2, 4, 2]
def baseStart_1756611 : Nat := 118140960795 + 1756611 * 2 ^ 59
def prefixEnd_1756611 : Nat := 4983230072969 + 3 ^ 40 * 1756611 * 2
def baseEnd_1756611 : Nat := 901985765975131985083999

theorem tailTrace_1756611 : CollatzResearch.WordTrace tailWord_1756611 prefixEnd_1756611 901985765975131985083999 := by
  unfold tailWord_1756611
  simp only [CollatzResearch.WordTrace]
  refine ⟨64068866639105827119269687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42712577759403884746179791 64068866639105827119269687)
  ·
    refine ⟨96103299958658740678904531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64068866639105827119269687 96103299958658740678904531)
    ·
      refine ⟨144154949937988111018356797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96103299958658740678904531 144154949937988111018356797)
      ·
        refine ⟨54058106226745541631883799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144154949937988111018356797 54058106226745541631883799)
        ·
          refine ⟨81087159340118312447825699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54058106226745541631883799 81087159340118312447825699)
          ·
            refine ⟨121630739010177468671738549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81087159340118312447825699 121630739010177468671738549)
            ·
              refine ⟨11402881782204137687975489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121630739010177468671738549 11402881782204137687975489)
              ·
                refine ⟨8552161336653103265981617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11402881782204137687975489 8552161336653103265981617)
                ·
                  refine ⟨6414121002489827449486213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8552161336653103265981617 6414121002489827449486213)
                  ·
                    refine ⟨1202647687966842646778665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6414121002489827449486213 1202647687966842646778665)
                    ·
                      refine ⟨901985765975131985083999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1202647687966842646778665 901985765975131985083999)
                      ·
                        rfl

theorem cell23_1756611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 4, 2].length) (baseStart_1756611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756611 prefixEnd_1756611 := by exact prefixLift 1756611
  have htrace : WordTrace (prefixWord ++ tailWord_1756611) baseStart_1756611 baseEnd_1756611 := by
    simpa [prefixWord, tailWord_1756611, baseEnd_1756611] using wordTrace_append hprefix tailTrace_1756611
  have hstable : (prefixWord ++ tailWord_1756611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756611).length < 2 ^ (prefixWord ++ tailWord_1756611).sum := by decide
  have hdescent : baseEnd_1756611 < baseStart_1756611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756671 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 3, 5, 2]
def baseStart_1756671 : Nat := 118140960795 + 1756671 * 2 ^ 59
def prefixEnd_1756671 : Nat := 4983230072969 + 3 ^ 40 * 1756671 * 2
def baseEnd_1756671 : Nat := 902016574814401750333723

theorem tailTrace_1756671 : CollatzResearch.WordTrace tailWord_1756671 prefixEnd_1756671 902016574814401750333723 := by
  unfold tailWord_1756671
  simp only [CollatzResearch.WordTrace]
  refine ⟨64071055018888457366453867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42714036679258971577635911 64071055018888457366453867)
  ·
    refine ⟨96106582528332686049680801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64071055018888457366453867 96106582528332686049680801)
    ·
      refine ⟨72079936896249514537260601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96106582528332686049680801 72079936896249514537260601)
      ·
        refine ⟨54059952672187135902945451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72079936896249514537260601 54059952672187135902945451)
        ·
          refine ⟨81089929008280703854418177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54059952672187135902945451 81089929008280703854418177)
          ·
            refine ⟨60817446756210527890813633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81089929008280703854418177 60817446756210527890813633)
            ·
              refine ⟨45613085067157895918110225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60817446756210527890813633 45613085067157895918110225)
              ·
                refine ⟨34209813800368421938582669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45613085067157895918110225 34209813800368421938582669)
                ·
                  refine ⟨12828680175138158226968501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34209813800368421938582669 12828680175138158226968501)
                  ·
                    refine ⟨1202688766419202333778297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12828680175138158226968501 1202688766419202333778297)
                    ·
                      refine ⟨902016574814401750333723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1202688766419202333778297 902016574814401750333723)
                      ·
                        rfl

theorem cell23_1756671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 5, 2].length) (baseStart_1756671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756671 prefixEnd_1756671 := by exact prefixLift 1756671
  have htrace : WordTrace (prefixWord ++ tailWord_1756671) baseStart_1756671 baseEnd_1756671 := by
    simpa [prefixWord, tailWord_1756671, baseEnd_1756671] using wordTrace_append hprefix tailTrace_1756671
  have hstable : (prefixWord ++ tailWord_1756671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756671).length < 2 ^ (prefixWord ++ tailWord_1756671).sum := by decide
  have hdescent : baseEnd_1756671 < baseStart_1756671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756705 : List Nat := [1, 2, 3, 2, 2, 3, 2, 1, 2, 3, 2]
def baseStart_1756705 : Nat := 118140960795 + 1756705 * 2 ^ 59
def prefixEnd_1756705 : Nat := 4983230072969 + 3 ^ 40 * 1756705 * 2
def baseEnd_1756705 : Nat := 902034033156654617308567

theorem tailTrace_1756705 : CollatzResearch.WordTrace tailWord_1756705 prefixEnd_1756705 902034033156654617308567 := by
  unfold tailWord_1756705
  simp only [CollatzResearch.WordTrace]
  refine ⟨64072295100765281173191569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42714863400510187448794379 64072295100765281173191569)
  ·
    refine ⟨48054221325573960879893677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64072295100765281173191569 48054221325573960879893677)
    ·
      refine ⟨18020332997090235329960129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48054221325573960879893677 18020332997090235329960129)
      ·
        refine ⟨13515249747817676497470097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18020332997090235329960129 13515249747817676497470097)
        ·
          refine ⟨10136437310863257373102573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13515249747817676497470097 10136437310863257373102573)
          ·
            refine ⟨3801163991573721514913465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10136437310863257373102573 3801163991573721514913465)
            ·
              refine ⟨2850872993680291136185099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3801163991573721514913465 2850872993680291136185099)
              ·
                refine ⟨4276309490520436704277649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2850872993680291136185099 4276309490520436704277649)
                ·
                  refine ⟨3207232117890327528208237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4276309490520436704277649 3207232117890327528208237)
                  ·
                    refine ⟨1202712044208872823078089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3207232117890327528208237 1202712044208872823078089)
                    ·
                      refine ⟨902034033156654617308567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1202712044208872823078089 902034033156654617308567)
                      ·
                        rfl

theorem cell23_1756705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_1756705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756705 prefixEnd_1756705 := by exact prefixLift 1756705
  have htrace : WordTrace (prefixWord ++ tailWord_1756705) baseStart_1756705 baseEnd_1756705 := by
    simpa [prefixWord, tailWord_1756705, baseEnd_1756705] using wordTrace_append hprefix tailTrace_1756705
  have hstable : (prefixWord ++ tailWord_1756705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756705).length < 2 ^ (prefixWord ++ tailWord_1756705).sum := by decide
  have hdescent : baseEnd_1756705 < baseStart_1756705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756728 : List Nat := [2, 1, 2, 1, 4, 2, 1, 4, 2, 4]
def baseStart_1756728 : Nat := 118140960795 + 1756728 * 2 ^ 59
def prefixEnd_1756728 : Nat := 4983230072969 + 3 ^ 40 * 1756728 * 2
def baseEnd_1756728 : Nat := 300681947737236009106987

theorem tailTrace_1756728 : CollatzResearch.WordTrace tailWord_1756728 prefixEnd_1756728 300681947737236009106987 := by
  unfold tailWord_1756728
  simp only [CollatzResearch.WordTrace]
  refine ⟨32036566989840978050639419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42715422653121304067519225 32036566989840978050639419)
  ·
    refine ⟨48054850484761467075959129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32036566989840978050639419 48054850484761467075959129)
    ·
      refine ⟨36041137863571100306969347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48054850484761467075959129 36041137863571100306969347)
      ·
        refine ⟨54061706795356650460454021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36041137863571100306969347 54061706795356650460454021)
        ·
          refine ⟨10136570024129371961335129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54061706795356650460454021 10136570024129371961335129)
          ·
            refine ⟨7602427518097028971001347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10136570024129371961335129 7602427518097028971001347)
            ·
              refine ⟨11403641277145543456502021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7602427518097028971001347 11403641277145543456502021)
              ·
                refine ⟨2138182739464789398094129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11403641277145543456502021 2138182739464789398094129)
                ·
                  refine ⟨1603637054598592048570597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2138182739464789398094129 1603637054598592048570597)
                  ·
                    refine ⟨300681947737236009106987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1603637054598592048570597 300681947737236009106987)
                    ·
                      rfl

theorem cell23_1756728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 2, 4].length) (baseStart_1756728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756728 prefixEnd_1756728 := by exact prefixLift 1756728
  have htrace : WordTrace (prefixWord ++ tailWord_1756728) baseStart_1756728 baseEnd_1756728 := by
    simpa [prefixWord, tailWord_1756728, baseEnd_1756728] using wordTrace_append hprefix tailTrace_1756728
  have hstable : (prefixWord ++ tailWord_1756728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756728).length < 2 ^ (prefixWord ++ tailWord_1756728).sum := by decide
  have hdescent : baseEnd_1756728 < baseStart_1756728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756729 : List Nat := [1, 2, 1, 5, 1, 4, 2, 2, 1, 1, 3]
def baseStart_1756729 : Nat := 118140960795 + 1756729 * 2 ^ 59
def prefixEnd_1756729 : Nat := 4983230072969 + 3 ^ 40 * 1756729 * 2
def baseEnd_1756729 : Nat := 902046356692362523408457

theorem tailTrace_1756729 : CollatzResearch.WordTrace tailWord_1756729 prefixEnd_1756729 902046356692362523408457 := by
  unfold tailWord_1756729
  simp only [CollatzResearch.WordTrace]
  refine ⟨64073170452678333272065241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42715446968452222181376827 64073170452678333272065241)
  ·
    refine ⟨48054877839508749954048931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64073170452678333272065241 48054877839508749954048931)
    ·
      refine ⟨72082316759263124931073397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48054877839508749954048931 72082316759263124931073397)
      ·
        refine ⟨6757717196180917962288131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72082316759263124931073397 6757717196180917962288131)
        ·
          refine ⟨10136575794271376943432197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6757717196180917962288131 10136575794271376943432197)
          ·
            refine ⟨1900607961425883176893537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10136575794271376943432197 1900607961425883176893537)
            ·
              refine ⟨1425455971069412382670153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1900607961425883176893537 1425455971069412382670153)
              ·
                refine ⟨1069091978302059287002615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1425455971069412382670153 1069091978302059287002615)
                ·
                  refine ⟨1603637967453088930503923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1069091978302059287002615 1603637967453088930503923)
                  ·
                    refine ⟨2405456951179633395755885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1603637967453088930503923 2405456951179633395755885)
                    ·
                      refine ⟨902046356692362523408457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2405456951179633395755885 902046356692362523408457)
                      ·
                        rfl

theorem cell23_1756729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_1756729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756729 prefixEnd_1756729 := by exact prefixLift 1756729
  have htrace : WordTrace (prefixWord ++ tailWord_1756729) baseStart_1756729 baseEnd_1756729 := by
    simpa [prefixWord, tailWord_1756729, baseEnd_1756729] using wordTrace_append hprefix tailTrace_1756729
  have hstable : (prefixWord ++ tailWord_1756729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756729).length < 2 ^ (prefixWord ++ tailWord_1756729).sum := by decide
  have hdescent : baseEnd_1756729 < baseStart_1756729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756748 : List Nat := [2, 2, 1, 3, 1, 4, 2, 1, 1, 2, 4]
def baseStart_1756748 : Nat := 118140960795 + 1756748 * 2 ^ 59
def prefixEnd_1756748 : Nat := 4983230072969 + 3 ^ 40 * 1756748 * 2
def baseEnd_1756748 : Nat := 902056112824797949070869

theorem tailTrace_1756748 : CollatzResearch.WordTrace tailWord_1756748 prefixEnd_1756748 902056112824797949070869 := by
  unfold tailWord_1756748
  simp only [CollatzResearch.WordTrace]
  refine ⟨32036931719804749758503449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42715908959739666344671265 32036931719804749758503449)
  ·
    refine ⟨24027698789853562318877587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32036931719804749758503449 24027698789853562318877587)
    ·
      refine ⟨36041548184780343478316381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24027698789853562318877587 36041548184780343478316381)
      ·
        refine ⟨13515580569292628804368643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36041548184780343478316381 13515580569292628804368643)
        ·
          refine ⟨20273370853938943206552965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13515580569292628804368643 20273370853938943206552965)
          ·
            refine ⟨3801257035113551851228681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20273370853938943206552965 3801257035113551851228681)
            ·
              refine ⟨2850942776335163888421511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3801257035113551851228681 2850942776335163888421511)
              ·
                refine ⟨4276414164502745832632267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2850942776335163888421511 4276414164502745832632267)
                ·
                  refine ⟨6414621246754118748948401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4276414164502745832632267 6414621246754118748948401)
                  ·
                    refine ⟨4810965935065589061711301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6414621246754118748948401 4810965935065589061711301)
                    ·
                      refine ⟨902056112824797949070869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4810965935065589061711301 902056112824797949070869)
                      ·
                        rfl

theorem cell23_1756748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_1756748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756748 prefixEnd_1756748 := by exact prefixLift 1756748
  have htrace : WordTrace (prefixWord ++ tailWord_1756748) baseStart_1756748 baseEnd_1756748 := by
    simpa [prefixWord, tailWord_1756748, baseEnd_1756748] using wordTrace_append hprefix tailTrace_1756748
  have hstable : (prefixWord ++ tailWord_1756748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756748).length < 2 ^ (prefixWord ++ tailWord_1756748).sum := by decide
  have hdescent : baseEnd_1756748 < baseStart_1756748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756768 : List Nat := [2, 1, 1, 3, 2, 1, 1, 4, 4, 1, 3]
def baseStart_1756768 : Nat := 118140960795 + 1756768 * 2 ^ 59
def prefixEnd_1756768 : Nat := 4983230072969 + 3 ^ 40 * 1756768 * 2
def baseEnd_1756768 : Nat := 902066382437887870820777

theorem tailTrace_1756768 : CollatzResearch.WordTrace tailWord_1756768 prefixEnd_1756768 902066382437887870820777 := by
  unfold tailWord_1756768
  simp only [CollatzResearch.WordTrace]
  refine ⟨32037296449768521466367479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42716395266358028621823305 32037296449768521466367479)
  ·
    refine ⟨48055944674652782199551219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32037296449768521466367479 48055944674652782199551219)
    ·
      refine ⟨72083917011979173299326829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48055944674652782199551219 72083917011979173299326829)
      ·
        refine ⟨27031468879492189987247561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72083917011979173299326829 27031468879492189987247561)
        ·
          refine ⟨20273601659619142490435671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27031468879492189987247561 20273601659619142490435671)
          ·
            refine ⟨30410402489428713735653507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20273601659619142490435671 30410402489428713735653507)
            ·
              refine ⟨45615603734143070603480261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30410402489428713735653507 45615603734143070603480261)
              ·
                refine ⟨8552925700151825738152549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45615603734143070603480261 8552925700151825738152549)
                ·
                  refine ⟨1603673568778467325903603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8552925700151825738152549 1603673568778467325903603)
                  ·
                    refine ⟨2405510353167700988855405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1603673568778467325903603 2405510353167700988855405)
                    ·
                      refine ⟨902066382437887870820777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2405510353167700988855405 902066382437887870820777)
                      ·
                        rfl

theorem cell23_1756768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_1756768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756768 prefixEnd_1756768 := by exact prefixLift 1756768
  have htrace : WordTrace (prefixWord ++ tailWord_1756768) baseStart_1756768 baseEnd_1756768 := by
    simpa [prefixWord, tailWord_1756768, baseEnd_1756768] using wordTrace_append hprefix tailTrace_1756768
  have hstable : (prefixWord ++ tailWord_1756768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756768).length < 2 ^ (prefixWord ++ tailWord_1756768).sum := by decide
  have hdescent : baseEnd_1756768 < baseStart_1756768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756772 : List Nat := [2, 3, 1, 1, 2, 5, 2, 1, 1, 2, 3]
def baseStart_1756772 : Nat := 118140960795 + 1756772 * 2 ^ 59
def prefixEnd_1756772 : Nat := 4983230072969 + 3 ^ 40 * 1756772 * 2
def baseEnd_1756772 : Nat := 902068436360505855170759

theorem tailTrace_1756772 : CollatzResearch.WordTrace tailWord_1756772 prefixEnd_1756772 902068436360505855170759 := by
  unfold tailWord_1756772
  simp only [CollatzResearch.WordTrace]
  refine ⟨32037369395761275807940285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42716492527681701077253713 32037369395761275807940285)
  ·
    refine ⟨12014013523410478427977607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32037369395761275807940285 12014013523410478427977607)
    ·
      refine ⟨18021020285115717641966411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12014013523410478427977607 18021020285115717641966411)
      ·
        refine ⟨27031530427673576462949617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18021020285115717641966411 27031530427673576462949617)
        ·
          refine ⟨20273647820755182347212213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27031530427673576462949617 20273647820755182347212213)
          ·
            refine ⟨1900654483195798345051145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20273647820755182347212213 1900654483195798345051145)
            ·
              refine ⟨1425490862396848758788359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1900654483195798345051145 1425490862396848758788359)
              ·
                refine ⟨2138236293595273138182539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1425490862396848758788359 2138236293595273138182539)
                ·
                  refine ⟨3207354440392909707273809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2138236293595273138182539 3207354440392909707273809)
                  ·
                    refine ⟨2405515830294682280455357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3207354440392909707273809 2405515830294682280455357)
                    ·
                      refine ⟨902068436360505855170759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2405515830294682280455357 902068436360505855170759)
                      ·
                        rfl

theorem cell23_1756772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 1, 2, 3].length) (baseStart_1756772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756772 prefixEnd_1756772 := by exact prefixLift 1756772
  have htrace : WordTrace (prefixWord ++ tailWord_1756772) baseStart_1756772 baseEnd_1756772 := by
    simpa [prefixWord, tailWord_1756772, baseEnd_1756772] using wordTrace_append hprefix tailTrace_1756772
  have hstable : (prefixWord ++ tailWord_1756772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756772).length < 2 ^ (prefixWord ++ tailWord_1756772).sum := by decide
  have hdescent : baseEnd_1756772 < baseStart_1756772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756811 : List Nat := [1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 5]
def baseStart_1756811 : Nat := 118140960795 + 1756811 * 2 ^ 59
def prefixEnd_1756811 : Nat := 4983230072969 + 3 ^ 40 * 1756811 * 2
def baseEnd_1756811 : Nat := 902088462106031202583079

theorem tailTrace_1756811 : CollatzResearch.WordTrace tailWord_1756811 prefixEnd_1756811 902088462106031202583079 := by
  unfold tailWord_1756811
  simp only [CollatzResearch.WordTrace]
  refine ⟨64076161238381261276550287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42717440825587507517700191 64076161238381261276550287)
  ·
    refine ⟨96114241857571891914825431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64076161238381261276550287 96114241857571891914825431)
    ·
      refine ⟨144171362786357837872238147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96114241857571891914825431 144171362786357837872238147)
      ·
        refine ⟨216257044179536756808357221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144171362786357837872238147 216257044179536756808357221)
        ·
          refine ⟨40548195783663141901566979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216257044179536756808357221 40548195783663141901566979)
          ·
            refine ⟨60822293675494712852350469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40548195783663141901566979 60822293675494712852350469)
            ·
              refine ⟨11404180064155258659815713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60822293675494712852350469 11404180064155258659815713)
              ·
                refine ⟨8553135048116443994861785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11404180064155258659815713 8553135048116443994861785)
                ·
                  refine ⟨6414851286087332996146339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8553135048116443994861785 6414851286087332996146339)
                  ·
                    refine ⟨9622276929130999494219509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6414851286087332996146339 9622276929130999494219509)
                    ·
                      refine ⟨902088462106031202583079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9622276929130999494219509 902088462106031202583079)
                      ·
                        rfl

theorem cell23_1756811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 5].length) (baseStart_1756811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756811 prefixEnd_1756811 := by exact prefixLift 1756811
  have htrace : WordTrace (prefixWord ++ tailWord_1756811) baseStart_1756811 baseEnd_1756811 := by
    simpa [prefixWord, tailWord_1756811, baseEnd_1756811] using wordTrace_append hprefix tailTrace_1756811
  have hstable : (prefixWord ++ tailWord_1756811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756811).length < 2 ^ (prefixWord ++ tailWord_1756811).sum := by decide
  have hdescent : baseEnd_1756811 < baseStart_1756811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756821 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 1, 4, 4]
def baseStart_1756821 : Nat := 118140960795 + 1756821 * 2 ^ 59
def prefixEnd_1756821 : Nat := 4983230072969 + 3 ^ 40 * 1756821 * 2
def baseEnd_1756821 : Nat := 902093596912576163458033

theorem tailTrace_1756821 : CollatzResearch.WordTrace tailWord_1756821 prefixEnd_1756821 902093596912576163458033 := by
  unfold tailWord_1756821
  simp only [CollatzResearch.WordTrace]
  refine ⟨64076525968345032984414317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42717683978896688656276211 64076525968345032984414317)
  ·
    refine ⟨24028697238129387369155369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64076525968345032984414317 24028697238129387369155369)
    ·
      refine ⟨18021522928597040526866527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24028697238129387369155369 18021522928597040526866527)
      ·
        refine ⟨27032284392895560790299791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18021522928597040526866527 27032284392895560790299791)
        ·
          refine ⟨40548426589343341185449687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27032284392895560790299791 40548426589343341185449687)
          ·
            refine ⟨60822639884015011778174531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40548426589343341185449687 60822639884015011778174531)
            ·
              refine ⟨91233959826022517667261797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60822639884015011778174531 91233959826022517667261797)
              ·
                refine ⟨17106367467379222062611587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91233959826022517667261797 17106367467379222062611587)
                ·
                  refine ⟨25659551201068833093917381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17106367467379222062611587 25659551201068833093917381)
                  ·
                    refine ⟨4811165850200406205109509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25659551201068833093917381 4811165850200406205109509)
                    ·
                      refine ⟨902093596912576163458033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4811165850200406205109509 902093596912576163458033)
                      ·
                        rfl

theorem cell23_1756821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_1756821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756821 prefixEnd_1756821 := by exact prefixLift 1756821
  have htrace : WordTrace (prefixWord ++ tailWord_1756821) baseStart_1756821 baseEnd_1756821 := by
    simpa [prefixWord, tailWord_1756821, baseEnd_1756821] using wordTrace_append hprefix tailTrace_1756821
  have hstable : (prefixWord ++ tailWord_1756821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756821).length < 2 ^ (prefixWord ++ tailWord_1756821).sum := by decide
  have hdescent : baseEnd_1756821 < baseStart_1756821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756848 : List Nat := [2, 1, 1, 1, 2, 1, 4, 6, 5]
def baseStart_1756848 : Nat := 118140960795 + 1756848 * 2 ^ 59
def prefixEnd_1756848 : Nat := 4983230072969 + 3 ^ 40 * 1756848 * 2
def baseEnd_1756848 : Nat := 100234162321138617535601

theorem tailTrace_1756848 : CollatzResearch.WordTrace tailWord_1756848 prefixEnd_1756848 100234162321138617535601 := by
  unfold tailWord_1756848
  simp only [CollatzResearch.WordTrace]
  refine ⟨32038755369623608297823599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42718340492831477730431465 32038755369623608297823599)
  ·
    refine ⟨48058133054435412446735399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32038755369623608297823599 48058133054435412446735399)
    ·
      refine ⟨72087199581653118670103099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48058133054435412446735399 72087199581653118670103099)
      ·
        refine ⟨108130799372479678005154649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72087199581653118670103099 108130799372479678005154649)
        ·
          refine ⟨81098099529359758503865987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108130799372479678005154649 81098099529359758503865987)
          ·
            refine ⟨121647149294039637755798981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81098099529359758503865987 121647149294039637755798981)
            ·
              refine ⟨22808840492632432079212309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121647149294039637755798981 22808840492632432079212309)
              ·
                refine ⟨1069164398092145253713077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22808840492632432079212309 1069164398092145253713077)
                ·
                  refine ⟨100234162321138617535601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1069164398092145253713077 100234162321138617535601)
                  ·
                    rfl

theorem cell23_1756848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6, 5].length) (baseStart_1756848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756848 prefixEnd_1756848 := by exact prefixLift 1756848
  have htrace : WordTrace (prefixWord ++ tailWord_1756848) baseStart_1756848 baseEnd_1756848 := by
    simpa [prefixWord, tailWord_1756848, baseEnd_1756848] using wordTrace_append hprefix tailTrace_1756848
  have hstable : (prefixWord ++ tailWord_1756848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756848).length < 2 ^ (prefixWord ++ tailWord_1756848).sum := by decide
  have hdescent : baseEnd_1756848 < baseStart_1756848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756871 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 7]
def baseStart_1756871 : Nat := 118140960795 + 1756871 * 2 ^ 59
def prefixEnd_1756871 : Nat := 4983230072969 + 3 ^ 40 * 1756871 * 2
def baseEnd_1756871 : Nat := 902119270945300967832803

theorem tailTrace_1756871 : CollatzResearch.WordTrace tailWord_1756871 prefixEnd_1756871 902119270945300967832803 := by
  unfold tailWord_1756871
  simp only [CollatzResearch.WordTrace]
  refine ⟨64078349618163891523734467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42718899745442594349156311 64078349618163891523734467)
  ·
    refine ⟨96117524427245837285601701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64078349618163891523734467 96117524427245837285601701)
    ·
      refine ⟨18022035830108594491050319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96117524427245837285601701 18022035830108594491050319)
      ·
        refine ⟨27033053745162891736575479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18022035830108594491050319 27033053745162891736575479)
        ·
          refine ⟨40549580617744337604863219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27033053745162891736575479 40549580617744337604863219)
          ·
            refine ⟨60824370926616506407294829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40549580617744337604863219 60824370926616506407294829)
            ·
              refine ⟨22809139097481189902735561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60824370926616506407294829 22809139097481189902735561)
              ·
                refine ⟨17106854323110892427051671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22809139097481189902735561 17106854323110892427051671)
                ·
                  refine ⟨25660281484666338640577507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17106854323110892427051671 25660281484666338640577507)
                  ·
                    refine ⟨38490422226999507960866261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25660281484666338640577507 38490422226999507960866261)
                    ·
                      refine ⟨902119270945300967832803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38490422226999507960866261 902119270945300967832803)
                      ·
                        rfl

theorem cell23_1756871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_1756871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756871 prefixEnd_1756871 := by exact prefixLift 1756871
  have htrace : WordTrace (prefixWord ++ tailWord_1756871) baseStart_1756871 baseEnd_1756871 := by
    simpa [prefixWord, tailWord_1756871, baseEnd_1756871] using wordTrace_append hprefix tailTrace_1756871
  have hstable : (prefixWord ++ tailWord_1756871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756871).length < 2 ^ (prefixWord ++ tailWord_1756871).sum := by decide
  have hdescent : baseEnd_1756871 < baseStart_1756871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756899 : List Nat := [1, 1, 1, 7, 2, 2, 2, 2, 5]
def baseStart_1756899 : Nat := 118140960795 + 1756899 * 2 ^ 59
def prefixEnd_1756899 : Nat := 4983230072969 + 3 ^ 40 * 1756899 * 2
def baseEnd_1756899 : Nat := 100237072044847428698075

theorem tailTrace_1756899 : CollatzResearch.WordTrace tailWord_1756899 prefixEnd_1756899 100237072044847428698075 := by
  unfold tailWord_1756899
  simp only [CollatzResearch.WordTrace]
  refine ⟨64079370862062452305753751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42719580574708301537169167 64079370862062452305753751)
  ·
    refine ⟨96119056293093678458630627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64079370862062452305753751 96119056293093678458630627)
    ·
      refine ⟨144178584439640517687945941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96119056293093678458630627 144178584439640517687945941)
      ·
        refine ⟨3379185572804074633311233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 144178584439640517687945941 3379185572804074633311233)
        ·
          refine ⟨2534389179603055974983425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3379185572804074633311233 2534389179603055974983425)
          ·
            refine ⟨1900791884702291981237569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2534389179603055974983425 1900791884702291981237569)
            ·
              refine ⟨1425593913526718985928177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1900791884702291981237569 1425593913526718985928177)
              ·
                refine ⟨1069195435145039239446133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1425593913526718985928177 1069195435145039239446133)
                ·
                  refine ⟨100237072044847428698075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1069195435145039239446133 100237072044847428698075)
                  ·
                    rfl

theorem cell23_1756899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2, 5].length) (baseStart_1756899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756899 prefixEnd_1756899 := by exact prefixLift 1756899
  have htrace : WordTrace (prefixWord ++ tailWord_1756899) baseStart_1756899 baseEnd_1756899 := by
    simpa [prefixWord, tailWord_1756899, baseEnd_1756899] using wordTrace_append hprefix tailTrace_1756899
  have hstable : (prefixWord ++ tailWord_1756899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756899).length < 2 ^ (prefixWord ++ tailWord_1756899).sum := by decide
  have hdescent : baseEnd_1756899 < baseStart_1756899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756921 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 12]
def baseStart_1756921 : Nat := 118140960795 + 1756921 * 2 ^ 59
def prefixEnd_1756921 : Nat := 4983230072969 + 3 ^ 40 * 1756921 * 2
def baseEnd_1756921 : Nat := 100238327219780641356397

theorem tailTrace_1756921 : CollatzResearch.WordTrace tailWord_1756921 prefixEnd_1756921 100238327219780641356397 := by
  unfold tailWord_1756921
  simp only [CollatzResearch.WordTrace]
  refine ⟨64080173267982750063054617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42720115511988500042036411 64080173267982750063054617)
  ·
    refine ⟨48060129950987062547290963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64080173267982750063054617 48060129950987062547290963)
    ·
      refine ⟨72090194926480593820936445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48060129950987062547290963 72090194926480593820936445)
      ·
        refine ⟨27033823097430222682851167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72090194926480593820936445 27033823097430222682851167)
        ·
          refine ⟨40550734646145334024276751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27033823097430222682851167 40550734646145334024276751)
          ·
            refine ⟨60826101969218001036415127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40550734646145334024276751 60826101969218001036415127)
            ·
              refine ⟨91239152953827001554622691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60826101969218001036415127 91239152953827001554622691)
              ·
                refine ⟨136858729430740502331934037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91239152953827001554622691 136858729430740502331934037)
                ·
                  refine ⟨100238327219780641356397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 136858729430740502331934037 100238327219780641356397)
                  ·
                    rfl

theorem cell23_1756921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 12].length) (baseStart_1756921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756921 prefixEnd_1756921 := by exact prefixLift 1756921
  have htrace : WordTrace (prefixWord ++ tailWord_1756921) baseStart_1756921 baseEnd_1756921 := by
    simpa [prefixWord, tailWord_1756921, baseEnd_1756921] using wordTrace_append hprefix tailTrace_1756921
  have hstable : (prefixWord ++ tailWord_1756921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756921).length < 2 ^ (prefixWord ++ tailWord_1756921).sum := by decide
  have hdescent : baseEnd_1756921 < baseStart_1756921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756932 : List Nat := [2, 3, 2, 2, 1, 4, 1, 1, 2, 1, 4]
def baseStart_1756932 : Nat := 118140960795 + 1756932 * 2 ^ 59
def prefixEnd_1756932 : Nat := 4983230072969 + 3 ^ 40 * 1756932 * 2
def baseEnd_1756932 : Nat := 902150593265225229170023

theorem tailTrace_1756932 : CollatzResearch.WordTrace tailWord_1756932 prefixEnd_1756932 902150593265225229170023 := by
  unfold tailWord_1756932
  simp only [CollatzResearch.WordTrace]
  refine ⟨32040287235471449470852525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42720382980628599294470033 32040287235471449470852525)
  ·
    refine ⟨12015107713301793551569697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32040287235471449470852525 12015107713301793551569697)
    ·
      refine ⟨9011330784976345163677273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12015107713301793551569697 9011330784976345163677273)
      ·
        refine ⟨6758498088732258872757955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9011330784976345163677273 6758498088732258872757955)
        ·
          refine ⟨10137747133098388309136933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6758498088732258872757955 10137747133098388309136933)
          ·
            refine ⟨1900827587455947807963175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10137747133098388309136933 1900827587455947807963175)
            ·
              refine ⟨2851241381183921711944763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1900827587455947807963175 2851241381183921711944763)
              ·
                refine ⟨4276862071775882567917145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2851241381183921711944763 4276862071775882567917145)
                ·
                  refine ⟨3207646553831911925937859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4276862071775882567917145 3207646553831911925937859)
                  ·
                    refine ⟨4811469830747867888906789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3207646553831911925937859 4811469830747867888906789)
                    ·
                      refine ⟨902150593265225229170023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4811469830747867888906789 902150593265225229170023)
                      ·
                        rfl

theorem cell23_1756932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_1756932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756932 prefixEnd_1756932 := by exact prefixLift 1756932
  have htrace : WordTrace (prefixWord ++ tailWord_1756932) baseStart_1756932 baseEnd_1756932 := by
    simpa [prefixWord, tailWord_1756932, baseEnd_1756932] using wordTrace_append hprefix tailTrace_1756932
  have hstable : (prefixWord ++ tailWord_1756932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756932).length < 2 ^ (prefixWord ++ tailWord_1756932).sum := by decide
  have hdescent : baseEnd_1756932 < baseStart_1756932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756942 : List Nat := [4, 1, 1, 2, 1, 1, 3, 5, 1, 4]
def baseStart_1756942 : Nat := 118140960795 + 1756942 * 2 ^ 59
def prefixEnd_1756942 : Nat := 4983230072969 + 3 ^ 40 * 1756942 * 2
def baseEnd_1756942 : Nat := 300718576023923396681659

theorem tailTrace_1756942 : CollatzResearch.WordTrace tailWord_1756942 prefixEnd_1756942 300718576023923396681659 := by
  unfold tailWord_1756942
  simp only [CollatzResearch.WordTrace]
  refine ⟨8010117400113333831196135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42720626133937780433046053 8010117400113333831196135)
  ·
    refine ⟨12015176100170000746794203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8010117400113333831196135 12015176100170000746794203)
    ·
      refine ⟨18022764150255001120191305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12015176100170000746794203 18022764150255001120191305)
      ·
        refine ⟨13517073112691250840143479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18022764150255001120191305 13517073112691250840143479)
        ·
          refine ⟨20275609669036876260215219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13517073112691250840143479 20275609669036876260215219)
          ·
            refine ⟨30413414503555314390322829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20275609669036876260215219 30413414503555314390322829)
            ·
              refine ⟨11405030438833242896371061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30413414503555314390322829 11405030438833242896371061)
              ·
                refine ⟨1069221603640616521534787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11405030438833242896371061 1069221603640616521534787)
                ·
                  refine ⟨1603832405460924782302181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1069221603640616521534787 1603832405460924782302181)
                  ·
                    refine ⟨300718576023923396681659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1603832405460924782302181 300718576023923396681659)
                    ·
                      rfl

theorem cell23_1756942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_1756942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756942 prefixEnd_1756942 := by exact prefixLift 1756942
  have htrace : WordTrace (prefixWord ++ tailWord_1756942) baseStart_1756942 baseEnd_1756942 := by
    simpa [prefixWord, tailWord_1756942, baseEnd_1756942] using wordTrace_append hprefix tailTrace_1756942
  have hstable : (prefixWord ++ tailWord_1756942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756942).length < 2 ^ (prefixWord ++ tailWord_1756942).sum := by decide
  have hdescent : baseEnd_1756942 < baseStart_1756942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756975 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 4, 3, 2]
def baseStart_1756975 : Nat := 118140960795 + 1756975 * 2 ^ 59
def prefixEnd_1756975 : Nat := 4983230072969 + 3 ^ 40 * 1756975 * 2
def baseEnd_1756975 : Nat := 902172672933368560932325

theorem tailTrace_1756975 : CollatzResearch.WordTrace tailWord_1756975 prefixEnd_1756975 902172672933368560932325 := by
  unfold tailWord_1756975
  simp only [CollatzResearch.WordTrace]
  refine ⟨64082142809787117285520379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42721428539858078190346919 64082142809787117285520379)
  ·
    refine ⟨96123214214680675928280569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64082142809787117285520379 96123214214680675928280569)
    ·
      refine ⟨72092410661010506946210427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96123214214680675928280569 72092410661010506946210427)
      ·
        refine ⟨108138615991515760419315641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72092410661010506946210427 108138615991515760419315641)
        ·
          refine ⟨81103961993636820314486731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108138615991515760419315641 81103961993636820314486731)
          ·
            refine ⟨121655942990455230471730097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81103961993636820314486731 121655942990455230471730097)
            ·
              refine ⟨91241957242841422853797573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121655942990455230471730097 91241957242841422853797573)
              ·
                refine ⟨17107866983032766785087045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91241957242841422853797573 17107866983032766785087045)
                ·
                  refine ⟨3207725059318643772203821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17107866983032766785087045 3207725059318643772203821)
                  ·
                    refine ⟨1202896897244491414576433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3207725059318643772203821 1202896897244491414576433)
                    ·
                      refine ⟨902172672933368560932325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1202896897244491414576433 902172672933368560932325)
                      ·
                        rfl

theorem cell23_1756975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 3, 2].length) (baseStart_1756975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756975 prefixEnd_1756975 := by exact prefixLift 1756975
  have htrace : WordTrace (prefixWord ++ tailWord_1756975) baseStart_1756975 baseEnd_1756975 := by
    simpa [prefixWord, tailWord_1756975, baseEnd_1756975] using wordTrace_append hprefix tailTrace_1756975
  have hstable : (prefixWord ++ tailWord_1756975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756975).length < 2 ^ (prefixWord ++ tailWord_1756975).sum := by decide
  have hdescent : baseEnd_1756975 < baseStart_1756975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756999 : List Nat := [1, 1, 4, 1, 2, 1, 5, 3, 1, 1, 3]
def baseStart_1756999 : Nat := 118140960795 + 1756999 * 2 ^ 59
def prefixEnd_1756999 : Nat := 4983230072969 + 3 ^ 40 * 1756999 * 2
def baseEnd_1756999 : Nat := 902184996469076467032215

theorem tailTrace_1756999 : CollatzResearch.WordTrace tailWord_1756999 prefixEnd_1756999 902184996469076467032215 := by
  unfold tailWord_1756999
  simp only [CollatzResearch.WordTrace]
  refine ⟨64083018161700169384394051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42722012107800112922929367 64083018161700169384394051)
  ·
    refine ⟨96124527242550254076591077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64083018161700169384394051 96124527242550254076591077)
    ·
      refine ⟨18023348857978172639360827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96124527242550254076591077 18023348857978172639360827)
      ·
        refine ⟨27035023286967258959041241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18023348857978172639360827 27035023286967258959041241)
        ·
          refine ⟨20276267465225444219280931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27035023286967258959041241 20276267465225444219280931)
          ·
            refine ⟨30414401197838166328921397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20276267465225444219280931 30414401197838166328921397)
            ·
              refine ⟨2851350112297328093336381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30414401197838166328921397 2851350112297328093336381)
              ·
                refine ⟨1069256292111498035001143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2851350112297328093336381 1069256292111498035001143)
                ·
                  refine ⟨1603884438167247052501715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1069256292111498035001143 1603884438167247052501715)
                  ·
                    refine ⟨2405826657250870578752573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1603884438167247052501715 2405826657250870578752573)
                    ·
                      refine ⟨902184996469076467032215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2405826657250870578752573 902184996469076467032215)
                      ·
                        rfl

theorem cell23_1756999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3, 1, 1, 3].length) (baseStart_1756999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1756999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1756999 prefixEnd_1756999 := by exact prefixLift 1756999
  have htrace : WordTrace (prefixWord ++ tailWord_1756999) baseStart_1756999 baseEnd_1756999 := by
    simpa [prefixWord, tailWord_1756999, baseEnd_1756999] using wordTrace_append hprefix tailTrace_1756999
  have hstable : (prefixWord ++ tailWord_1756999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756999).length < 2 ^ (prefixWord ++ tailWord_1756999).sum := by decide
  have hdescent : baseEnd_1756999 < baseStart_1756999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757018 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6]
def baseStart_1757018 : Nat := 118140960795 + 1757018 * 2 ^ 59
def prefixEnd_1757018 : Nat := 4983230072969 + 3 ^ 40 * 1757018 * 2
def baseEnd_1757018 : Nat := 902194752601511892694627

theorem tailTrace_1757018 : CollatzResearch.WordTrace tailWord_1757018 prefixEnd_1757018 902194752601511892694627 := by
  unfold tailWord_1757018
  simp only [CollatzResearch.WordTrace]
  refine ⟨16020927787157833907333927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42722474099087557086223805 16020927787157833907333927)
  ·
    refine ⟨24031391680736750861000891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16020927787157833907333927 24031391680736750861000891)
    ·
      refine ⟨36047087521105126291501337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24031391680736750861000891 36047087521105126291501337)
      ·
        refine ⟨27035315640828844718626003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36047087521105126291501337 27035315640828844718626003)
        ·
          refine ⟨40552973461243267077939005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27035315640828844718626003 40552973461243267077939005)
          ·
            refine ⟨15207365047966225154227127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40552973461243267077939005 15207365047966225154227127)
            ·
              refine ⟨22811047571949337731340691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15207365047966225154227127 22811047571949337731340691)
              ·
                refine ⟨34216571357924006597011037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22811047571949337731340691 34216571357924006597011037)
                ·
                  refine ⟨12831214259221502473879139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34216571357924006597011037 12831214259221502473879139)
                  ·
                    refine ⟨19246821388832253710818709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12831214259221502473879139 19246821388832253710818709)
                    ·
                      refine ⟨902194752601511892694627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19246821388832253710818709 902194752601511892694627)
                      ·
                        rfl

theorem cell23_1757018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_1757018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757018 prefixEnd_1757018 := by exact prefixLift 1757018
  have htrace : WordTrace (prefixWord ++ tailWord_1757018) baseStart_1757018 baseEnd_1757018 := by
    simpa [prefixWord, tailWord_1757018, baseEnd_1757018] using wordTrace_append hprefix tailTrace_1757018
  have hstable : (prefixWord ++ tailWord_1757018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757018).length < 2 ^ (prefixWord ++ tailWord_1757018).sum := by decide
  have hdescent : baseEnd_1757018 < baseStart_1757018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757025 : List Nat := [1, 2, 3, 1, 1, 1, 4, 2, 3, 2, 3]
def baseStart_1757025 : Nat := 118140960795 + 1757025 * 2 ^ 59
def prefixEnd_1757025 : Nat := 4983230072969 + 3 ^ 40 * 1757025 * 2
def baseEnd_1757025 : Nat := 902198346966093365307095

theorem tailTrace_1757025 : CollatzResearch.WordTrace tailWord_1757025 prefixEnd_1757025 902198346966093365307095 := by
  unfold tailWord_1757025
  simp only [CollatzResearch.WordTrace]
  refine ⟨64083966459605975824840529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42722644306403983883227019 64083966459605975824840529)
  ·
    refine ⟨48062974844704481868630397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64083966459605975824840529 48062974844704481868630397)
    ·
      refine ⟨18023615566764180700736399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48062974844704481868630397 18023615566764180700736399)
      ·
        refine ⟨27035423350146271051104599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18023615566764180700736399 27035423350146271051104599)
        ·
          refine ⟨40553135025219406576656899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27035423350146271051104599 40553135025219406576656899)
          ·
            refine ⟨60829702537829109864985349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40553135025219406576656899 60829702537829109864985349)
            ·
              refine ⟨11405569225842958099684753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60829702537829109864985349 11405569225842958099684753)
              ·
                refine ⟨8554176919382218574763565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11405569225842958099684753 8554176919382218574763565)
                ·
                  refine ⟨3207816344768331965536337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8554176919382218574763565 3207816344768331965536337)
                  ·
                    refine ⟨2405862258576248974152253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3207816344768331965536337 2405862258576248974152253)
                    ·
                      refine ⟨902198346966093365307095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2405862258576248974152253 902198346966093365307095)
                      ·
                        rfl

theorem cell23_1757025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_1757025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757025 prefixEnd_1757025 := by exact prefixLift 1757025
  have htrace : WordTrace (prefixWord ++ tailWord_1757025) baseStart_1757025 baseEnd_1757025 := by
    simpa [prefixWord, tailWord_1757025, baseEnd_1757025] using wordTrace_append hprefix tailTrace_1757025
  have hstable : (prefixWord ++ tailWord_1757025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757025).length < 2 ^ (prefixWord ++ tailWord_1757025).sum := by decide
  have hdescent : baseEnd_1757025 < baseStart_1757025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757032 : List Nat := [2, 1, 4, 2, 1, 1, 3, 3, 2, 4]
def baseStart_1757032 : Nat := 118140960795 + 1757032 * 2 ^ 59
def prefixEnd_1757032 : Nat := 4983230072969 + 3 ^ 40 * 1757032 * 2
def baseEnd_1757032 : Nat := 300733980443558279306521

theorem tailTrace_1757032 : CollatzResearch.WordTrace tailWord_1757032 prefixEnd_1757032 300733980443558279306521 := by
  unfold tailWord_1757032
  simp only [CollatzResearch.WordTrace]
  refine ⟨32042110885290308010172675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42722814513720410680230233 32042110885290308010172675)
  ·
    refine ⟨48063166327935462015259013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32042110885290308010172675 48063166327935462015259013)
    ·
      refine ⟨9011843686487899127861065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48063166327935462015259013 9011843686487899127861065)
      ·
        refine ⟨6758882764865924345895799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9011843686487899127861065 6758882764865924345895799)
        ·
          refine ⟨10138324147298886518843699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6758882764865924345895799 10138324147298886518843699)
          ·
            refine ⟨15207486220948329778265549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10138324147298886518843699 15207486220948329778265549)
            ·
              refine ⟨5702807332855623666849581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15207486220948329778265549 5702807332855623666849581)
              ·
                refine ⟨2138552749820858875068593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5702807332855623666849581 2138552749820858875068593)
                ·
                  refine ⟨1603914562365644156301445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2138552749820858875068593 1603914562365644156301445)
                  ·
                    refine ⟨300733980443558279306521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1603914562365644156301445 300733980443558279306521)
                    ·
                      rfl

theorem cell23_1757032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_1757032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757032 prefixEnd_1757032 := by exact prefixLift 1757032
  have htrace : WordTrace (prefixWord ++ tailWord_1757032) baseStart_1757032 baseEnd_1757032 := by
    simpa [prefixWord, tailWord_1757032, baseEnd_1757032] using wordTrace_append hprefix tailTrace_1757032
  have hstable : (prefixWord ++ tailWord_1757032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757032).length < 2 ^ (prefixWord ++ tailWord_1757032).sum := by decide
  have hdescent : baseEnd_1757032 < baseStart_1757032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757059 : List Nat := [1, 1, 1, 3, 4, 3, 3, 1, 1, 2, 3]
def baseStart_1757059 : Nat := 118140960795 + 1757059 * 2 ^ 59
def prefixEnd_1757059 : Nat := 4983230072969 + 3 ^ 40 * 1757059 * 2
def baseEnd_1757059 : Nat := 902215805308346232281939

theorem tailTrace_1757059 : CollatzResearch.WordTrace tailWord_1757059 prefixEnd_1757059 902215805308346232281939 := by
  unfold tailWord_1757059
  simp only [CollatzResearch.WordTrace]
  refine ⟨64085206541482799631578231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42723471027655199754385487 64085206541482799631578231)
  ·
    refine ⟨96127809812224199447367347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64085206541482799631578231 96127809812224199447367347)
    ·
      refine ⟨144191714718336299171051021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96127809812224199447367347 144191714718336299171051021)
      ·
        refine ⟨54071893019376112189144133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144191714718336299171051021 54071893019376112189144133)
        ·
          refine ⟨10138479941133021035464525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54071893019376112189144133 10138479941133021035464525)
          ·
            refine ⟨3801929977924882888299197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10138479941133021035464525 3801929977924882888299197)
            ·
              refine ⟨1425723741721831083112199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3801929977924882888299197 1425723741721831083112199)
              ·
                refine ⟨2138585612582746624668299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1425723741721831083112199 2138585612582746624668299)
                ·
                  refine ⟨3207878418874119937002449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2138585612582746624668299 3207878418874119937002449)
                  ·
                    refine ⟨2405908814155589952751837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3207878418874119937002449 2405908814155589952751837)
                    ·
                      refine ⟨902215805308346232281939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2405908814155589952751837 902215805308346232281939)
                      ·
                        rfl

theorem cell23_1757059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 1, 2, 3].length) (baseStart_1757059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757059 prefixEnd_1757059 := by exact prefixLift 1757059
  have htrace : WordTrace (prefixWord ++ tailWord_1757059) baseStart_1757059 baseEnd_1757059 := by
    simpa [prefixWord, tailWord_1757059, baseEnd_1757059] using wordTrace_append hprefix tailTrace_1757059
  have hstable : (prefixWord ++ tailWord_1757059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757059).length < 2 ^ (prefixWord ++ tailWord_1757059).sum := by decide
  have hdescent : baseEnd_1757059 < baseStart_1757059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757072 : List Nat := [2, 1, 1, 1, 1, 1, 2, 8, 2, 1, 3]
def baseStart_1757072 : Nat := 118140960795 + 1757072 * 2 ^ 59
def prefixEnd_1757072 : Nat := 4983230072969 + 3 ^ 40 * 1757072 * 2
def baseEnd_1757072 : Nat := 902222480556854681419379

theorem tailTrace_1757072 : CollatzResearch.WordTrace tailWord_1757072 prefixEnd_1757072 902222480556854681419379 := by
  unfold tailWord_1757072
  simp only [CollatzResearch.WordTrace]
  refine ⟨32042840345217851425900735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42723787126957135234534313 32042840345217851425900735)
  ·
    refine ⟨48064260517826777138851103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32042840345217851425900735 48064260517826777138851103)
    ·
      refine ⟨72096390776740165708276655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48064260517826777138851103 72096390776740165708276655)
      ·
        refine ⟨108144586165110248562414983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72096390776740165708276655 108144586165110248562414983)
        ·
          refine ⟨162216879247665372843622475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108144586165110248562414983 162216879247665372843622475)
          ·
            refine ⟨243325318871498059265433713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162216879247665372843622475 243325318871498059265433713)
            ·
              refine ⟨182493989153623544449075285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243325318871498059265433713 182493989153623544449075285)
              ·
                refine ⟨2138601435394025911512601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 182493989153623544449075285 2138601435394025911512601)
                ·
                  refine ⟨1603951076545519433634451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2138601435394025911512601 1603951076545519433634451)
                  ·
                    refine ⟨2405926614818279150451677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1603951076545519433634451 2405926614818279150451677)
                    ·
                      refine ⟨902222480556854681419379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2405926614818279150451677 902222480556854681419379)
                      ·
                        rfl

theorem cell23_1757072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 2, 1, 3].length) (baseStart_1757072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757072 prefixEnd_1757072 := by exact prefixLift 1757072
  have htrace : WordTrace (prefixWord ++ tailWord_1757072) baseStart_1757072 baseEnd_1757072 := by
    simpa [prefixWord, tailWord_1757072, baseEnd_1757072] using wordTrace_append hprefix tailTrace_1757072
  have hstable : (prefixWord ++ tailWord_1757072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757072).length < 2 ^ (prefixWord ++ tailWord_1757072).sum := by decide
  have hdescent : baseEnd_1757072 < baseStart_1757072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757086 : List Nat := [4, 3, 1, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_1757086 : Nat := 118140960795 + 1757086 * 2 ^ 59
def prefixEnd_1757086 : Nat := 4983230072969 + 3 ^ 40 * 1757086 * 2
def baseEnd_1757086 : Nat := 902229669286017626644315

theorem tailTrace_1757086 : CollatzResearch.WordTrace tailWord_1757086 prefixEnd_1757086 902229669286017626644315 := by
  unfold tailWord_1757086
  simp only [CollatzResearch.WordTrace]
  refine ⟨8010773914048122905351389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42724127541589988828540741 8010773914048122905351389)
  ·
    refine ⟨3004040217768046089506771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8010773914048122905351389 3004040217768046089506771)
    ·
      refine ⟨4506060326652069134260157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3004040217768046089506771 4506060326652069134260157)
      ·
        refine ⟨1689772622494525925347559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4506060326652069134260157 1689772622494525925347559)
        ·
          refine ⟨2534658933741788888021339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1689772622494525925347559 2534658933741788888021339)
          ·
            refine ⟨3801988400612683332032009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2534658933741788888021339 3801988400612683332032009)
            ·
              refine ⟨2851491300459512499024007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3801988400612683332032009 2851491300459512499024007)
              ·
                refine ⟨4277236950689268748536011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2851491300459512499024007 4277236950689268748536011)
                ·
                  refine ⟨6415855426033903122804017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4277236950689268748536011 6415855426033903122804017)
                  ·
                    refine ⟨4811891569525427342103013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6415855426033903122804017 4811891569525427342103013)
                    ·
                      refine ⟨902229669286017626644315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4811891569525427342103013 902229669286017626644315)
                      ·
                        rfl

theorem cell23_1757086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_1757086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757086 prefixEnd_1757086 := by exact prefixLift 1757086
  have htrace : WordTrace (prefixWord ++ tailWord_1757086) baseStart_1757086 baseEnd_1757086 := by
    simpa [prefixWord, tailWord_1757086, baseEnd_1757086] using wordTrace_append hprefix tailTrace_1757086
  have hstable : (prefixWord ++ tailWord_1757086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757086).length < 2 ^ (prefixWord ++ tailWord_1757086).sum := by decide
  have hdescent : baseEnd_1757086 < baseStart_1757086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757089 : List Nat := [1, 2, 3, 4, 2, 1, 2, 1, 1, 3, 3]
def baseStart_1757089 : Nat := 118140960795 + 1757089 * 2 ^ 59
def prefixEnd_1757089 : Nat := 4983230072969 + 3 ^ 40 * 1757089 * 2
def baseEnd_1757089 : Nat := 902231209727981114906801

theorem tailTrace_1757089 : CollatzResearch.WordTrace tailWord_1757089 prefixEnd_1757089 902231209727981114906801 := by
  unfold tailWord_1757089
  simp only [CollatzResearch.WordTrace]
  refine ⟨64086300731374114755170321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42724200487582743170113547 64086300731374114755170321)
  ·
    refine ⟨48064725548530586066377741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64086300731374114755170321 48064725548530586066377741)
    ·
      refine ⟨18024272080698969774891653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48064725548530586066377741 18024272080698969774891653)
      ·
        refine ⟨3379551015131056832792185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18024272080698969774891653 3379551015131056832792185)
        ·
          refine ⟨2534663261348292624594139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3379551015131056832792185 2534663261348292624594139)
          ·
            refine ⟨3801994892022438936891209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2534663261348292624594139 3801994892022438936891209)
            ·
              refine ⟨2851496169016829202668407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3801994892022438936891209 2851496169016829202668407)
              ·
                refine ⟨4277244253525243804002611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2851496169016829202668407 4277244253525243804002611)
                ·
                  refine ⟨6415866380287865706003917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4277244253525243804002611 6415866380287865706003917)
                  ·
                    refine ⟨2405949892607949639751469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6415866380287865706003917 2405949892607949639751469)
                    ·
                      refine ⟨902231209727981114906801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2405949892607949639751469 902231209727981114906801)
                      ·
                        rfl

theorem cell23_1757089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_1757089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757089 prefixEnd_1757089 := by exact prefixLift 1757089
  have htrace : WordTrace (prefixWord ++ tailWord_1757089) baseStart_1757089 baseEnd_1757089 := by
    simpa [prefixWord, tailWord_1757089, baseEnd_1757089] using wordTrace_append hprefix tailTrace_1757089
  have hstable : (prefixWord ++ tailWord_1757089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757089).length < 2 ^ (prefixWord ++ tailWord_1757089).sum := by decide
  have hdescent : baseEnd_1757089 < baseStart_1757089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757112 : List Nat := [2, 1, 2, 1, 2, 3, 1, 4, 1, 4, 2]
def baseStart_1757112 : Nat := 118140960795 + 1757112 * 2 ^ 59
def prefixEnd_1757112 : Nat := 4983230072969 + 3 ^ 40 * 1757112 * 2
def baseEnd_1757112 : Nat := 902243019783034524919195

theorem tailTrace_1757112 : CollatzResearch.WordTrace tailWord_1757112 prefixEnd_1757112 902243019783034524919195 := by
  unfold tailWord_1757112
  simp only [CollatzResearch.WordTrace]
  refine ⟨32043569805145394841628795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42724759740193859788838393 32043569805145394841628795)
  ·
    refine ⟨48065354707718092262443193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32043569805145394841628795 48065354707718092262443193)
    ·
      refine ⟨36049016030788569196832395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48065354707718092262443193 36049016030788569196832395)
      ·
        refine ⟨54073524046182853795248593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36049016030788569196832395 54073524046182853795248593)
        ·
          refine ⟨40555143034637140346436445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54073524046182853795248593 40555143034637140346436445)
          ·
            refine ⟨15208178637988927629913667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40555143034637140346436445 15208178637988927629913667)
            ·
              refine ⟨22812267956983391444870501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15208178637988927629913667 22812267956983391444870501)
              ·
                refine ⟨4277300241934385895913219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22812267956983391444870501 4277300241934385895913219)
                ·
                  refine ⟨6415950362901578843869829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4277300241934385895913219 6415950362901578843869829)
                  ·
                    refine ⟨1202990693044046033225593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6415950362901578843869829 1202990693044046033225593)
                    ·
                      refine ⟨902243019783034524919195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1202990693044046033225593 902243019783034524919195)
                      ·
                        rfl

theorem cell23_1757112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 1, 4, 2].length) (baseStart_1757112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757112 prefixEnd_1757112 := by exact prefixLift 1757112
  have htrace : WordTrace (prefixWord ++ tailWord_1757112) baseStart_1757112 baseEnd_1757112 := by
    simpa [prefixWord, tailWord_1757112, baseEnd_1757112] using wordTrace_append hprefix tailTrace_1757112
  have hstable : (prefixWord ++ tailWord_1757112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757112).length < 2 ^ (prefixWord ++ tailWord_1757112).sum := by decide
  have hdescent : baseEnd_1757112 < baseStart_1757112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757135 : List Nat := [1, 1, 2, 1, 1, 5, 4, 1, 7]
def baseStart_1757135 : Nat := 118140960795 + 1757135 * 2 ^ 59
def prefixEnd_1757135 : Nat := 4983230072969 + 3 ^ 40 * 1757135 * 2
def baseEnd_1757135 : Nat := 100250536648676437214621

theorem tailTrace_1757135 : CollatzResearch.WordTrace tailWord_1757135 prefixEnd_1757135 100250536648676437214621 := by
  unfold tailWord_1757135
  simp only [CollatzResearch.WordTrace]
  refine ⟨64087978489207464611344859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42725318992804976407563239 64087978489207464611344859)
  ·
    refine ⟨96131967733811196917017289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64087978489207464611344859 96131967733811196917017289)
    ·
      refine ⟨72098975800358397687762967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96131967733811196917017289 72098975800358397687762967)
      ·
        refine ⟨108148463700537596531644451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72098975800358397687762967 108148463700537596531644451)
        ·
          refine ⟨162222695550806394797466677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108148463700537596531644451 162222695550806394797466677)
          ·
            refine ⟨15208377707888099512262501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162222695550806394797466677 15208377707888099512262501)
            ·
              refine ⟨2851570820229018658549219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15208377707888099512262501 2851570820229018658549219)
              ·
                refine ⟨4277356230343527987823829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2851570820229018658549219 4277356230343527987823829)
                ·
                  refine ⟨100250536648676437214621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4277356230343527987823829 100250536648676437214621)
                  ·
                    rfl

theorem cell23_1757135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 7].length) (baseStart_1757135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757135 prefixEnd_1757135 := by exact prefixLift 1757135
  have htrace : WordTrace (prefixWord ++ tailWord_1757135) baseStart_1757135 baseEnd_1757135 := by
    simpa [prefixWord, tailWord_1757135, baseEnd_1757135] using wordTrace_append hprefix tailTrace_1757135
  have hstable : (prefixWord ++ tailWord_1757135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757135).length < 2 ^ (prefixWord ++ tailWord_1757135).sum := by decide
  have hdescent : baseEnd_1757135 < baseStart_1757135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757146 : List Nat := [3, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2]
def baseStart_1757146 : Nat := 118140960795 + 1757146 * 2 ^ 59
def prefixEnd_1757146 : Nat := 4983230072969 + 3 ^ 40 * 1757146 * 2
def baseEnd_1757146 : Nat := 902260478125287391894039

theorem tailTrace_1757146 : CollatzResearch.WordTrace tailWord_1757146 prefixEnd_1757146 902260478125287391894039 := by
  unfold tailWord_1757146
  simp only [CollatzResearch.WordTrace]
  refine ⟨16022094923041903372498823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42725586461445075659996861 16022094923041903372498823)
  ·
    refine ⟨24033142384562855058748235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16022094923041903372498823 24033142384562855058748235)
    ·
      refine ⟨36049713576844282588122353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24033142384562855058748235 36049713576844282588122353)
      ·
        refine ⟨27037285182633211941091765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36049713576844282588122353 27037285182633211941091765)
        ·
          refine ⟨2534745485871863619477353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27037285182633211941091765 2534745485871863619477353)
          ·
            refine ⟨1901059114403897714608015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2534745485871863619477353 1901059114403897714608015)
            ·
              refine ⟨2851588671605846571912023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1901059114403897714608015 2851588671605846571912023)
              ·
                refine ⟨4277383007408769857868035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2851588671605846571912023 4277383007408769857868035)
                ·
                  refine ⟨6416074511113154786802053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4277383007408769857868035 6416074511113154786802053)
                  ·
                    refine ⟨1203013970833716522525385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6416074511113154786802053 1203013970833716522525385)
                    ·
                      refine ⟨902260478125287391894039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1203013970833716522525385 902260478125287391894039)
                      ·
                        rfl

theorem cell23_1757146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2].length) (baseStart_1757146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757146 prefixEnd_1757146 := by exact prefixLift 1757146
  have htrace : WordTrace (prefixWord ++ tailWord_1757146) baseStart_1757146 baseEnd_1757146 := by
    simpa [prefixWord, tailWord_1757146, baseEnd_1757146] using wordTrace_append hprefix tailTrace_1757146
  have hstable : (prefixWord ++ tailWord_1757146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757146).length < 2 ^ (prefixWord ++ tailWord_1757146).sum := by decide
  have hdescent : baseEnd_1757146 < baseStart_1757146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757197 : List Nat := [1, 7, 1, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_1757197 : Nat := 118140960795 + 1757197 * 2 ^ 59
def prefixEnd_1757197 : Nat := 4983230072969 + 3 ^ 40 * 1757197 * 2
def baseEnd_1757197 : Nat := 902286665638666692356305

theorem tailTrace_1757197 : CollatzResearch.WordTrace tailWord_1757197 prefixEnd_1757197 902286665638666692356305 := by
  unfold tailWord_1757197
  simp only [CollatzResearch.WordTrace]
  refine ⟨64090239814982849200101845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42726826543321899466734563 64090239814982849200101845)
  ·
    refine ⟨1502114995663660528127387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 64090239814982849200101845 1502114995663660528127387)
    ·
      refine ⟨2253172493495490792191081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1502114995663660528127387 2253172493495490792191081)
      ·
        refine ⟨1689879370121618094143311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2253172493495490792191081 1689879370121618094143311)
        ·
          refine ⟨2534819055182427141214967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1689879370121618094143311 2534819055182427141214967)
          ·
            refine ⟨3802228582773640711822451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2534819055182427141214967 3802228582773640711822451)
            ·
              refine ⟨5703342874160461067733677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3802228582773640711822451 5703342874160461067733677)
              ·
                refine ⟨2138753577810172900400129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5703342874160461067733677 2138753577810172900400129)
                ·
                  refine ⟨1604065183357629675300097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2138753577810172900400129 1604065183357629675300097)
                  ·
                    refine ⟨1203048887518222256475073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1604065183357629675300097 1203048887518222256475073)
                    ·
                      refine ⟨902286665638666692356305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1203048887518222256475073 902286665638666692356305)
                      ·
                        rfl

theorem cell23_1757197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_1757197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757197 prefixEnd_1757197 := by exact prefixLift 1757197
  have htrace : WordTrace (prefixWord ++ tailWord_1757197) baseStart_1757197 baseEnd_1757197 := by
    simpa [prefixWord, tailWord_1757197, baseEnd_1757197] using wordTrace_append hprefix tailTrace_1757197
  have hstable : (prefixWord ++ tailWord_1757197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757197).length < 2 ^ (prefixWord ++ tailWord_1757197).sum := by decide
  have hdescent : baseEnd_1757197 < baseStart_1757197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757265 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 1, 3, 7]
def baseStart_1757265 : Nat := 118140960795 + 1757265 * 2 ^ 59
def prefixEnd_1757265 : Nat := 4983230072969 + 3 ^ 40 * 1757265 * 2
def baseEnd_1757265 : Nat := 902321582323172426305991

theorem tailTrace_1757265 : CollatzResearch.WordTrace tailWord_1757265 prefixEnd_1757265 902321582323172426305991 := by
  unfold tailWord_1757265
  simp only [CollatzResearch.WordTrace]
  refine ⟨64092719978736496813577249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42728479985824331209051499 64092719978736496813577249)
  ·
    refine ⟨48069539984052372610182937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64092719978736496813577249 48069539984052372610182937)
    ·
      refine ⟨36052154988039279457637203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48069539984052372610182937 36052154988039279457637203)
      ·
        refine ⟨54078232482058919186455805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36052154988039279457637203 54078232482058919186455805)
        ·
          refine ⟨20279337180772094694920927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54078232482058919186455805 20279337180772094694920927)
          ·
            refine ⟨30419005771158142042381391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20279337180772094694920927 30419005771158142042381391)
            ·
              refine ⟨45628508656737213063572087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30419005771158142042381391 45628508656737213063572087)
              ·
                refine ⟨68442762985105819595358131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45628508656737213063572087 68442762985105819595358131)
                ·
                  refine ⟨102664144477658729393037197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68442762985105819595358131 102664144477658729393037197)
                  ·
                    refine ⟨38499054179122023522388949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102664144477658729393037197 38499054179122023522388949)
                    ·
                      refine ⟨902321582323172426305991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38499054179122023522388949 902321582323172426305991)
                      ·
                        rfl

theorem cell23_1757265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_1757265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757265 prefixEnd_1757265 := by exact prefixLift 1757265
  have htrace : WordTrace (prefixWord ++ tailWord_1757265) baseStart_1757265 baseEnd_1757265 := by
    simpa [prefixWord, tailWord_1757265, baseEnd_1757265] using wordTrace_append hprefix tailTrace_1757265
  have hstable : (prefixWord ++ tailWord_1757265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757265).length < 2 ^ (prefixWord ++ tailWord_1757265).sum := by decide
  have hdescent : baseEnd_1757265 < baseStart_1757265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757269 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 5, 1, 3]
def baseStart_1757269 : Nat := 118140960795 + 1757269 * 2 ^ 59
def prefixEnd_1757269 : Nat := 4983230072969 + 3 ^ 40 * 1757269 * 2
def baseEnd_1757269 : Nat := 902323636245790410655973

theorem tailTrace_1757269 : CollatzResearch.WordTrace tailWord_1757269 prefixEnd_1757269 902323636245790410655973 := by
  unfold tailWord_1757269
  simp only [CollatzResearch.WordTrace]
  refine ⟨64092865870722005496722861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42728577247148003664481907 64092865870722005496722861)
  ·
    refine ⟨24034824701520752061271073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64092865870722005496722861 24034824701520752061271073)
    ·
      refine ⟨18026118526140564045953305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24034824701520752061271073 18026118526140564045953305)
      ·
        refine ⟨13519588894605423034464979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18026118526140564045953305 13519588894605423034464979)
        ·
          refine ⟨20279383341908134551697469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13519588894605423034464979 20279383341908134551697469)
          ·
            refine ⟨7604768753215550456886551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20279383341908134551697469 7604768753215550456886551)
            ·
              refine ⟨11407153129823325685329827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7604768753215550456886551 11407153129823325685329827)
              ·
                refine ⟨17110729694734988527994741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11407153129823325685329827 17110729694734988527994741)
                ·
                  refine ⟨1604130908881405174499507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17110729694734988527994741 1604130908881405174499507)
                  ·
                    refine ⟨2406196363322107761749261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1604130908881405174499507 2406196363322107761749261)
                    ·
                      refine ⟨902323636245790410655973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2406196363322107761749261 902323636245790410655973)
                      ·
                        rfl

theorem cell23_1757269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_1757269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757269 prefixEnd_1757269 := by exact prefixLift 1757269
  have htrace : WordTrace (prefixWord ++ tailWord_1757269) baseStart_1757269 baseEnd_1757269 := by
    simpa [prefixWord, tailWord_1757269, baseEnd_1757269] using wordTrace_append hprefix tailTrace_1757269
  have hstable : (prefixWord ++ tailWord_1757269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757269).length < 2 ^ (prefixWord ++ tailWord_1757269).sum := by decide
  have hdescent : baseEnd_1757269 < baseStart_1757269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757272 : List Nat := [2, 1, 2, 2, 1, 4, 2, 1, 3, 5]
def baseStart_1757272 : Nat := 118140960795 + 1757272 * 2 ^ 59
def prefixEnd_1757272 : Nat := 4983230072969 + 3 ^ 40 * 1757272 * 2
def baseEnd_1757272 : Nat := 300775058895917966306153

theorem tailTrace_1757272 : CollatzResearch.WordTrace tailWord_1757272 prefixEnd_1757272 300775058895917966306153 := by
  unfold tailWord_1757272
  simp only [CollatzResearch.WordTrace]
  refine ⟨32046487644855568504541035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42728650193140758006054713 32046487644855568504541035)
  ·
    refine ⟨48069731467283352756811553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32046487644855568504541035 48069731467283352756811553)
    ·
      refine ⟨36052298600462514567608665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48069731467283352756811553 36052298600462514567608665)
      ·
        refine ⟨27039223950346885925706499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36052298600462514567608665 27039223950346885925706499)
        ·
          refine ⟨40558835925520328888559749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27039223950346885925706499 40558835925520328888559749)
          ·
            refine ⟨7604781736035061666604953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40558835925520328888559749 7604781736035061666604953)
            ·
              refine ⟨5703586302026296249953715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7604781736035061666604953 5703586302026296249953715)
              ·
                refine ⟨8555379453039444374930573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5703586302026296249953715 8555379453039444374930573)
                ·
                  refine ⟨3208267294889791640598965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8555379453039444374930573 3208267294889791640598965)
                  ·
                    refine ⟨300775058895917966306153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3208267294889791640598965 300775058895917966306153)
                    ·
                      rfl

theorem cell23_1757272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 3, 5].length) (baseStart_1757272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757272 prefixEnd_1757272 := by exact prefixLift 1757272
  have htrace : WordTrace (prefixWord ++ tailWord_1757272) baseStart_1757272 baseEnd_1757272 := by
    simpa [prefixWord, tailWord_1757272, baseEnd_1757272] using wordTrace_append hprefix tailTrace_1757272
  have hstable : (prefixWord ++ tailWord_1757272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757272).length < 2 ^ (prefixWord ++ tailWord_1757272).sum := by decide
  have hdescent : baseEnd_1757272 < baseStart_1757272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757279 : List Nat := [1, 1, 2, 3, 1, 1, 2, 5, 2, 3, 2]
def baseStart_1757279 : Nat := 118140960795 + 1757279 * 2 ^ 59
def prefixEnd_1757279 : Nat := 4983230072969 + 3 ^ 40 * 1757279 * 2
def baseEnd_1757279 : Nat := 902328771052335371530927

theorem tailTrace_1757279 : CollatzResearch.WordTrace tailWord_1757279 prefixEnd_1757279 902328771052335371530927 := by
  unfold tailWord_1757279
  simp only [CollatzResearch.WordTrace]
  refine ⟨64093230600685777204586891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42728820400457184803057927 64093230600685777204586891)
  ·
    refine ⟨96139845901028665806880337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64093230600685777204586891 96139845901028665806880337)
    ·
      refine ⟨72104884425771499355160253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96139845901028665806880337 72104884425771499355160253)
      ·
        refine ⟨27039331659664312258185095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72104884425771499355160253 27039331659664312258185095)
        ·
          refine ⟨40558997489496468387277643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27039331659664312258185095 40558997489496468387277643)
          ·
            refine ⟨60838496234244702580916465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40558997489496468387277643 60838496234244702580916465)
            ·
              refine ⟨45628872175683526935687349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60838496234244702580916465 45628872175683526935687349)
              ·
                refine ⟨4277706766470330650220689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45628872175683526935687349 4277706766470330650220689)
                ·
                  refine ⟨3208280074852747987665517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4277706766470330650220689 3208280074852747987665517)
                  ·
                    refine ⟨1203105028069780495374569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3208280074852747987665517 1203105028069780495374569)
                    ·
                      refine ⟨902328771052335371530927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1203105028069780495374569 902328771052335371530927)
                      ·
                        rfl

theorem cell23_1757279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 3, 2].length) (baseStart_1757279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757279 prefixEnd_1757279 := by exact prefixLift 1757279
  have htrace : WordTrace (prefixWord ++ tailWord_1757279) baseStart_1757279 baseEnd_1757279 := by
    simpa [prefixWord, tailWord_1757279, baseEnd_1757279] using wordTrace_append hprefix tailTrace_1757279
  have hstable : (prefixWord ++ tailWord_1757279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757279).length < 2 ^ (prefixWord ++ tailWord_1757279).sum := by decide
  have hdescent : baseEnd_1757279 < baseStart_1757279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757319 : List Nat := [1, 1, 4, 2, 1, 1, 2, 5, 2, 4]
def baseStart_1757319 : Nat := 118140960795 + 1757319 * 2 ^ 59
def prefixEnd_1757319 : Nat := 4983230072969 + 3 ^ 40 * 1757319 * 2
def baseEnd_1757319 : Nat := 300783103426171738343581

theorem tailTrace_1757319 : CollatzResearch.WordTrace tailWord_1757319 prefixEnd_1757319 300783103426171738343581 := by
  unfold tailWord_1757319
  simp only [CollatzResearch.WordTrace]
  refine ⟨64094689520540864036043011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42729793013693909357362007 64094689520540864036043011)
  ·
    refine ⟨96142034280811296054064517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64094689520540864036043011 96142034280811296054064517)
    ·
      refine ⟨18026631427652118010137097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96142034280811296054064517 18026631427652118010137097)
      ·
        refine ⟨13519973570739088507602823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18026631427652118010137097 13519973570739088507602823)
        ·
          refine ⟨20279960356108632761404235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13519973570739088507602823 20279960356108632761404235)
          ·
            refine ⟨30419940534162949142106353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20279960356108632761404235 30419940534162949142106353)
            ·
              refine ⟨22814955400622211856579765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30419940534162949142106353 22814955400622211856579765)
              ·
                refine ⟨2138902068808332361554353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22814955400622211856579765 2138902068808332361554353)
                ·
                  refine ⟨1604176551606249271165765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2138902068808332361554353 1604176551606249271165765)
                  ·
                    refine ⟨300783103426171738343581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1604176551606249271165765 300783103426171738343581)
                    ·
                      rfl

theorem cell23_1757319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_1757319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757319 prefixEnd_1757319 := by exact prefixLift 1757319
  have htrace : WordTrace (prefixWord ++ tailWord_1757319) baseStart_1757319 baseEnd_1757319 := by
    simpa [prefixWord, tailWord_1757319, baseEnd_1757319] using wordTrace_append hprefix tailTrace_1757319
  have hstable : (prefixWord ++ tailWord_1757319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757319).length < 2 ^ (prefixWord ++ tailWord_1757319).sum := by decide
  have hdescent : baseEnd_1757319 < baseStart_1757319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757346 : List Nat := [3, 3, 1, 3, 1, 2, 2, 1, 1, 1, 5]
def baseStart_1757346 : Nat := 118140960795 + 1757346 * 2 ^ 59
def prefixEnd_1757346 : Nat := 4983230072969 + 3 ^ 40 * 1757346 * 2
def baseEnd_1757346 : Nat := 902363174256186609393119

theorem tailTrace_1757346 : CollatzResearch.WordTrace tailWord_1757346 prefixEnd_1757346 902363174256186609393119 := by
  unfold tailWord_1757346
  simp only [CollatzResearch.WordTrace]
  refine ⟨16023918572860761911818973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42730449527628698431517261 16023918572860761911818973)
  ·
    refine ⟨6008969464822785716932115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16023918572860761911818973 6008969464822785716932115)
    ·
      refine ⟨9013454197234178575398173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6008969464822785716932115 9013454197234178575398173)
      ·
        refine ⟨3380045323962816965774315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9013454197234178575398173 3380045323962816965774315)
        ·
          refine ⟨5070067985944225448661473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3380045323962816965774315 5070067985944225448661473)
          ·
            refine ⟨3802550989458169086496105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5070067985944225448661473 3802550989458169086496105)
            ·
              refine ⟨2851913242093626814872079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3802550989458169086496105 2851913242093626814872079)
              ·
                refine ⟨4277869863140440222308119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2851913242093626814872079 4277869863140440222308119)
                ·
                  refine ⟨6416804794710660333462179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4277869863140440222308119 6416804794710660333462179)
                  ·
                    refine ⟨9625207192065990500193269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6416804794710660333462179 9625207192065990500193269)
                    ·
                      refine ⟨902363174256186609393119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9625207192065990500193269 902363174256186609393119)
                      ·
                        rfl

theorem cell23_1757346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_1757346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757346 prefixEnd_1757346 := by exact prefixLift 1757346
  have htrace : WordTrace (prefixWord ++ tailWord_1757346) baseStart_1757346 baseEnd_1757346 := by
    simpa [prefixWord, tailWord_1757346, baseEnd_1757346] using wordTrace_append hprefix tailTrace_1757346
  have hstable : (prefixWord ++ tailWord_1757346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757346).length < 2 ^ (prefixWord ++ tailWord_1757346).sum := by decide
  have hdescent : baseEnd_1757346 < baseStart_1757346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757362 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 2, 7]
def baseStart_1757362 : Nat := 118140960795 + 1757362 * 2 ^ 59
def prefixEnd_1757362 : Nat := 4983230072969 + 3 ^ 40 * 1757362 * 2
def baseEnd_1757362 : Nat := 300790463315552848931015

theorem tailTrace_1757362 : CollatzResearch.WordTrace tailWord_1757362 prefixEnd_1757362 300790463315552848931015 := by
  unfold tailWord_1757362
  simp only [CollatzResearch.WordTrace]
  refine ⟨16024064464846270594964585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42730838572923388253238893 16024064464846270594964585)
  ·
    refine ⟨12018048348634702946223439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16024064464846270594964585 12018048348634702946223439)
    ·
      refine ⟨18027072522952054419335159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12018048348634702946223439 18027072522952054419335159)
      ·
        refine ⟨27040608784428081629002739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18027072522952054419335159 27040608784428081629002739)
        ·
          refine ⟨40560913176642122443504109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27040608784428081629002739 40560913176642122443504109)
          ·
            refine ⟨15210342441240795916314041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40560913176642122443504109 15210342441240795916314041)
            ·
              refine ⟨11407756830930596937235531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15210342441240795916314041 11407756830930596937235531)
              ·
                refine ⟨17111635246395895405853297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11407756830930596937235531 17111635246395895405853297)
                ·
                  refine ⟨12833726434796921554389973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17111635246395895405853297 12833726434796921554389973)
                  ·
                    refine ⟨300790463315552848931015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12833726434796921554389973 300790463315552848931015)
                    ·
                      rfl

theorem cell23_1757362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_1757362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757362 prefixEnd_1757362 := by exact prefixLift 1757362
  have htrace : WordTrace (prefixWord ++ tailWord_1757362) baseStart_1757362 baseEnd_1757362 := by
    simpa [prefixWord, tailWord_1757362, baseEnd_1757362] using wordTrace_append hprefix tailTrace_1757362
  have hstable : (prefixWord ++ tailWord_1757362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757362).length < 2 ^ (prefixWord ++ tailWord_1757362).sum := by decide
  have hdescent : baseEnd_1757362 < baseStart_1757362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757386 : List Nat := [3, 1, 2, 1, 3, 1, 3, 1, 3, 3, 2]
def baseStart_1757386 : Nat := 118140960795 + 1757386 * 2 ^ 59
def prefixEnd_1757386 : Nat := 4983230072969 + 3 ^ 40 * 1757386 * 2
def baseEnd_1757386 : Nat := 902383713482366452892935

theorem tailTrace_1757386 : CollatzResearch.WordTrace tailWord_1757386 prefixEnd_1757386 902383713482366452892935 := by
  unfold tailWord_1757386
  simp only [CollatzResearch.WordTrace]
  refine ⟨16024283302824533619683003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42731422140865422985821341 16024283302824533619683003)
  ·
    refine ⟨24036424954236800429524505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16024283302824533619683003 24036424954236800429524505)
    ·
      refine ⟨18027318715677600322143379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24036424954236800429524505 18027318715677600322143379)
      ·
        refine ⟨27040978073516400483215069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18027318715677600322143379 27040978073516400483215069)
        ·
          refine ⟨10140366777568650181205651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27040978073516400483215069 10140366777568650181205651)
          ·
            refine ⟨15210550166352975271808477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10140366777568650181205651 15210550166352975271808477)
            ·
              refine ⟨5703956312382365726928179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15210550166352975271808477 5703956312382365726928179)
              ·
                refine ⟨8555934468573548590392269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5703956312382365726928179 8555934468573548590392269)
                ·
                  refine ⟨3208475425715080721397101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8555934468573548590392269 3208475425715080721397101)
                  ·
                    refine ⟨1203178284643155270523913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3208475425715080721397101 1203178284643155270523913)
                    ·
                      refine ⟨902383713482366452892935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1203178284643155270523913 902383713482366452892935)
                      ·
                        rfl

theorem cell23_1757386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 3, 3, 2].length) (baseStart_1757386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757386 prefixEnd_1757386 := by exact prefixLift 1757386
  have htrace : WordTrace (prefixWord ++ tailWord_1757386) baseStart_1757386 baseEnd_1757386 := by
    simpa [prefixWord, tailWord_1757386, baseEnd_1757386] using wordTrace_append hprefix tailTrace_1757386
  have hstable : (prefixWord ++ tailWord_1757386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757386).length < 2 ^ (prefixWord ++ tailWord_1757386).sum := by decide
  have hdescent : baseEnd_1757386 < baseStart_1757386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757411 : List Nat := [1, 1, 1, 8, 2, 1, 2, 2, 1, 2, 2]
def baseStart_1757411 : Nat := 118140960795 + 1757411 * 2 ^ 59
def prefixEnd_1757411 : Nat := 4983230072969 + 3 ^ 40 * 1757411 * 2
def baseEnd_1757411 : Nat := 902396550498728855080321

theorem tailTrace_1757411 : CollatzResearch.WordTrace tailWord_1757411 prefixEnd_1757411 902396550498728855080321 := by
  unfold tailWord_1757411
  simp only [CollatzResearch.WordTrace]
  refine ⟨64098045036207563748392087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42732030024138375832261391 64098045036207563748392087)
  ·
    refine ⟨96147067554311345622588131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64098045036207563748392087 96147067554311345622588131)
    ·
      refine ⟨144220601331467018433882197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96147067554311345622588131 144220601331467018433882197)
      ·
        refine ⟨1690085171853129122272057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 144220601331467018433882197 1690085171853129122272057)
        ·
          refine ⟨1267563878889846841704043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1690085171853129122272057 1267563878889846841704043)
          ·
            refine ⟨1901345818334770262556065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1267563878889846841704043 1901345818334770262556065)
            ·
              refine ⟨1426009363751077696917049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1901345818334770262556065 1426009363751077696917049)
              ·
                refine ⟨1069507022813308272687787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1426009363751077696917049 1069507022813308272687787)
                ·
                  refine ⟨1604260534219962409031681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1069507022813308272687787 1604260534219962409031681)
                  ·
                    refine ⟨1203195400664971806773761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1604260534219962409031681 1203195400664971806773761)
                    ·
                      refine ⟨902396550498728855080321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1203195400664971806773761 902396550498728855080321)
                      ·
                        rfl

theorem cell23_1757411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_1757411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757411 prefixEnd_1757411 := by exact prefixLift 1757411
  have htrace : WordTrace (prefixWord ++ tailWord_1757411) baseStart_1757411 baseEnd_1757411 := by
    simpa [prefixWord, tailWord_1757411, baseEnd_1757411] using wordTrace_append hprefix tailTrace_1757411
  have hstable : (prefixWord ++ tailWord_1757411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757411).length < 2 ^ (prefixWord ++ tailWord_1757411).sum := by decide
  have hdescent : baseEnd_1757411 < baseStart_1757411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757412 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 2, 3, 6]
def baseStart_1757412 : Nat := 118140960795 + 1757412 * 2 ^ 59
def prefixEnd_1757412 : Nat := 4983230072969 + 3 ^ 40 * 1757412 * 2
def baseEnd_1757412 : Nat := 902397063979383351167815

theorem tailTrace_1757412 : CollatzResearch.WordTrace tailWord_1757412 prefixEnd_1757412 902397063979383351167815 := by
  unfold tailWord_1757412
  simp only [CollatzResearch.WordTrace]
  refine ⟨32049040754601970459589245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42732054339469293946118993 32049040754601970459589245)
  ·
    refine ⟨12018390282975738922345967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32049040754601970459589245 12018390282975738922345967)
    ·
      refine ⟨18027585424463608383518951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12018390282975738922345967 18027585424463608383518951)
      ·
        refine ⟨27041378136695412575278427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18027585424463608383518951 27041378136695412575278427)
        ·
          refine ⟨40562067205043118862917641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27041378136695412575278427 40562067205043118862917641)
          ·
            refine ⟨30421550403782339147188231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40562067205043118862917641 30421550403782339147188231)
            ·
              refine ⟨45632325605673508720782347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30421550403782339147188231 45632325605673508720782347)
              ·
                refine ⟨68448488408510263081173521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45632325605673508720782347 68448488408510263081173521)
                ·
                  refine ⟨51336366306382697310880141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68448488408510263081173521 51336366306382697310880141)
                  ·
                    refine ⟨19251137364893511491580053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51336366306382697310880141 19251137364893511491580053)
                    ·
                      refine ⟨902397063979383351167815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19251137364893511491580053 902397063979383351167815)
                      ·
                        rfl

theorem cell23_1757412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_1757412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757412 prefixEnd_1757412 := by exact prefixLift 1757412
  have htrace : WordTrace (prefixWord ++ tailWord_1757412) baseStart_1757412 baseEnd_1757412 := by
    simpa [prefixWord, tailWord_1757412, baseEnd_1757412] using wordTrace_append hprefix tailTrace_1757412
  have hstable : (prefixWord ++ tailWord_1757412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757412).length < 2 ^ (prefixWord ++ tailWord_1757412).sum := by decide
  have hdescent : baseEnd_1757412 < baseStart_1757412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757529 : List Nat := [1, 2, 1, 2, 2, 2, 1, 6, 6]
def baseStart_1757529 : Nat := 118140960795 + 1757529 * 2 ^ 59
def prefixEnd_1757529 : Nat := 4983230072969 + 3 ^ 40 * 1757529 * 2
def baseEnd_1757529 : Nat := 100273015690662154822753

theorem tailTrace_1757529 : CollatzResearch.WordTrace tailWord_1757529 prefixEnd_1757529 100273015690662154822753 := by
  unfold tailWord_1757529
  simp only [CollatzResearch.WordTrace]
  refine ⟨64102348849780069901187641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42734899233186713267458427 64102348849780069901187641)
  ·
    refine ⟨48076761637335052425890731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64102348849780069901187641 48076761637335052425890731)
    ·
      refine ⟨72115142456002578638836097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48076761637335052425890731 72115142456002578638836097)
      ·
        refine ⟨54086356842001933979127073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72115142456002578638836097 54086356842001933979127073)
        ·
          refine ⟨40564767631501450484345305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54086356842001933979127073 40564767631501450484345305)
          ·
            refine ⟨30423575723626087863258979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40564767631501450484345305 30423575723626087863258979)
            ·
              refine ⟨45635363585439131794888469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30423575723626087863258979 45635363585439131794888469)
              ·
                refine ⟨2139157668067459302885397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45635363585439131794888469 2139157668067459302885397)
                ·
                  refine ⟨100273015690662154822753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2139157668067459302885397 100273015690662154822753)
                  ·
                    rfl

theorem cell23_1757529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 6].length) (baseStart_1757529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757529 prefixEnd_1757529 := by exact prefixLift 1757529
  have htrace : WordTrace (prefixWord ++ tailWord_1757529) baseStart_1757529 baseEnd_1757529 := by
    simpa [prefixWord, tailWord_1757529, baseEnd_1757529] using wordTrace_append hprefix tailTrace_1757529
  have hstable : (prefixWord ++ tailWord_1757529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757529).length < 2 ^ (prefixWord ++ tailWord_1757529).sum := by decide
  have hdescent : baseEnd_1757529 < baseStart_1757529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757589 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 5, 6]
def baseStart_1757589 : Nat := 118140960795 + 1757589 * 2 ^ 59
def prefixEnd_1757589 : Nat := 4983230072969 + 3 ^ 40 * 1757589 * 2
def baseEnd_1757589 : Nat := 300829316685076386218167

theorem tailTrace_1757589 : CollatzResearch.WordTrace tailWord_1757589 prefixEnd_1757589 300829316685076386218167 := by
  unfold tailWord_1757589
  simp only [CollatzResearch.WordTrace]
  refine ⟨64104537229562700148371821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42736358153041800098914547 64104537229562700148371821)
  ·
    refine ⟨24039201461086012555639433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64104537229562700148371821 24039201461086012555639433)
    ·
      refine ⟨18029401095814509416729575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24039201461086012555639433 18029401095814509416729575)
      ·
        refine ⟨27044101643721764125094363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18029401095814509416729575 27044101643721764125094363)
        ·
          refine ⟨40566152465582646187641545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27044101643721764125094363 40566152465582646187641545)
          ·
            refine ⟨30424614349186984640731159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40566152465582646187641545 30424614349186984640731159)
            ·
              refine ⟨45636921523780476961096739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30424614349186984640731159 45636921523780476961096739)
              ·
                refine ⟨68455382285670715441645109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45636921523780476961096739 68455382285670715441645109)
                ·
                  refine ⟨6417692089281629572654229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68455382285670715441645109 6417692089281629572654229)
                  ·
                    refine ⟨300829316685076386218167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6417692089281629572654229 300829316685076386218167)
                    ·
                      rfl

theorem cell23_1757589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_1757589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757589 prefixEnd_1757589 := by exact prefixLift 1757589
  have htrace : WordTrace (prefixWord ++ tailWord_1757589) baseStart_1757589 baseEnd_1757589 := by
    simpa [prefixWord, tailWord_1757589, baseEnd_1757589] using wordTrace_append hprefix tailTrace_1757589
  have hstable : (prefixWord ++ tailWord_1757589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757589).length < 2 ^ (prefixWord ++ tailWord_1757589).sum := by decide
  have hdescent : baseEnd_1757589 < baseStart_1757589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757609 : List Nat := [1, 2, 1, 1, 1, 1, 3, 5, 1, 1, 6]
def baseStart_1757609 : Nat := 118140960795 + 1757609 * 2 ^ 59
def prefixEnd_1757609 : Nat := 4983230072969 + 3 ^ 40 * 1757609 * 2
def baseEnd_1757609 : Nat := 902498219668319080404409

theorem tailTrace_1757609 : CollatzResearch.WordTrace tailWord_1757609 prefixEnd_1757609 902498219668319080404409 := by
  unfold tailWord_1757609
  simp only [CollatzResearch.WordTrace]
  refine ⟨64105266689490243564099881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42736844459660162376066587 64105266689490243564099881)
  ·
    refine ⟨48078950017117682673074911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64105266689490243564099881 48078950017117682673074911)
    ·
      refine ⟨72118425025676524009612367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48078950017117682673074911 72118425025676524009612367)
      ·
        refine ⟨108177637538514786014418551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72118425025676524009612367 108177637538514786014418551)
        ·
          refine ⟨162266456307772179021627827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108177637538514786014418551 162266456307772179021627827)
          ·
            refine ⟨243399684461658268532441741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162266456307772179021627827 243399684461658268532441741)
            ·
              refine ⟨91274881673121850699665653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243399684461658268532441741 91274881673121850699665653)
              ·
                refine ⟨8557020156855173503093655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91274881673121850699665653 8557020156855173503093655)
                ·
                  refine ⟨12835530235282760254640483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8557020156855173503093655 12835530235282760254640483)
                  ·
                    refine ⟨19253295352924140381960725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12835530235282760254640483 19253295352924140381960725)
                    ·
                      refine ⟨902498219668319080404409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19253295352924140381960725 902498219668319080404409)
                      ·
                        rfl

theorem cell23_1757609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 1, 6].length) (baseStart_1757609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757609 prefixEnd_1757609 := by exact prefixLift 1757609
  have htrace : WordTrace (prefixWord ++ tailWord_1757609) baseStart_1757609 baseEnd_1757609 := by
    simpa [prefixWord, tailWord_1757609, baseEnd_1757609] using wordTrace_append hprefix tailTrace_1757609
  have hstable : (prefixWord ++ tailWord_1757609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757609).length < 2 ^ (prefixWord ++ tailWord_1757609).sum := by decide
  have hdescent : baseEnd_1757609 < baseStart_1757609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757630 : List Nat := [4, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4]
def baseStart_1757630 : Nat := 118140960795 + 1757630 * 2 ^ 59
def prefixEnd_1757630 : Nat := 4983230072969 + 3 ^ 40 * 1757630 * 2
def baseEnd_1757630 : Nat := 902509002762063498241813

theorem tailTrace_1757630 : CollatzResearch.WordTrace tailWord_1757630 prefixEnd_1757630 902509002762063498241813 := by
  unfold tailWord_1757630
  simp only [CollatzResearch.WordTrace]
  refine ⟨8013254077801770518826793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42737355081609442767076229 8013254077801770518826793)
  ·
    refine ⟨6009940558351327889120095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8013254077801770518826793 6009940558351327889120095)
    ·
      refine ⟨9014910837526991833680143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6009940558351327889120095 9014910837526991833680143)
      ·
        refine ⟨13522366256290487750520215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9014910837526991833680143 13522366256290487750520215)
        ·
          refine ⟨20283549384435731625780323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13522366256290487750520215 20283549384435731625780323)
          ·
            refine ⟨30425324076653597438670485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20283549384435731625780323 30425324076653597438670485)
            ·
              refine ⟨1426187066093137379937679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30425324076653597438670485 1426187066093137379937679)
              ·
                refine ⟨2139280599139706069906519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1426187066093137379937679 2139280599139706069906519)
                ·
                  refine ⟨3208920898709559104859779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2139280599139706069906519 3208920898709559104859779)
                  ·
                    refine ⟨4813381348064338657289669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3208920898709559104859779 4813381348064338657289669)
                    ·
                      refine ⟨902509002762063498241813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4813381348064338657289669 902509002762063498241813)
                      ·
                        rfl

theorem cell23_1757630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_1757630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757630 prefixEnd_1757630 := by exact prefixLift 1757630
  have htrace : WordTrace (prefixWord ++ tailWord_1757630) baseStart_1757630 baseEnd_1757630 := by
    simpa [prefixWord, tailWord_1757630, baseEnd_1757630] using wordTrace_append hprefix tailTrace_1757630
  have hstable : (prefixWord ++ tailWord_1757630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757630).length < 2 ^ (prefixWord ++ tailWord_1757630).sum := by decide
  have hdescent : baseEnd_1757630 < baseStart_1757630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757640 : List Nat := [2, 1, 3, 1, 3, 4, 1, 2, 2, 4]
def baseStart_1757640 : Nat := 118140960795 + 1757640 * 2 ^ 59
def prefixEnd_1757640 : Nat := 4983230072969 + 3 ^ 40 * 1757640 * 2
def baseEnd_1757640 : Nat := 300838045856202819705589

theorem tailTrace_1757640 : CollatzResearch.WordTrace tailWord_1757640 prefixEnd_1757640 300838045856202819705589 := by
  unfold tailWord_1757640
  simp only [CollatzResearch.WordTrace]
  refine ⟨32053198676188967929239187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42737598234918623905652249 32053198676188967929239187)
  ·
    refine ⟨48079798014283451893858781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32053198676188967929239187 48079798014283451893858781)
    ·
      refine ⟨18029924255356294460197043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48079798014283451893858781 18029924255356294460197043)
      ·
        refine ⟨27044886383034441690295565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18029924255356294460197043 27044886383034441690295565)
        ·
          refine ⟨10141832393637915633860837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27044886383034441690295565 10141832393637915633860837)
          ·
            refine ⟨1901593573807109181348907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10141832393637915633860837 1901593573807109181348907)
            ·
              refine ⟨2852390360710663772023361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1901593573807109181348907 2852390360710663772023361)
              ·
                refine ⟨2139292770532997829017521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2852390360710663772023361 2139292770532997829017521)
                ·
                  refine ⟨1604469577899748371763141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2139292770532997829017521 1604469577899748371763141)
                  ·
                    refine ⟨300838045856202819705589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1604469577899748371763141 300838045856202819705589)
                    ·
                      rfl

theorem cell23_1757640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_1757640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757640 prefixEnd_1757640 := by exact prefixLift 1757640
  have htrace : WordTrace (prefixWord ++ tailWord_1757640) baseStart_1757640 baseEnd_1757640 := by
    simpa [prefixWord, tailWord_1757640, baseEnd_1757640] using wordTrace_append hprefix tailTrace_1757640
  have hstable : (prefixWord ++ tailWord_1757640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757640).length < 2 ^ (prefixWord ++ tailWord_1757640).sum := by decide
  have hdescent : baseEnd_1757640 < baseStart_1757640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757649 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 1, 9]
def baseStart_1757649 : Nat := 118140960795 + 1757649 * 2 ^ 59
def prefixEnd_1757649 : Nat := 4983230072969 + 3 ^ 40 * 1757649 * 2
def baseEnd_1757649 : Nat := 300839586298166307968075

theorem tailTrace_1757649 : CollatzResearch.WordTrace tailWord_1757649 prefixEnd_1757649 300839586298166307968075 := by
  unfold tailWord_1757649
  simp only [CollatzResearch.WordTrace]
  refine ⟨64106725609345330395556001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42737817072896886930370667 64106725609345330395556001)
  ·
    refine ⟨48080044207008997796667001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64106725609345330395556001 48080044207008997796667001)
    ·
      refine ⟨36060033155256748347500251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48080044207008997796667001 36060033155256748347500251)
      ·
        refine ⟨54090049732885122521250377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36060033155256748347500251 54090049732885122521250377)
        ·
          refine ⟨40567537299663841890937783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54090049732885122521250377 40567537299663841890937783)
          ·
            refine ⟨60851305949495762836406675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40567537299663841890937783 60851305949495762836406675)
            ·
              refine ⟨91276958924243644254610013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60851305949495762836406675 91276958924243644254610013)
              ·
                refine ⟨34228859596591366595478755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91276958924243644254610013 34228859596591366595478755)
                ·
                  refine ⟨51343289394887049893218133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34228859596591366595478755 51343289394887049893218133)
                  ·
                    refine ⟨300839586298166307968075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 51343289394887049893218133 300839586298166307968075)
                    ·
                      rfl

theorem cell23_1757649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_1757649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757649 prefixEnd_1757649 := by exact prefixLift 1757649
  have htrace : WordTrace (prefixWord ++ tailWord_1757649) baseStart_1757649 baseEnd_1757649 := by
    simpa [prefixWord, tailWord_1757649, baseEnd_1757649] using wordTrace_append hprefix tailTrace_1757649
  have hstable : (prefixWord ++ tailWord_1757649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757649).length < 2 ^ (prefixWord ++ tailWord_1757649).sum := by decide
  have hdescent : baseEnd_1757649 < baseStart_1757649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757650 : List Nat := [3, 2, 2, 4, 1, 1, 1, 2, 1, 1, 5]
def baseStart_1757650 : Nat := 118140960795 + 1757650 * 2 ^ 59
def prefixEnd_1757650 : Nat := 4983230072969 + 3 ^ 40 * 1757650 * 2
def baseEnd_1757650 : Nat := 902519272375153419991721

theorem tailTrace_1757650 : CollatzResearch.WordTrace tailWord_1757650 prefixEnd_1757650 902519272375153419991721 := by
  unfold tailWord_1757650
  simp only [CollatzResearch.WordTrace]
  refine ⟨16026690520585426891585601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42737841388227805044228269 16026690520585426891585601)
  ·
    refine ⟨12020017890439070168689201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16026690520585426891585601 12020017890439070168689201)
    ·
      refine ⟨9015013417829302626516901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12020017890439070168689201 9015013417829302626516901)
      ·
        refine ⟨1690315015842994242471919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9015013417829302626516901 1690315015842994242471919)
        ·
          refine ⟨2535472523764491363707879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1690315015842994242471919 2535472523764491363707879)
          ·
            refine ⟨3803208785646737045561819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2535472523764491363707879 3803208785646737045561819)
            ·
              refine ⟨5704813178470105568342729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3803208785646737045561819 5704813178470105568342729)
              ·
                refine ⟨4278609883852579176257047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5704813178470105568342729 4278609883852579176257047)
                ·
                  refine ⟨6417914825778868764385571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4278609883852579176257047 6417914825778868764385571)
                  ·
                    refine ⟨9626872238668303146578357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6417914825778868764385571 9626872238668303146578357)
                    ·
                      refine ⟨902519272375153419991721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9626872238668303146578357 902519272375153419991721)
                      ·
                        rfl

theorem cell23_1757650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_1757650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757650 prefixEnd_1757650 := by exact prefixLift 1757650
  have htrace : WordTrace (prefixWord ++ tailWord_1757650) baseStart_1757650 baseEnd_1757650 := by
    simpa [prefixWord, tailWord_1757650, baseEnd_1757650] using wordTrace_append hprefix tailTrace_1757650
  have hstable : (prefixWord ++ tailWord_1757650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757650).length < 2 ^ (prefixWord ++ tailWord_1757650).sum := by decide
  have hdescent : baseEnd_1757650 < baseStart_1757650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757663 : List Nat := [1, 1, 2, 3, 3, 2, 3, 1, 1, 3, 3]
def baseStart_1757663 : Nat := 118140960795 + 1757663 * 2 ^ 59
def prefixEnd_1757663 : Nat := 4983230072969 + 3 ^ 40 * 1757663 * 2
def baseEnd_1757663 : Nat := 902525947623661869129161

theorem tailTrace_1757663 : CollatzResearch.WordTrace tailWord_1757663 prefixEnd_1757663 902525947623661869129161 := by
  unfold tailWord_1757663
  simp only [CollatzResearch.WordTrace]
  refine ⟨64107236231294610786565643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42738157487529740524377095 64107236231294610786565643)
  ·
    refine ⟨96160854346941916179848465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64107236231294610786565643 96160854346941916179848465)
    ·
      refine ⟨72120640760206437134886349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96160854346941916179848465 72120640760206437134886349)
      ·
        refine ⟨27045240285077413925582381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72120640760206437134886349 27045240285077413925582381)
        ·
          refine ⟨10141965106904030222093393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27045240285077413925582381 10141965106904030222093393)
          ·
            refine ⟨7606473830178022666570045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10141965106904030222093393 7606473830178022666570045)
            ·
              refine ⟨2852427686316758499963767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7606473830178022666570045 2852427686316758499963767)
              ·
                refine ⟨4278641529475137749945651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2852427686316758499963767 4278641529475137749945651)
                ·
                  refine ⟨6417962294212706624918477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4278641529475137749945651 6417962294212706624918477)
                  ·
                    refine ⟨2406735860329764984344429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6417962294212706624918477 2406735860329764984344429)
                    ·
                      refine ⟨902525947623661869129161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2406735860329764984344429 902525947623661869129161)
                      ·
                        rfl

theorem cell23_1757663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_1757663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757663 prefixEnd_1757663 := by exact prefixLift 1757663
  have htrace : WordTrace (prefixWord ++ tailWord_1757663) baseStart_1757663 baseEnd_1757663 := by
    simpa [prefixWord, tailWord_1757663, baseEnd_1757663] using wordTrace_append hprefix tailTrace_1757663
  have hstable : (prefixWord ++ tailWord_1757663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757663).length < 2 ^ (prefixWord ++ tailWord_1757663).sum := by decide
  have hdescent : baseEnd_1757663 < baseStart_1757663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757698 : List Nat := [3, 4, 1, 2, 2, 1, 3, 2, 1, 2, 2]
def baseStart_1757698 : Nat := 118140960795 + 1757698 * 2 ^ 59
def prefixEnd_1757698 : Nat := 4983230072969 + 3 ^ 40 * 1757698 * 2
def baseEnd_1757698 : Nat := 902543919446569232191501

theorem tailTrace_1757698 : CollatzResearch.WordTrace tailWord_1757698 prefixEnd_1757698 902543919446569232191501 := by
  unfold tailWord_1757698
  simp only [CollatzResearch.WordTrace]
  refine ⟨16027128196541952941022437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42739008524111874509393165 16027128196541952941022437)
  ·
    refine ⟨3005086536851616176441707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16027128196541952941022437 3005086536851616176441707)
    ·
      refine ⟨4507629805277424264662561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3005086536851616176441707 4507629805277424264662561)
      ·
        refine ⟨3380722353958068198496921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4507629805277424264662561 3380722353958068198496921)
        ·
          refine ⟨2535541765468551148872691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3380722353958068198496921 2535541765468551148872691)
          ·
            refine ⟨3803312648202826723309037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2535541765468551148872691 3803312648202826723309037)
            ·
              refine ⟨1426242243076060021240889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3803312648202826723309037 1426242243076060021240889)
              ·
                refine ⟨1069681682307045015930667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1426242243076060021240889 1069681682307045015930667)
                ·
                  refine ⟨1604522523460567523896001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1069681682307045015930667 1604522523460567523896001)
                  ·
                    refine ⟨1203391892595425642922001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1604522523460567523896001 1203391892595425642922001)
                    ·
                      refine ⟨902543919446569232191501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1203391892595425642922001 902543919446569232191501)
                      ·
                        rfl

theorem cell23_1757698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_1757698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757698 prefixEnd_1757698 := by exact prefixLift 1757698
  have htrace : WordTrace (prefixWord ++ tailWord_1757698) baseStart_1757698 baseEnd_1757698 := by
    simpa [prefixWord, tailWord_1757698, baseEnd_1757698] using wordTrace_append hprefix tailTrace_1757698
  have hstable : (prefixWord ++ tailWord_1757698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757698).length < 2 ^ (prefixWord ++ tailWord_1757698).sum := by decide
  have hdescent : baseEnd_1757698 < baseStart_1757698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757706 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 1, 3, 5]
def baseStart_1757706 : Nat := 118140960795 + 1757706 * 2 ^ 59
def prefixEnd_1757706 : Nat := 4983230072969 + 3 ^ 40 * 1757706 * 2
def baseEnd_1757706 : Nat := 902548027291805200891463

theorem tailTrace_1757706 : CollatzResearch.WordTrace tailWord_1757706 prefixEnd_1757706 902548027291805200891463 := by
  unfold tailWord_1757706
  simp only [CollatzResearch.WordTrace]
  refine ⟨16027201142534707282595243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42739203046759219420253981 16027201142534707282595243)
  ·
    refine ⟨24040801713802060923892865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16027201142534707282595243 24040801713802060923892865)
    ·
      refine ⟨18030601285351545692919649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24040801713802060923892865 18030601285351545692919649)
      ·
        refine ⟨13522950964013659269689737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18030601285351545692919649 13522950964013659269689737)
        ·
          refine ⟨10142213223010244452267303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13522950964013659269689737 10142213223010244452267303)
          ·
            refine ⟨15213319834515366678400955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10142213223010244452267303 15213319834515366678400955)
            ·
              refine ⟨22819979751773050017601433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15213319834515366678400955 22819979751773050017601433)
              ·
                refine ⟨17114984813829787513201075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22819979751773050017601433 17114984813829787513201075)
                ·
                  refine ⟨25672477220744681269801613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17114984813829787513201075 25672477220744681269801613)
                  ·
                    refine ⟨9627178957779255476175605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25672477220744681269801613 9627178957779255476175605)
                    ·
                      refine ⟨902548027291805200891463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9627178957779255476175605 902548027291805200891463)
                      ·
                        rfl

theorem cell23_1757706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_1757706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757706 prefixEnd_1757706 := by exact prefixLift 1757706
  have htrace : WordTrace (prefixWord ++ tailWord_1757706) baseStart_1757706 baseEnd_1757706 := by
    simpa [prefixWord, tailWord_1757706, baseEnd_1757706] using wordTrace_append hprefix tailTrace_1757706
  have hstable : (prefixWord ++ tailWord_1757706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757706).length < 2 ^ (prefixWord ++ tailWord_1757706).sum := by decide
  have hdescent : baseEnd_1757706 < baseStart_1757706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757753 : List Nat := [1, 2, 1, 5, 1, 1, 2, 2, 2, 3, 3]
def baseStart_1757753 : Nat := 118140960795 + 1757753 * 2 ^ 59
def prefixEnd_1757753 : Nat := 4983230072969 + 3 ^ 40 * 1757753 * 2
def baseEnd_1757753 : Nat := 902572160882566517003747

theorem tailTrace_1757753 : CollatzResearch.WordTrace tailWord_1757753 prefixEnd_1757753 902572160882566517003747 := by
  unfold tailWord_1757753
  simp only [CollatzResearch.WordTrace]
  refine ⟨64110518800968556157341913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42740345867312370771561275 64110518800968556157341913)
  ·
    refine ⟨48082889100726417118006435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64110518800968556157341913 48082889100726417118006435)
    ·
      refine ⟨72124333651089625677009653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48082889100726417118006435 72124333651089625677009653)
      ·
        refine ⟨6761656279789652407219655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72124333651089625677009653 6761656279789652407219655)
        ·
          refine ⟨10142484419684478610829483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6761656279789652407219655 10142484419684478610829483)
          ·
            refine ⟨15213726629526717916244225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10142484419684478610829483 15213726629526717916244225)
            ·
              refine ⟨11410294972145038437183169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15213726629526717916244225 11410294972145038437183169)
              ·
                refine ⟨8557721229108778827887377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11410294972145038437183169 8557721229108778827887377)
                ·
                  refine ⟨6418290921831584120915533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8557721229108778827887377 6418290921831584120915533)
                  ·
                    refine ⟨2406859095686844045343325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6418290921831584120915533 2406859095686844045343325)
                    ·
                      refine ⟨902572160882566517003747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2406859095686844045343325 902572160882566517003747)
                      ·
                        rfl

theorem cell23_1757753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_1757753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757753 prefixEnd_1757753 := by exact prefixLift 1757753
  have htrace : WordTrace (prefixWord ++ tailWord_1757753) baseStart_1757753 baseEnd_1757753 := by
    simpa [prefixWord, tailWord_1757753, baseEnd_1757753] using wordTrace_append hprefix tailTrace_1757753
  have hstable : (prefixWord ++ tailWord_1757753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757753).length < 2 ^ (prefixWord ++ tailWord_1757753).sum := by decide
  have hdescent : baseEnd_1757753 < baseStart_1757753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757760 : List Nat := [2, 1, 1, 2, 2, 2, 6, 2, 5]
def baseStart_1757760 : Nat := 118140960795 + 1757760 * 2 ^ 59
def prefixEnd_1757760 : Nat := 4983230072969 + 3 ^ 40 * 1757760 * 2
def baseEnd_1757760 : Nat := 100286195027460887735135

theorem tailTrace_1757760 : CollatzResearch.WordTrace tailWord_1757760 prefixEnd_1757760 100286195027460887735135 := by
  unfold tailWord_1757760
  simp only [CollatzResearch.WordTrace]
  refine ⟨32055387055971598176423367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42740516074628797568564489 32055387055971598176423367)
  ·
    refine ⟨48083080583957397264635051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32055387055971598176423367 48083080583957397264635051)
    ·
      refine ⟨72124620875936095896952577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48083080583957397264635051 72124620875936095896952577)
      ·
        refine ⟨54093465656952071922714433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72124620875936095896952577 54093465656952071922714433)
        ·
          refine ⟨40570099242714053942035825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54093465656952071922714433 40570099242714053942035825)
          ·
            refine ⟨30427574432035540456526869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40570099242714053942035825 30427574432035540456526869)
            ·
              refine ⟨1426292551501665958899697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30427574432035540456526869 1426292551501665958899697)
              ·
                refine ⟨1069719413626249469174773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1426292551501665958899697 1069719413626249469174773)
                ·
                  refine ⟨100286195027460887735135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1069719413626249469174773 100286195027460887735135)
                  ·
                    rfl

theorem cell23_1757760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2, 5].length) (baseStart_1757760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757760 prefixEnd_1757760 := by exact prefixLift 1757760
  have htrace : WordTrace (prefixWord ++ tailWord_1757760) baseStart_1757760 baseEnd_1757760 := by
    simpa [prefixWord, tailWord_1757760, baseEnd_1757760] using wordTrace_append hprefix tailTrace_1757760
  have hstable : (prefixWord ++ tailWord_1757760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757760).length < 2 ^ (prefixWord ++ tailWord_1757760).sum := by decide
  have hdescent : baseEnd_1757760 < baseStart_1757760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757793 : List Nat := [1, 2, 3, 1, 1, 5, 1, 1, 1, 3, 4]
def baseStart_1757793 : Nat := 118140960795 + 1757793 * 2 ^ 59
def prefixEnd_1757793 : Nat := 4983230072969 + 3 ^ 40 * 1757793 * 2
def baseEnd_1757793 : Nat := 902592700108746360503563

theorem tailTrace_1757793 : CollatzResearch.WordTrace tailWord_1757793 prefixEnd_1757793 902592700108746360503563 := by
  unfold tailWord_1757793
  simp only [CollatzResearch.WordTrace]
  refine ⟨64111977720823642988798033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42741318480549095325865355 64111977720823642988798033)
  ·
    refine ⟨48083983290617732241598525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64111977720823642988798033 48083983290617732241598525)
    ·
      refine ⟨18031493733981649590599447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48083983290617732241598525 18031493733981649590599447)
      ·
        refine ⟨27047240600972474385899171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18031493733981649590599447 27047240600972474385899171)
        ·
          refine ⟨40570860901458711578848757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27047240600972474385899171 40570860901458711578848757)
          ·
            refine ⟨3803518209511754210517071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40570860901458711578848757 3803518209511754210517071)
            ·
              refine ⟨5705277314267631315775607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3803518209511754210517071 5705277314267631315775607)
              ·
                refine ⟨8557915971401446973663411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5705277314267631315775607 8557915971401446973663411)
                ·
                  refine ⟨12836873957102170460495117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8557915971401446973663411 12836873957102170460495117)
                  ·
                    refine ⟨4813827733913313922685669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12836873957102170460495117 4813827733913313922685669)
                    ·
                      refine ⟨902592700108746360503563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4813827733913313922685669 902592700108746360503563)
                      ·
                        rfl

theorem cell23_1757793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_1757793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757793 prefixEnd_1757793 := by exact prefixLift 1757793
  have htrace : WordTrace (prefixWord ++ tailWord_1757793) baseStart_1757793 baseEnd_1757793 := by
    simpa [prefixWord, tailWord_1757793, baseEnd_1757793] using wordTrace_append hprefix tailTrace_1757793
  have hstable : (prefixWord ++ tailWord_1757793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757793).length < 2 ^ (prefixWord ++ tailWord_1757793).sum := by decide
  have hdescent : baseEnd_1757793 < baseStart_1757793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757794 : List Nat := [3, 3, 2, 3, 1, 1, 2, 3, 5]
def baseStart_1757794 : Nat := 118140960795 + 1757794 * 2 ^ 59
def prefixEnd_1757794 : Nat := 4983230072969 + 3 ^ 40 * 1757794 * 2
def baseEnd_1757794 : Nat := 100288134843266761843451

theorem tailTrace_1757794 : CollatzResearch.WordTrace tailWord_1757794 prefixEnd_1757794 100288134843266761843451 := by
  unfold tailWord_1757794
  simp only [CollatzResearch.WordTrace]
  refine ⟨16028003548455005039896109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42741342795880013439722957 16028003548455005039896109)
  ·
    refine ⟨6010501330670626889961041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16028003548455005039896109 6010501330670626889961041)
    ·
      refine ⟨4507875998002970167470781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6010501330670626889961041 4507875998002970167470781)
      ·
        refine ⟨1690453499251113812801543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4507875998002970167470781 1690453499251113812801543)
        ·
          refine ⟨2535680248876670719202315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1690453499251113812801543 2535680248876670719202315)
          ·
            refine ⟨3803520373315006078803473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2535680248876670719202315 3803520373315006078803473)
            ·
              refine ⟨2852640279986254559102605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3803520373315006078803473 2852640279986254559102605)
              ·
                refine ⟨1069740104994845459663477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2852640279986254559102605 1069740104994845459663477)
                ·
                  refine ⟨100288134843266761843451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1069740104994845459663477 100288134843266761843451)
                  ·
                    rfl

theorem cell23_1757794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_1757794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757794 prefixEnd_1757794 := by exact prefixLift 1757794
  have htrace : WordTrace (prefixWord ++ tailWord_1757794) baseStart_1757794 baseEnd_1757794 := by
    simpa [prefixWord, tailWord_1757794, baseEnd_1757794] using wordTrace_append hprefix tailTrace_1757794
  have hstable : (prefixWord ++ tailWord_1757794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757794).length < 2 ^ (prefixWord ++ tailWord_1757794).sum := by decide
  have hdescent : baseEnd_1757794 < baseStart_1757794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757816 : List Nat := [2, 1, 2, 1, 1, 1, 2, 5, 8]
def baseStart_1757816 : Nat := 118140960795 + 1757816 * 2 ^ 59
def prefixEnd_1757816 : Nat := 4983230072969 + 3 ^ 40 * 1757816 * 2
def baseEnd_1757816 : Nat := 100289390018199974501773

theorem tailTrace_1757816 : CollatzResearch.WordTrace tailWord_1757816 prefixEnd_1757816 100289390018199974501773 := by
  unfold tailWord_1757816
  simp only [CollatzResearch.WordTrace]
  refine ⟨32056408299870158958442651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42741877733160211944590201 32056408299870158958442651)
  ·
    refine ⟨48084612449805238437663977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32056408299870158958442651 48084612449805238437663977)
    ·
      refine ⟨36063459337353928828247983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48084612449805238437663977 36063459337353928828247983)
      ·
        refine ⟨54095189006030893242371975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36063459337353928828247983 54095189006030893242371975)
        ·
          refine ⟨81142783509046339863557963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54095189006030893242371975 81142783509046339863557963)
          ·
            refine ⟨121714175263569509795336945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81142783509046339863557963 121714175263569509795336945)
            ·
              refine ⟨91285631447677132346502709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121714175263569509795336945 91285631447677132346502709)
              ·
                refine ⟨8558027948219731157484629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91285631447677132346502709 8558027948219731157484629)
                ·
                  refine ⟨100289390018199974501773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8558027948219731157484629 100289390018199974501773)
                  ·
                    rfl

theorem cell23_1757816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 8].length) (baseStart_1757816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757816 prefixEnd_1757816 := by exact prefixLift 1757816
  have htrace : WordTrace (prefixWord ++ tailWord_1757816) baseStart_1757816 baseEnd_1757816 := by
    simpa [prefixWord, tailWord_1757816, baseEnd_1757816] using wordTrace_append hprefix tailTrace_1757816
  have hstable : (prefixWord ++ tailWord_1757816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757816).length < 2 ^ (prefixWord ++ tailWord_1757816).sum := by decide
  have hdescent : baseEnd_1757816 < baseStart_1757816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757923 : List Nat := [1, 1, 1, 7, 1, 12]
def baseStart_1757923 : Nat := 118140960795 + 1757923 * 2 ^ 59
def prefixEnd_1757923 : Nat := 4983230072969 + 3 ^ 40 * 1757923 * 2
def baseEnd_1757923 : Nat := 3714647953061032312255

theorem tailTrace_1757923 : CollatzResearch.WordTrace tailWord_1757923 prefixEnd_1757923 3714647953061032312255 := by
  unfold tailWord_1757923
  simp only [CollatzResearch.WordTrace]
  refine ⟨64116719210352675191030423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42744479473568450127353615 64116719210352675191030423)
  ·
    refine ⟨96175078815529012786545635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64116719210352675191030423 96175078815529012786545635)
    ·
      refine ⟨144262618223293519179818453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96175078815529012786545635 144262618223293519179818453)
      ·
        refine ⟨3381155114608441855776995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 144262618223293519179818453 3381155114608441855776995)
        ·
          refine ⟨5071732671912662783665493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3381155114608441855776995 5071732671912662783665493)
          ·
            refine ⟨3714647953061032312255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 5071732671912662783665493 3714647953061032312255)
            ·
              rfl

theorem cell23_1757923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 12].length) (baseStart_1757923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757923 prefixEnd_1757923 := by exact prefixLift 1757923
  have htrace : WordTrace (prefixWord ++ tailWord_1757923) baseStart_1757923 baseEnd_1757923 := by
    simpa [prefixWord, tailWord_1757923, baseEnd_1757923] using wordTrace_append hprefix tailTrace_1757923
  have hstable : (prefixWord ++ tailWord_1757923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757923).length < 2 ^ (prefixWord ++ tailWord_1757923).sum := by decide
  have hdescent : baseEnd_1757923 < baseStart_1757923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757928 : List Nat := [2, 1, 4, 1, 4, 2, 2, 2, 1, 1, 3]
def baseStart_1757928 : Nat := 118140960795 + 1757928 * 2 ^ 59
def prefixEnd_1757928 : Nat := 4983230072969 + 3 ^ 40 * 1757928 * 2
def baseEnd_1757928 : Nat := 902662019997103332315443

theorem tailTrace_1757928 : CollatzResearch.WordTrace tailWord_1757928 prefixEnd_1757928 902662019997103332315443 := by
  unfold tailWord_1757928
  simp only [CollatzResearch.WordTrace]
  refine ⟨32058450787667280522481219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42744601050223040696641625 32058450787667280522481219)
  ·
    refine ⟨48087676181500920783721829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32058450787667280522481219 48087676181500920783721829)
    ·
      refine ⟨9016439284031422646947843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48087676181500920783721829 9016439284031422646947843)
      ·
        refine ⟨13524658926047133970421765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9016439284031422646947843 13524658926047133970421765)
        ·
          refine ⟨2535873548633837619454081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13524658926047133970421765 2535873548633837619454081)
          ·
            refine ⟨1901905161475378214590561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2535873548633837619454081 1901905161475378214590561)
            ·
              refine ⟨1426428871106533660942921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1901905161475378214590561 1426428871106533660942921)
              ·
                refine ⟨1069821653329900245707191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1426428871106533660942921 1069821653329900245707191)
                ·
                  refine ⟨1604732479994850368560787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1069821653329900245707191 1604732479994850368560787)
                  ·
                    refine ⟨2407098719992275552841181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1604732479994850368560787 2407098719992275552841181)
                    ·
                      refine ⟨902662019997103332315443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2407098719992275552841181 902662019997103332315443)
                      ·
                        rfl

theorem cell23_1757928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_1757928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757928 prefixEnd_1757928 := by exact prefixLift 1757928
  have htrace : WordTrace (prefixWord ++ tailWord_1757928) baseStart_1757928 baseEnd_1757928 := by
    simpa [prefixWord, tailWord_1757928, baseEnd_1757928] using wordTrace_append hprefix tailTrace_1757928
  have hstable : (prefixWord ++ tailWord_1757928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757928).length < 2 ^ (prefixWord ++ tailWord_1757928).sum := by decide
  have hdescent : baseEnd_1757928 < baseStart_1757928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757953 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 4, 7]
def baseStart_1757953 : Nat := 118140960795 + 1757953 * 2 ^ 59
def prefixEnd_1757953 : Nat := 4983230072969 + 3 ^ 40 * 1757953 * 2
def baseEnd_1757953 : Nat := 300891619004488578167609

theorem tailTrace_1757953 : CollatzResearch.WordTrace tailWord_1757953 prefixEnd_1757953 300891619004488578167609 := by
  unfold tailWord_1757953
  simp only [CollatzResearch.WordTrace]
  refine ⟨64117813400243990314622513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42745208933495993543081675 64117813400243990314622513)
  ·
    refine ⟨48088360050182992735966885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64117813400243990314622513 48088360050182992735966885)
    ·
      refine ⟨9016567509409311137993791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48088360050182992735966885 9016567509409311137993791)
      ·
        refine ⟨13524851264113966706990687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9016567509409311137993791 13524851264113966706990687)
        ·
          refine ⟨20287276896170950060486031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13524851264113966706990687 20287276896170950060486031)
          ·
            refine ⟨30430915344256425090729047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20287276896170950060486031 30430915344256425090729047)
            ·
              refine ⟨45646373016384637636093571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30430915344256425090729047 45646373016384637636093571)
              ·
                refine ⟨68469559524576956454140357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45646373016384637636093571 68469559524576956454140357)
                ·
                  refine ⟨12838042410858179335151317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68469559524576956454140357 12838042410858179335151317)
                  ·
                    refine ⟨300891619004488578167609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12838042410858179335151317 300891619004488578167609)
                    ·
                      rfl

theorem cell23_1757953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_1757953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757953 prefixEnd_1757953 := by exact prefixLift 1757953
  have htrace : WordTrace (prefixWord ++ tailWord_1757953) baseStart_1757953 baseEnd_1757953 := by
    simpa [prefixWord, tailWord_1757953, baseEnd_1757953] using wordTrace_append hprefix tailTrace_1757953
  have hstable : (prefixWord ++ tailWord_1757953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757953).length < 2 ^ (prefixWord ++ tailWord_1757953).sum := by decide
  have hdescent : baseEnd_1757953 < baseStart_1757953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757963 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 5]
def baseStart_1757963 : Nat := 118140960795 + 1757963 * 2 ^ 59
def prefixEnd_1757963 : Nat := 4983230072969 + 3 ^ 40 * 1757963 * 2
def baseEnd_1757963 : Nat := 902679991820010695377781

theorem tailTrace_1757963 : CollatzResearch.WordTrace tailWord_1757963 prefixEnd_1757963 902679991820010695377781 := by
  unfold tailWord_1757963
  simp only [CollatzResearch.WordTrace]
  refine ⟨64118178130207762022486543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42745452086805174681657695 64118178130207762022486543)
  ·
    refine ⟨96177267195311643033729815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64118178130207762022486543 96177267195311643033729815)
    ·
      refine ⟨144265900792967464550594723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96177267195311643033729815 144265900792967464550594723)
      ·
        refine ⟨216398851189451196825892085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144265900792967464550594723 216398851189451196825892085)
        ·
          refine ⟨20287392299011049702427383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 216398851189451196825892085 20287392299011049702427383)
          ·
            refine ⟨30431088448516574553641075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20287392299011049702427383 30431088448516574553641075)
            ·
              refine ⟨45646632672774861830461613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30431088448516574553641075 45646632672774861830461613)
              ·
                refine ⟨17117487252290573186423105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45646632672774861830461613 17117487252290573186423105)
                ·
                  refine ⟨12838115439217929889817329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17117487252290573186423105 12838115439217929889817329)
                  ·
                    refine ⟨9628586579413447417362997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12838115439217929889817329 9628586579413447417362997)
                    ·
                      refine ⟨902679991820010695377781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9628586579413447417362997 902679991820010695377781)
                      ·
                        rfl

theorem cell23_1757963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 5].length) (baseStart_1757963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757963 prefixEnd_1757963 := by exact prefixLift 1757963
  have htrace : WordTrace (prefixWord ++ tailWord_1757963) baseStart_1757963 baseEnd_1757963 := by
    simpa [prefixWord, tailWord_1757963, baseEnd_1757963] using wordTrace_append hprefix tailTrace_1757963
  have hstable : (prefixWord ++ tailWord_1757963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757963).length < 2 ^ (prefixWord ++ tailWord_1757963).sum := by decide
  have hdescent : baseEnd_1757963 < baseStart_1757963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757984 : List Nat := [2, 1, 1, 5, 1, 2, 3, 2, 2, 1, 3]
def baseStart_1757984 : Nat := 118140960795 + 1757984 * 2 ^ 59
def prefixEnd_1757984 : Nat := 4983230072969 + 3 ^ 40 * 1757984 * 2
def baseEnd_1757984 : Nat := 902690774913755113215185

theorem tailTrace_1757984 : CollatzResearch.WordTrace tailWord_1757984 prefixEnd_1757984 902690774913755113215185 := by
  unfold tailWord_1757984
  simp only [CollatzResearch.WordTrace]
  refine ⟨32059472031565841304500503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42745962708754455072667337 32059472031565841304500503)
  ·
    refine ⟨48089208047348761956750755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32059472031565841304500503 48089208047348761956750755)
    ·
      refine ⟨72133812071023142935126133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48089208047348761956750755 72133812071023142935126133)
      ·
        refine ⟨6762544881658419650168075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72133812071023142935126133 6762544881658419650168075)
        ·
          refine ⟨10143817322487629475252113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6762544881658419650168075 10143817322487629475252113)
          ·
            refine ⟨7607862991865722106439085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10143817322487629475252113 7607862991865722106439085)
            ·
              refine ⟨2852948621949645789914657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7607862991865722106439085 2852948621949645789914657)
              ·
                refine ⟨2139711466462234342435993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2852948621949645789914657 2139711466462234342435993)
                ·
                  refine ⟨1604783599846675756826995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2139711466462234342435993 1604783599846675756826995)
                  ·
                    refine ⟨2407175399770013635240493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1604783599846675756826995 2407175399770013635240493)
                    ·
                      refine ⟨902690774913755113215185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2407175399770013635240493 902690774913755113215185)
                      ·
                        rfl

theorem cell23_1757984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_1757984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757984 prefixEnd_1757984 := by exact prefixLift 1757984
  have htrace : WordTrace (prefixWord ++ tailWord_1757984) baseStart_1757984 baseEnd_1757984 := by
    simpa [prefixWord, tailWord_1757984, baseEnd_1757984] using wordTrace_append hprefix tailTrace_1757984
  have hstable : (prefixWord ++ tailWord_1757984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757984).length < 2 ^ (prefixWord ++ tailWord_1757984).sum := by decide
  have hdescent : baseEnd_1757984 < baseStart_1757984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757993 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 1, 3, 5]
def baseStart_1757993 : Nat := 118140960795 + 1757993 * 2 ^ 59
def prefixEnd_1757993 : Nat := 4983230072969 + 3 ^ 40 * 1757993 * 2
def baseEnd_1757993 : Nat := 902695396239645578002643

theorem tailTrace_1757993 : CollatzResearch.WordTrace tailWord_1757993 prefixEnd_1757993 902695396239645578002643 := by
  unfold tailWord_1757993
  simp only [CollatzResearch.WordTrace]
  refine ⟨64119272320099077146078633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42746181546732718097385755 64119272320099077146078633)
  ·
    refine ⟨48089454240074307859558975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64119272320099077146078633 48089454240074307859558975)
    ·
      refine ⟨72134181360111461789338463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48089454240074307859558975 72134181360111461789338463)
      ·
        refine ⟨108201272040167192684007695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72134181360111461789338463 108201272040167192684007695)
        ·
          refine ⟨162301908060250789026011543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108201272040167192684007695 162301908060250789026011543)
          ·
            refine ⟨243452862090376183539017315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162301908060250789026011543 243452862090376183539017315)
            ·
              refine ⟨365179293135564275308525973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243452862090376183539017315 365179293135564275308525973)
              ·
                refine ⟨17117779365729575405087155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 365179293135564275308525973 17117779365729575405087155)
                ·
                  refine ⟨25676669048594363107630733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17117779365729575405087155 25676669048594363107630733)
                  ·
                    refine ⟨9628750893222886165361525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25676669048594363107630733 9628750893222886165361525)
                    ·
                      refine ⟨902695396239645578002643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9628750893222886165361525 902695396239645578002643)
                      ·
                        rfl

theorem cell23_1757993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 3, 5].length) (baseStart_1757993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1757993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1757993 prefixEnd_1757993 := by exact prefixLift 1757993
  have htrace : WordTrace (prefixWord ++ tailWord_1757993) baseStart_1757993 baseEnd_1757993 := by
    simpa [prefixWord, tailWord_1757993, baseEnd_1757993] using wordTrace_append hprefix tailTrace_1757993
  have hstable : (prefixWord ++ tailWord_1757993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757993).length < 2 ^ (prefixWord ++ tailWord_1757993).sum := by decide
  have hdescent : baseEnd_1757993 < baseStart_1757993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758040 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 4, 3, 3]
def baseStart_1758040 : Nat := 118140960795 + 1758040 * 2 ^ 59
def prefixEnd_1758040 : Nat := 4983230072969 + 3 ^ 40 * 1758040 * 2
def baseEnd_1758040 : Nat := 902719529830406894114927

theorem tailTrace_1758040 : CollatzResearch.WordTrace tailWord_1758040 prefixEnd_1758040 902719529830406894114927 := by
  unfold tailWord_1758040
  simp only [CollatzResearch.WordTrace]
  refine ⟨32060493275464402086519787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42747324367285869448693049 32060493275464402086519787)
  ·
    refine ⟨48090739913196603129779681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32060493275464402086519787 48090739913196603129779681)
    ·
      refine ⟨36068054934897452347334761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48090739913196603129779681 36068054934897452347334761)
      ·
        refine ⟨27051041201173089260501071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36068054934897452347334761 27051041201173089260501071)
        ·
          refine ⟨40576561801759633890751607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27051041201173089260501071 40576561801759633890751607)
          ·
            refine ⟨60864842702639450836127411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40576561801759633890751607 60864842702639450836127411)
            ·
              refine ⟨91297264053959176254191117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60864842702639450836127411 91297264053959176254191117)
              ·
                refine ⟨34236474020234691095321669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91297264053959176254191117 34236474020234691095321669)
                ·
                  refine ⟨6419338878794004580372813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34236474020234691095321669 6419338878794004580372813)
                  ·
                    refine ⟨2407252079547751717639805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6419338878794004580372813 2407252079547751717639805)
                    ·
                      refine ⟨902719529830406894114927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2407252079547751717639805 902719529830406894114927)
                      ·
                        rfl

theorem cell23_1758040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_1758040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758040 prefixEnd_1758040 := by exact prefixLift 1758040
  have htrace : WordTrace (prefixWord ++ tailWord_1758040) baseStart_1758040 baseEnd_1758040 := by
    simpa [prefixWord, tailWord_1758040, baseEnd_1758040] using wordTrace_append hprefix tailTrace_1758040
  have hstable : (prefixWord ++ tailWord_1758040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758040).length < 2 ^ (prefixWord ++ tailWord_1758040).sum := by decide
  have hdescent : baseEnd_1758040 < baseStart_1758040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758060 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 4, 5]
def baseStart_1758060 : Nat := 118140960795 + 1758060 * 2 ^ 59
def prefixEnd_1758060 : Nat := 4983230072969 + 3 ^ 40 * 1758060 * 2
def baseEnd_1758060 : Nat := 300909933147832271954945

theorem tailTrace_1758060 : CollatzResearch.WordTrace tailWord_1758060 prefixEnd_1758060 300909933147832271954945 := by
  unfold tailWord_1758060
  simp only [CollatzResearch.WordTrace]
  refine ⟨32060858005428173794383817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42747810673904231725845089 32060858005428173794383817)
  ·
    refine ⟨24045643504071130345787863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32060858005428173794383817 24045643504071130345787863)
    ·
      refine ⟨36068465256106695518681795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24045643504071130345787863 36068465256106695518681795)
      ·
        refine ⟨54102697884160043278022693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36068465256106695518681795 54102697884160043278022693)
        ·
          refine ⟨10144255853280008114629255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54102697884160043278022693 10144255853280008114629255)
          ·
            refine ⟨15216383779920012171943883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10144255853280008114629255 15216383779920012171943883)
            ·
              refine ⟨22824575669880018257915825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15216383779920012171943883 22824575669880018257915825)
              ·
                refine ⟨17118431752410013693436869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22824575669880018257915825 17118431752410013693436869)
                ·
                  refine ⟨3209705953576877567519413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17118431752410013693436869 3209705953576877567519413)
                  ·
                    refine ⟨300909933147832271954945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3209705953576877567519413 300909933147832271954945)
                    ·
                      rfl

theorem cell23_1758060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 5].length) (baseStart_1758060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758060 prefixEnd_1758060 := by exact prefixLift 1758060
  have htrace : WordTrace (prefixWord ++ tailWord_1758060) baseStart_1758060 baseEnd_1758060 := by
    simpa [prefixWord, tailWord_1758060, baseEnd_1758060] using wordTrace_append hprefix tailTrace_1758060
  have hstable : (prefixWord ++ tailWord_1758060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758060).length < 2 ^ (prefixWord ++ tailWord_1758060).sum := by decide
  have hdescent : baseEnd_1758060 < baseStart_1758060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758097 : List Nat := [1, 2, 2, 1, 1, 1, 3, 4, 2, 4, 2]
def baseStart_1758097 : Nat := 118140960795 + 1758097 * 2 ^ 59
def prefixEnd_1758097 : Nat := 4983230072969 + 3 ^ 40 * 1758097 * 2
def baseEnd_1758097 : Nat := 902748798227713171102165

theorem tailTrace_1758097 : CollatzResearch.WordTrace tailWord_1758097 prefixEnd_1758097 902748798227713171102165 := by
  unfold tailWord_1758097
  simp only [CollatzResearch.WordTrace]
  refine ⟨64123065511722302907864545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42748710341148201938576363 64123065511722302907864545)
  ·
    refine ⟨48092299133791727180898409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64123065511722302907864545 48092299133791727180898409)
    ·
      refine ⟨36069224350343795385673807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48092299133791727180898409 36069224350343795385673807)
      ·
        refine ⟨54103836525515693078510711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36069224350343795385673807 54103836525515693078510711)
        ·
          refine ⟨81155754788273539617766067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54103836525515693078510711 81155754788273539617766067)
          ·
            refine ⟨121733632182410309426649101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81155754788273539617766067 121733632182410309426649101)
            ·
              refine ⟨45650112068403866034993413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121733632182410309426649101 45650112068403866034993413)
              ·
                refine ⟨8559396012825724881561265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45650112068403866034993413 8559396012825724881561265)
                ·
                  refine ⟨6419547009619293661170949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8559396012825724881561265 6419547009619293661170949)
                  ·
                    refine ⟨1203665064303617561469553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6419547009619293661170949 1203665064303617561469553)
                    ·
                      refine ⟨902748798227713171102165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1203665064303617561469553 902748798227713171102165)
                      ·
                        rfl

theorem cell23_1758097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 4, 2].length) (baseStart_1758097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758097 prefixEnd_1758097 := by exact prefixLift 1758097
  have htrace : WordTrace (prefixWord ++ tailWord_1758097) baseStart_1758097 baseEnd_1758097 := by
    simpa [prefixWord, tailWord_1758097, baseEnd_1758097] using wordTrace_append hprefix tailTrace_1758097
  have hstable : (prefixWord ++ tailWord_1758097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758097).length < 2 ^ (prefixWord ++ tailWord_1758097).sum := by decide
  have hdescent : baseEnd_1758097 < baseStart_1758097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758098 : List Nat := [3, 2, 3, 2, 2, 2, 2, 2, 5]
def baseStart_1758098 : Nat := 118140960795 + 1758098 * 2 ^ 59
def prefixEnd_1758098 : Nat := 4983230072969 + 3 ^ 40 * 1758098 * 2
def baseEnd_1758098 : Nat := 100305479078707518576629

theorem tailTrace_1758098 : CollatzResearch.WordTrace tailWord_1758098 prefixEnd_1758098 100305479078707518576629 := by
  unfold tailWord_1758098
  simp only [CollatzResearch.WordTrace]
  refine ⟨16030775496179670019662737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42748734656479120052433965 16030775496179670019662737)
  ·
    refine ⟨12023081622134752514747053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16030775496179670019662737 12023081622134752514747053)
    ·
      refine ⟨4508655608300532193030145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12023081622134752514747053 4508655608300532193030145)
      ·
        refine ⟨3381491706225399144772609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4508655608300532193030145 3381491706225399144772609)
        ·
          refine ⟨2536118779669049358579457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3381491706225399144772609 2536118779669049358579457)
          ·
            refine ⟨1902089084751787018934593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2536118779669049358579457 1902089084751787018934593)
            ·
              refine ⟨1426566813563840264200945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1902089084751787018934593 1426566813563840264200945)
              ·
                refine ⟨1069925110172880198150709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1426566813563840264200945 1069925110172880198150709)
                ·
                  refine ⟨100305479078707518576629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1069925110172880198150709 100305479078707518576629)
                  ·
                    rfl

theorem cell23_1758098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2, 5].length) (baseStart_1758098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758098 prefixEnd_1758098 := by exact prefixLift 1758098
  have htrace : WordTrace (prefixWord ++ tailWord_1758098) baseStart_1758098 baseEnd_1758098 := by
    simpa [prefixWord, tailWord_1758098, baseEnd_1758098] using wordTrace_append hprefix tailTrace_1758098
  have hstable : (prefixWord ++ tailWord_1758098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758098).length < 2 ^ (prefixWord ++ tailWord_1758098).sum := by decide
  have hdescent : baseEnd_1758098 < baseStart_1758098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758114 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 1, 6, 2]
def baseStart_1758114 : Nat := 118140960795 + 1758114 * 2 ^ 59
def prefixEnd_1758114 : Nat := 4983230072969 + 3 ^ 40 * 1758114 * 2
def baseEnd_1758114 : Nat := 902757527398839604589587

theorem tailTrace_1758114 : CollatzResearch.WordTrace tailWord_1758114 prefixEnd_1758114 902757527398839604589587 := by
  unfold tailWord_1758114
  simp only [CollatzResearch.WordTrace]
  refine ⟨16030921388165178702808349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42749123701773809874155597 16030921388165178702808349)
  ·
    refine ⟨6011595520561942013553131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16030921388165178702808349 6011595520561942013553131)
    ·
      refine ⟨9017393280842913020329697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6011595520561942013553131 9017393280842913020329697)
      ·
        refine ⟨6763044960632184765247273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9017393280842913020329697 6763044960632184765247273)
        ·
          refine ⟨5072283720474138573935455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6763044960632184765247273 5072283720474138573935455)
          ·
            refine ⟨7608425580711207860903183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5072283720474138573935455 7608425580711207860903183)
            ·
              refine ⟨11412638371066811791354775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7608425580711207860903183 11412638371066811791354775)
              ·
                refine ⟨17118957556600217687032163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11412638371066811791354775 17118957556600217687032163)
                ·
                  refine ⟨25678436334900326530548245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17118957556600217687032163 25678436334900326530548245)
                  ·
                    refine ⟨1203676703198452806119449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25678436334900326530548245 1203676703198452806119449)
                    ·
                      refine ⟨902757527398839604589587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1203676703198452806119449 902757527398839604589587)
                      ·
                        rfl

theorem cell23_1758114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_1758114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758114 prefixEnd_1758114 := by exact prefixLift 1758114
  have htrace : WordTrace (prefixWord ++ tailWord_1758114) baseStart_1758114 baseEnd_1758114 := by
    simpa [prefixWord, tailWord_1758114, baseEnd_1758114] using wordTrace_append hprefix tailTrace_1758114
  have hstable : (prefixWord ++ tailWord_1758114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758114).length < 2 ^ (prefixWord ++ tailWord_1758114).sum := by decide
  have hdescent : baseEnd_1758114 < baseStart_1758114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758204 : List Nat := [2, 2, 2, 1, 2, 3, 2, 3, 1, 1, 4]
def baseStart_1758204 : Nat := 118140960795 + 1758204 * 2 ^ 59
def prefixEnd_1758204 : Nat := 4983230072969 + 3 ^ 40 * 1758204 * 2
def baseEnd_1758204 : Nat := 902803740657744252464173

theorem tailTrace_1758204 : CollatzResearch.WordTrace tailWord_1758204 prefixEnd_1758204 902803740657744252464173 := by
  unfold tailWord_1758204
  simp only [CollatzResearch.WordTrace]
  refine ⟨32063484061167330091004833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42751312081556440121339777 32063484061167330091004833)
  ·
    refine ⟨24047613045875497568253625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32063484061167330091004833 24047613045875497568253625)
    ·
      refine ⟨18035709784406623176190219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24047613045875497568253625 18035709784406623176190219)
      ·
        refine ⟨27053564676609934764285329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18035709784406623176190219 27053564676609934764285329)
        ·
          refine ⟨20290173507457451073213997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27053564676609934764285329 20290173507457451073213997)
          ·
            refine ⟨7608815065296544152455249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20290173507457451073213997 7608815065296544152455249)
            ·
              refine ⟨5706611298972408114341437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7608815065296544152455249 5706611298972408114341437)
              ·
                refine ⟨2139979237114653042878039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5706611298972408114341437 2139979237114653042878039)
                ·
                  refine ⟨3209968855671979564317059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2139979237114653042878039 3209968855671979564317059)
                  ·
                    refine ⟨4814953283507969346475589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3209968855671979564317059 4814953283507969346475589)
                    ·
                      refine ⟨902803740657744252464173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4814953283507969346475589 902803740657744252464173)
                      ·
                        rfl

theorem cell23_1758204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_1758204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758204 prefixEnd_1758204 := by exact prefixLift 1758204
  have htrace : WordTrace (prefixWord ++ tailWord_1758204) baseStart_1758204 baseEnd_1758204 := by
    simpa [prefixWord, tailWord_1758204, baseEnd_1758204] using wordTrace_append hprefix tailTrace_1758204
  have hstable : (prefixWord ++ tailWord_1758204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758204).length < 2 ^ (prefixWord ++ tailWord_1758204).sum := by decide
  have hdescent : baseEnd_1758204 < baseStart_1758204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758207 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 7, 2, 3]
def baseStart_1758207 : Nat := 118140960795 + 1758207 * 2 ^ 59
def prefixEnd_1758207 : Nat := 4983230072969 + 3 ^ 40 * 1758207 * 2
def baseEnd_1758207 : Nat := 902805281099707740726659

theorem tailTrace_1758207 : CollatzResearch.WordTrace tailWord_1758207 prefixEnd_1758207 902805281099707740726659 := by
  unfold tailWord_1758207
  simp only [CollatzResearch.WordTrace]
  refine ⟨64127077541323791694368875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42751385027549194462912583 64127077541323791694368875)
  ·
    refine ⟨96190616311985687541553313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64127077541323791694368875 96190616311985687541553313)
    ·
      refine ⟨72142962233989265656164985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96190616311985687541553313 72142962233989265656164985)
      ·
        refine ⟨54107221675491949242123739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72142962233989265656164985 54107221675491949242123739)
        ·
          refine ⟨81160832513237923863185609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54107221675491949242123739 81160832513237923863185609)
          ·
            refine ⟨60870624384928442897389207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81160832513237923863185609 60870624384928442897389207)
            ·
              refine ⟨91305936577392664346083811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60870624384928442897389207 91305936577392664346083811)
              ·
                refine ⟨136958904866088996519125717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91305936577392664346083811 136958904866088996519125717)
                ·
                  refine ⟨3209974332798960855917009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 136958904866088996519125717 3209974332798960855917009)
                  ·
                    refine ⟨2407480749599220641937757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3209974332798960855917009 2407480749599220641937757)
                    ·
                      refine ⟨902805281099707740726659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2407480749599220641937757 902805281099707740726659)
                      ·
                        rfl

theorem cell23_1758207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2, 3].length) (baseStart_1758207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758207 prefixEnd_1758207 := by exact prefixLift 1758207
  have htrace : WordTrace (prefixWord ++ tailWord_1758207) baseStart_1758207 baseEnd_1758207 := by
    simpa [prefixWord, tailWord_1758207, baseEnd_1758207] using wordTrace_append hprefix tailTrace_1758207
  have hstable : (prefixWord ++ tailWord_1758207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758207).length < 2 ^ (prefixWord ++ tailWord_1758207).sum := by decide
  have hdescent : baseEnd_1758207 < baseStart_1758207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758231 : List Nat := [1, 1, 3, 5, 1, 2, 1, 3, 2, 4]
def baseStart_1758231 : Nat := 118140960795 + 1758231 * 2 ^ 59
def prefixEnd_1758231 : Nat := 4983230072969 + 3 ^ 40 * 1758231 * 2
def baseEnd_1758231 : Nat := 300939201545138548942183

theorem tailTrace_1758231 : CollatzResearch.WordTrace tailWord_1758231 prefixEnd_1758231 300939201545138548942183 := by
  unfold tailWord_1758231
  simp only [CollatzResearch.WordTrace]
  refine ⟨64127952893236843793242547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42751968595491229195495031 64127952893236843793242547)
  ·
    refine ⟨96191929339855265689863821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64127952893236843793242547 96191929339855265689863821)
    ·
      refine ⟨36071973502445724633698933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96191929339855265689863821 36071973502445724633698933)
      ·
        refine ⟨3381747515854286684409275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36071973502445724633698933 3381747515854286684409275)
        ·
          refine ⟨5072621273781430026613913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3381747515854286684409275 5072621273781430026613913)
          ·
            refine ⟨3804465955336072519960435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5072621273781430026613913 3804465955336072519960435)
            ·
              refine ⟨5706698933004108779940653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3804465955336072519960435 5706698933004108779940653)
              ·
                refine ⟨2140012099876540792477745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5706698933004108779940653 2140012099876540792477745)
                ·
                  refine ⟨1605009074907405594358309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2140012099876540792477745 1605009074907405594358309)
                  ·
                    refine ⟨300939201545138548942183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1605009074907405594358309 300939201545138548942183)
                    ·
                      rfl

theorem cell23_1758231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2, 4].length) (baseStart_1758231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758231 prefixEnd_1758231 := by exact prefixLift 1758231
  have htrace : WordTrace (prefixWord ++ tailWord_1758231) baseStart_1758231 baseEnd_1758231 := by
    simpa [prefixWord, tailWord_1758231, baseEnd_1758231] using wordTrace_append hprefix tailTrace_1758231
  have hstable : (prefixWord ++ tailWord_1758231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758231).length < 2 ^ (prefixWord ++ tailWord_1758231).sum := by decide
  have hdescent : baseEnd_1758231 < baseStart_1758231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758241 : List Nat := [1, 2, 3, 2, 3, 1, 3, 2, 1, 2, 3]
def baseStart_1758241 : Nat := 118140960795 + 1758241 * 2 ^ 59
def prefixEnd_1758241 : Nat := 4983230072969 + 3 ^ 40 * 1758241 * 2
def baseEnd_1758241 : Nat := 902822739441960607701503

theorem tailTrace_1758241 : CollatzResearch.WordTrace tailWord_1758241 prefixEnd_1758241 902822739441960607701503 := by
  unfold tailWord_1758241
  simp only [CollatzResearch.WordTrace]
  refine ⟨64128317623200615501106577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42752211748800410334071051 64128317623200615501106577)
  ·
    refine ⟨48096238217400461625829933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64128317623200615501106577 48096238217400461625829933)
    ·
      refine ⟨18036089331525173109686225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48096238217400461625829933 18036089331525173109686225)
      ·
        refine ⟨13527066998643879832264669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18036089331525173109686225 13527066998643879832264669)
        ·
          refine ⟨5072650124491454937099251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13527066998643879832264669 5072650124491454937099251)
          ·
            refine ⟨7608975186737182405648877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5072650124491454937099251 7608975186737182405648877)
            ·
              refine ⟨2853365695026443402118329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7608975186737182405648877 2853365695026443402118329)
              ·
                refine ⟨2140024271269832551588747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2853365695026443402118329 2140024271269832551588747)
                ·
                  refine ⟨3210036406904748827383121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2140024271269832551588747 3210036406904748827383121)
                  ·
                    refine ⟨2407527305178561620537341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3210036406904748827383121 2407527305178561620537341)
                    ·
                      refine ⟨902822739441960607701503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2407527305178561620537341 902822739441960607701503)
                      ·
                        rfl

theorem cell23_1758241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_1758241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758241 prefixEnd_1758241 := by exact prefixLift 1758241
  have htrace : WordTrace (prefixWord ++ tailWord_1758241) baseStart_1758241 baseEnd_1758241 := by
    simpa [prefixWord, tailWord_1758241, baseEnd_1758241] using wordTrace_append hprefix tailTrace_1758241
  have hstable : (prefixWord ++ tailWord_1758241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758241).length < 2 ^ (prefixWord ++ tailWord_1758241).sum := by decide
  have hdescent : baseEnd_1758241 < baseStart_1758241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758277 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 2, 3, 4]
def baseStart_1758277 : Nat := 118140960795 + 1758277 * 2 ^ 59
def prefixEnd_1758277 : Nat := 4983230072969 + 3 ^ 40 * 1758277 * 2
def baseEnd_1758277 : Nat := 902841224745522466851337

theorem tailTrace_1758277 : CollatzResearch.WordTrace tailWord_1758277 prefixEnd_1758277 902841224745522466851337 := by
  unfold tailWord_1758277
  simp only [CollatzResearch.WordTrace]
  refine ⟨64129630651070193649417085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42753087100713462432944723 64129630651070193649417085)
  ·
    refine ⟨24048611494151322618531407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64129630651070193649417085 24048611494151322618531407)
    ·
      refine ⟨36072917241226983927797111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24048611494151322618531407 36072917241226983927797111)
      ·
        refine ⟨54109375861840475891695667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36072917241226983927797111 54109375861840475891695667)
        ·
          refine ⟨81164063792760713837543501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54109375861840475891695667 81164063792760713837543501)
          ·
            refine ⟨30436523922285267689078813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81164063792760713837543501 30436523922285267689078813)
            ·
              refine ⟨11413696470856975383404555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30436523922285267689078813 11413696470856975383404555)
              ·
                refine ⟨17120544706285463075106833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11413696470856975383404555 17120544706285463075106833)
                ·
                  refine ⟨12840408529714097306330125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17120544706285463075106833 12840408529714097306330125)
                  ·
                    refine ⟨4815153198642786489873797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12840408529714097306330125 4815153198642786489873797)
                    ·
                      refine ⟨902841224745522466851337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4815153198642786489873797 902841224745522466851337)
                      ·
                        rfl

theorem cell23_1758277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_1758277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758277 prefixEnd_1758277 := by exact prefixLift 1758277
  have htrace : WordTrace (prefixWord ++ tailWord_1758277) baseStart_1758277 baseEnd_1758277 := by
    simpa [prefixWord, tailWord_1758277, baseEnd_1758277] using wordTrace_append hprefix tailTrace_1758277
  have hstable : (prefixWord ++ tailWord_1758277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758277).length < 2 ^ (prefixWord ++ tailWord_1758277).sum := by decide
  have hdescent : baseEnd_1758277 < baseStart_1758277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758297 : List Nat := [1, 2, 1, 2, 2, 1, 2, 4, 2, 1, 5]
def baseStart_1758297 : Nat := 118140960795 + 1758297 * 2 ^ 59
def prefixEnd_1758297 : Nat := 4983230072969 + 3 ^ 40 * 1758297 * 2
def baseEnd_1758297 : Nat := 902851494358612388601245

theorem tailTrace_1758297 : CollatzResearch.WordTrace tailWord_1758297 prefixEnd_1758297 902851494358612388601245 := by
  unfold tailWord_1758297
  simp only [CollatzResearch.WordTrace]
  refine ⟨64130360110997737065145145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42753573407331824710096763 64130360110997737065145145)
  ·
    refine ⟨48097770083248302798858859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64130360110997737065145145 48097770083248302798858859)
    ·
      refine ⟨72146655124872454198288289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48097770083248302798858859 72146655124872454198288289)
      ·
        refine ⟨54109991343654340648716217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72146655124872454198288289 54109991343654340648716217)
        ·
          refine ⟨40582493507740755486537163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54109991343654340648716217 40582493507740755486537163)
          ·
            refine ⟨60873740261611133229805745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40582493507740755486537163 60873740261611133229805745)
            ·
              refine ⟨45655305196208349922354309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60873740261611133229805745 45655305196208349922354309)
              ·
                refine ⟨8560369724289065610441433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45655305196208349922354309 8560369724289065610441433)
                ·
                  refine ⟨6420277293216799207831075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8560369724289065610441433 6420277293216799207831075)
                  ·
                    refine ⟨9630415939825198811746613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6420277293216799207831075 9630415939825198811746613)
                    ·
                      refine ⟨902851494358612388601245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9630415939825198811746613 902851494358612388601245)
                      ·
                        rfl

theorem cell23_1758297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_1758297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758297 prefixEnd_1758297 := by exact prefixLift 1758297
  have htrace : WordTrace (prefixWord ++ tailWord_1758297) baseStart_1758297 baseEnd_1758297 := by
    simpa [prefixWord, tailWord_1758297, baseEnd_1758297] using wordTrace_append hprefix tailTrace_1758297
  have hstable : (prefixWord ++ tailWord_1758297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758297).length < 2 ^ (prefixWord ++ tailWord_1758297).sum := by decide
  have hdescent : baseEnd_1758297 < baseStart_1758297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758307 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 4]
def baseStart_1758307 : Nat := 118140960795 + 1758307 * 2 ^ 59
def prefixEnd_1758307 : Nat := 4983230072969 + 3 ^ 40 * 1758307 * 2
def baseEnd_1758307 : Nat := 902856629165157349476199

theorem tailTrace_1758307 : CollatzResearch.WordTrace tailWord_1758307 prefixEnd_1758307 902856629165157349476199 := by
  unfold tailWord_1758307
  simp only [CollatzResearch.WordTrace]
  refine ⟨64130724840961508773009175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42753816560641005848672783 64130724840961508773009175)
  ·
    refine ⟨96196087261442263159513763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64130724840961508773009175 96196087261442263159513763)
    ·
      refine ⟨144294130892163394739270645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96196087261442263159513763 144294130892163394739270645)
      ·
        refine ⟨13527574771140318256806623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144294130892163394739270645 13527574771140318256806623)
        ·
          refine ⟨20291362156710477385209935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13527574771140318256806623 20291362156710477385209935)
          ·
            refine ⟨30437043235065716077814903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20291362156710477385209935 30437043235065716077814903)
            ·
              refine ⟨45655564852598574116722355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30437043235065716077814903 45655564852598574116722355)
              ·
                refine ⟨68483347278897861175083533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45655564852598574116722355 68483347278897861175083533)
                ·
                  refine ⟨25681255229586697940656325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68483347278897861175083533 25681255229586697940656325)
                  ·
                    refine ⟨4815235355547505863873061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25681255229586697940656325 4815235355547505863873061)
                    ·
                      refine ⟨902856629165157349476199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4815235355547505863873061 902856629165157349476199)
                      ·
                        rfl

theorem cell23_1758307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_1758307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758307 prefixEnd_1758307 := by exact prefixLift 1758307
  have htrace : WordTrace (prefixWord ++ tailWord_1758307) baseStart_1758307 baseEnd_1758307 := by
    simpa [prefixWord, tailWord_1758307, baseEnd_1758307] using wordTrace_append hprefix tailTrace_1758307
  have hstable : (prefixWord ++ tailWord_1758307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758307).length < 2 ^ (prefixWord ++ tailWord_1758307).sum := by decide
  have hdescent : baseEnd_1758307 < baseStart_1758307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758311 : List Nat := [1, 1, 5, 1, 1, 3, 2, 2, 1, 4, 2]
def baseStart_1758311 : Nat := 118140960795 + 1758311 * 2 ^ 59
def prefixEnd_1758311 : Nat := 4983230072969 + 3 ^ 40 * 1758311 * 2
def baseEnd_1758311 : Nat := 902858683087775333826181

theorem tailTrace_1758311 : CollatzResearch.WordTrace tailWord_1758311 prefixEnd_1758311 902858683087775333826181 := by
  unfold tailWord_1758311
  simp only [CollatzResearch.WordTrace]
  refine ⟨64130870732947017456154787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42753913821964678304103191 64130870732947017456154787)
  ·
    refine ⟨96196306099420526184232181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64130870732947017456154787 96196306099420526184232181)
    ·
      refine ⟨9018403696820674329771767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96196306099420526184232181 9018403696820674329771767)
      ·
        refine ⟨13527605545231011494657651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9018403696820674329771767 13527605545231011494657651)
        ·
          refine ⟨20291408317846517241986477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13527605545231011494657651 20291408317846517241986477)
          ·
            refine ⟨7609278119192443965744929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20291408317846517241986477 7609278119192443965744929)
            ·
              refine ⟨5706958589394332974308697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7609278119192443965744929 5706958589394332974308697)
              ·
                refine ⟨4280218942045749730731523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5706958589394332974308697 4280218942045749730731523)
                ·
                  refine ⟨6420328413068624596097285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4280218942045749730731523 6420328413068624596097285)
                  ·
                    refine ⟨1203811577450367111768241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6420328413068624596097285 1203811577450367111768241)
                    ·
                      refine ⟨902858683087775333826181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1203811577450367111768241 902858683087775333826181)
                      ·
                        rfl

theorem cell23_1758311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_1758311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758311 prefixEnd_1758311 := by exact prefixLift 1758311
  have htrace : WordTrace (prefixWord ++ tailWord_1758311) baseStart_1758311 baseEnd_1758311 := by
    simpa [prefixWord, tailWord_1758311, baseEnd_1758311] using wordTrace_append hprefix tailTrace_1758311
  have hstable : (prefixWord ++ tailWord_1758311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758311).length < 2 ^ (prefixWord ++ tailWord_1758311).sum := by decide
  have hdescent : baseEnd_1758311 < baseStart_1758311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758328 : List Nat := [2, 1, 2, 1, 1, 1, 7, 2, 2, 2, 2]
def baseStart_1758328 : Nat := 118140960795 + 1758328 * 2 ^ 59
def prefixEnd_1758328 : Nat := 4983230072969 + 3 ^ 40 * 1758328 * 2
def baseEnd_1758328 : Nat := 902867412258901767313603

theorem tailTrace_1758328 : CollatzResearch.WordTrace tailWord_1758328 prefixEnd_1758328 902867412258901767313603 := by
  unfold tailWord_1758328
  simp only [CollatzResearch.WordTrace]
  refine ⟨32065745386942714679761819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42754327182590286239682425 32065745386942714679761819)
  ·
    refine ⟨48098618080414072019642729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32065745386942714679761819 48098618080414072019642729)
    ·
      refine ⟨36073963560310554014732047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48098618080414072019642729 36073963560310554014732047)
      ·
        refine ⟨54110945340465831022098071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36073963560310554014732047 54110945340465831022098071)
        ·
          refine ⟨81166418010698746533147107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54110945340465831022098071 81166418010698746533147107)
          ·
            refine ⟨121749627016048119799720661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81166418010698746533147107 121749627016048119799720661)
            ·
              refine ⟨2853506883188627807805953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 121749627016048119799720661 2853506883188627807805953)
              ·
                refine ⟨2140130162391470855854465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2853506883188627807805953 2140130162391470855854465)
                ·
                  refine ⟨1605097621793603141890849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2140130162391470855854465 1605097621793603141890849)
                  ·
                    refine ⟨1203823216345202356418137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1605097621793603141890849 1203823216345202356418137)
                    ·
                      refine ⟨902867412258901767313603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1203823216345202356418137 902867412258901767313603)
                      ·
                        rfl

theorem cell23_1758328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 2, 2, 2].length) (baseStart_1758328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758328 prefixEnd_1758328 := by exact prefixLift 1758328
  have htrace : WordTrace (prefixWord ++ tailWord_1758328) baseStart_1758328 baseEnd_1758328 := by
    simpa [prefixWord, tailWord_1758328, baseEnd_1758328] using wordTrace_append hprefix tailTrace_1758328
  have hstable : (prefixWord ++ tailWord_1758328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758328).length < 2 ^ (prefixWord ++ tailWord_1758328).sum := by decide
  have hdescent : baseEnd_1758328 < baseStart_1758328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758345 : List Nat := [1, 2, 1, 1, 4, 4, 3, 1, 2, 2, 2]
def baseStart_1758345 : Nat := 118140960795 + 1758345 * 2 ^ 59
def prefixEnd_1758345 : Nat := 4983230072969 + 3 ^ 40 * 1758345 * 2
def baseEnd_1758345 : Nat := 902876141430028200801025

theorem tailTrace_1758345 : CollatzResearch.WordTrace tailWord_1758345 prefixEnd_1758345 902876141430028200801025 := by
  unfold tailWord_1758345
  simp only [CollatzResearch.WordTrace]
  refine ⟨64132110814823841262892489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42754740543215894175261659 64132110814823841262892489)
  ·
    refine ⟨48099083111117880947169367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64132110814823841262892489 48099083111117880947169367)
    ·
      refine ⟨72148624666676821420754051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48099083111117880947169367 72148624666676821420754051)
      ·
        refine ⟨108222937000015232131131077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72148624666676821420754051 108222937000015232131131077)
        ·
          refine ⟨20291800687502856024587077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108222937000015232131131077 20291800687502856024587077)
          ·
            refine ⟨3804712628906785504610077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20291800687502856024587077 3804712628906785504610077)
            ·
              refine ⟨1426767235840044564228779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3804712628906785504610077 1426767235840044564228779)
              ·
                refine ⟨2140150853760066846343169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1426767235840044564228779 2140150853760066846343169)
                ·
                  refine ⟨1605113140320050134757377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2140150853760066846343169 1605113140320050134757377)
                  ·
                    refine ⟨1203834855240037601068033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1605113140320050134757377 1203834855240037601068033)
                    ·
                      refine ⟨902876141430028200801025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1203834855240037601068033 902876141430028200801025)
                      ·
                        rfl

theorem cell23_1758345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 2, 2, 2].length) (baseStart_1758345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758345 prefixEnd_1758345 := by exact prefixLift 1758345
  have htrace : WordTrace (prefixWord ++ tailWord_1758345) baseStart_1758345 baseEnd_1758345 := by
    simpa [prefixWord, tailWord_1758345, baseEnd_1758345] using wordTrace_append hprefix tailTrace_1758345
  have hstable : (prefixWord ++ tailWord_1758345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758345).length < 2 ^ (prefixWord ++ tailWord_1758345).sum := by decide
  have hdescent : baseEnd_1758345 < baseStart_1758345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758357 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 3, 1, 7]
def baseStart_1758357 : Nat := 118140960795 + 1758357 * 2 ^ 59
def prefixEnd_1758357 : Nat := 4983230072969 + 3 ^ 40 * 1758357 * 2
def baseEnd_1758357 : Nat := 902882303197882153850969

theorem tailTrace_1758357 : CollatzResearch.WordTrace tailWord_1758357 prefixEnd_1758357 902882303197882153850969 := by
  unfold tailWord_1758357
  simp only [CollatzResearch.WordTrace]
  refine ⟨64132548490780367312329325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42755032327186911541552883 64132548490780367312329325)
  ·
    refine ⟨24049705684042637742123497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64132548490780367312329325 24049705684042637742123497)
    ·
      refine ⟨18037279263031978306592623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24049705684042637742123497 18037279263031978306592623)
      ·
        refine ⟨27055918894547967459888935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18037279263031978306592623 27055918894547967459888935)
        ·
          refine ⟨40583878341821951189833403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27055918894547967459888935 40583878341821951189833403)
          ·
            refine ⟨60875817512732926784750105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40583878341821951189833403 60875817512732926784750105)
            ·
              refine ⟨45656863134549695088562579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60875817512732926784750105 45656863134549695088562579)
              ·
                refine ⟨68485294701824542632843869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45656863134549695088562579 68485294701824542632843869)
                ·
                  refine ⟨25681985513184203487316451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68485294701824542632843869 25681985513184203487316451)
                  ·
                    refine ⟨38522978269776305230974677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25681985513184203487316451 38522978269776305230974677)
                    ·
                      refine ⟨902882303197882153850969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38522978269776305230974677 902882303197882153850969)
                      ·
                        rfl

theorem cell23_1758357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_1758357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758357 prefixEnd_1758357 := by exact prefixLift 1758357
  have htrace : WordTrace (prefixWord ++ tailWord_1758357) baseStart_1758357 baseEnd_1758357 := by
    simpa [prefixWord, tailWord_1758357, baseEnd_1758357] using wordTrace_append hprefix tailTrace_1758357
  have hstable : (prefixWord ++ tailWord_1758357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758357).length < 2 ^ (prefixWord ++ tailWord_1758357).sum := by decide
  have hdescent : baseEnd_1758357 < baseStart_1758357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758364 : List Nat := [2, 2, 3, 2, 1, 2, 2, 1, 1, 7]
def baseStart_1758364 : Nat := 118140960795 + 1758364 * 2 ^ 59
def prefixEnd_1758364 : Nat := 4983230072969 + 3 ^ 40 * 1758364 * 2
def baseEnd_1758364 : Nat := 300961965854154542154479

theorem tailTrace_1758364 : CollatzResearch.WordTrace tailWord_1758364 prefixEnd_1758364 300961965854154542154479 := by
  unfold tailWord_1758364
  simp only [CollatzResearch.WordTrace]
  refine ⟨32066401900877503753917073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42755202534503338338556097 32066401900877503753917073)
  ·
    refine ⟨24049801425658127815437805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32066401900877503753917073 24049801425658127815437805)
    ·
      refine ⟨9018675534621797930789177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24049801425658127815437805 9018675534621797930789177)
      ·
        refine ⟨6764006650966348448091883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9018675534621797930789177 6764006650966348448091883)
        ·
          refine ⟨10146009976449522672137825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6764006650966348448091883 10146009976449522672137825)
          ·
            refine ⟨7609507482337142004103369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10146009976449522672137825 7609507482337142004103369)
            ·
              refine ⟨5707130611752856503077527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7609507482337142004103369 5707130611752856503077527)
              ·
                refine ⟨8560695917629284754616291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5707130611752856503077527 8560695917629284754616291)
                ·
                  refine ⟨12841043876443927131924437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8560695917629284754616291 12841043876443927131924437)
                  ·
                    refine ⟨300961965854154542154479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12841043876443927131924437 300961965854154542154479)
                    ·
                      rfl

theorem cell23_1758364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_1758364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758364 prefixEnd_1758364 := by exact prefixLift 1758364
  have htrace : WordTrace (prefixWord ++ tailWord_1758364) baseStart_1758364 baseEnd_1758364 := by
    simpa [prefixWord, tailWord_1758364, baseEnd_1758364] using wordTrace_append hprefix tailTrace_1758364
  have hstable : (prefixWord ++ tailWord_1758364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758364).length < 2 ^ (prefixWord ++ tailWord_1758364).sum := by decide
  have hdescent : baseEnd_1758364 < baseStart_1758364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758384 : List Nat := [2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 4]
def baseStart_1758384 : Nat := 118140960795 + 1758384 * 2 ^ 59
def prefixEnd_1758384 : Nat := 4983230072969 + 3 ^ 40 * 1758384 * 2
def baseEnd_1758384 : Nat := 902896167175553548213345

theorem tailTrace_1758384 : CollatzResearch.WordTrace tailWord_1758384 prefixEnd_1758384 902896167175553548213345 := by
  unfold tailWord_1758384
  simp only [CollatzResearch.WordTrace]
  refine ⟨32066766630841275461781103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42755688841121700615708137 32066766630841275461781103)
  ·
    refine ⟨48100149946261913192671655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32066766630841275461781103 48100149946261913192671655)
    ·
      refine ⟨72150224919392869789007483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48100149946261913192671655 72150224919392869789007483)
      ·
        refine ⟨108225337379089304683511225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72150224919392869789007483 108225337379089304683511225)
        ·
          refine ⟨81169003034316978512633419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108225337379089304683511225 81169003034316978512633419)
          ·
            refine ⟨121753504551475467768950129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81169003034316978512633419 121753504551475467768950129)
            ·
              refine ⟨91315128413606600826712597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121753504551475467768950129 91315128413606600826712597)
              ·
                refine ⟨4280396644387809413752153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91315128413606600826712597 4280396644387809413752153)
                ·
                  refine ⟨3210297483290857060314115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4280396644387809413752153 3210297483290857060314115)
                  ·
                    refine ⟨4815446224936285590471173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3210297483290857060314115 4815446224936285590471173)
                    ·
                      refine ⟨902896167175553548213345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4815446224936285590471173 902896167175553548213345)
                      ·
                        rfl

theorem cell23_1758384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 4].length) (baseStart_1758384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758384 prefixEnd_1758384 := by exact prefixLift 1758384
  have htrace : WordTrace (prefixWord ++ tailWord_1758384) baseStart_1758384 baseEnd_1758384 := by
    simpa [prefixWord, tailWord_1758384, baseEnd_1758384] using wordTrace_append hprefix tailTrace_1758384
  have hstable : (prefixWord ++ tailWord_1758384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758384).length < 2 ^ (prefixWord ++ tailWord_1758384).sum := by decide
  have hdescent : baseEnd_1758384 < baseStart_1758384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758445 : List Nat := [1, 5, 1, 2, 2, 2, 1, 4, 1, 4]
def baseStart_1758445 : Nat := 118140960795 + 1758445 * 2 ^ 59
def prefixEnd_1758445 : Nat := 4983230072969 + 3 ^ 40 * 1758445 * 2
def baseEnd_1758445 : Nat := 300975829831825936516855

theorem tailTrace_1758445 : CollatzResearch.WordTrace tailWord_1758445 prefixEnd_1758445 300975829831825936516855 := by
  unfold tailWord_1758445
  simp only [CollatzResearch.WordTrace]
  refine ⟨64135758114461558341532789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42757172076307705561021859 64135758114461558341532789)
  ·
    refine ⟨6012727323230771094518699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64135758114461558341532789 6012727323230771094518699)
    ·
      refine ⟨9019090984846156641778049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6012727323230771094518699 9019090984846156641778049)
      ·
        refine ⟨6764318238634617481333537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9019090984846156641778049 6764318238634617481333537)
        ·
          refine ⟨5073238678975963111000153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6764318238634617481333537 5073238678975963111000153)
          ·
            refine ⟨3804929009231972333250115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5073238678975963111000153 3804929009231972333250115)
            ·
              refine ⟨5707393513847958499875173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3804929009231972333250115 5707393513847958499875173)
              ·
                refine ⟨1070136283846492218726595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5707393513847958499875173 1070136283846492218726595)
                ·
                  refine ⟨1605204425769738328089893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1070136283846492218726595 1605204425769738328089893)
                  ·
                    refine ⟨300975829831825936516855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1605204425769738328089893 300975829831825936516855)
                    ·
                      rfl

theorem cell23_1758445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_1758445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758445 prefixEnd_1758445 := by exact prefixLift 1758445
  have htrace : WordTrace (prefixWord ++ tailWord_1758445) baseStart_1758445 baseEnd_1758445 := by
    simpa [prefixWord, tailWord_1758445, baseEnd_1758445] using wordTrace_append hprefix tailTrace_1758445
  have hstable : (prefixWord ++ tailWord_1758445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758445).length < 2 ^ (prefixWord ++ tailWord_1758445).sum := by decide
  have hdescent : baseEnd_1758445 < baseStart_1758445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758468 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 5, 1, 3]
def baseStart_1758468 : Nat := 118140960795 + 1758468 * 2 ^ 59
def prefixEnd_1758468 : Nat := 4983230072969 + 3 ^ 40 * 1758468 * 2
def baseEnd_1758468 : Nat := 902939299550531219562959

theorem tailTrace_1758468 : CollatzResearch.WordTrace tailWord_1758468 prefixEnd_1758468 902939299550531219562959 := by
  unfold tailWord_1758468
  simp only [CollatzResearch.WordTrace]
  refine ⟨32068298496689116634810029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42757731328918822179746705 32068298496689116634810029)
  ·
    refine ⟨12025611936258418738053761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32068298496689116634810029 12025611936258418738053761)
    ·
      refine ⟨9019208952193814053540321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12025611936258418738053761 9019208952193814053540321)
      ·
        refine ⟨6764406714145360540155241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9019208952193814053540321 6764406714145360540155241)
        ·
          refine ⟨5073305035609020405116431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6764406714145360540155241 5073305035609020405116431)
          ·
            refine ⟨7609957553413530607674647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5073305035609020405116431 7609957553413530607674647)
            ·
              refine ⟨11414936330120295911511971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7609957553413530607674647 11414936330120295911511971)
              ·
                refine ⟨17122404495180443867267957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11414936330120295911511971 17122404495180443867267957)
                ·
                  refine ⟨1605225421423166612556371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17122404495180443867267957 1605225421423166612556371)
                  ·
                    refine ⟨2407838132134749918834557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1605225421423166612556371 2407838132134749918834557)
                    ·
                      refine ⟨902939299550531219562959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2407838132134749918834557 902939299550531219562959)
                      ·
                        rfl

theorem cell23_1758468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_1758468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758468 prefixEnd_1758468 := by exact prefixLift 1758468
  have htrace : WordTrace (prefixWord ++ tailWord_1758468) baseStart_1758468 baseEnd_1758468 := by
    simpa [prefixWord, tailWord_1758468, baseEnd_1758468] using wordTrace_append hprefix tailTrace_1758468
  have hstable : (prefixWord ++ tailWord_1758468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758468).length < 2 ^ (prefixWord ++ tailWord_1758468).sum := by decide
  have hdescent : baseEnd_1758468 < baseStart_1758468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758478 : List Nat := [4, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2]
def baseStart_1758478 : Nat := 118140960795 + 1758478 * 2 ^ 59
def prefixEnd_1758478 : Nat := 4983230072969 + 3 ^ 40 * 1758478 * 2
def baseEnd_1758478 : Nat := 902944434357076180437913

theorem tailTrace_1758478 : CollatzResearch.WordTrace tailWord_1758478 prefixEnd_1758478 902944434357076180437913 := by
  unfold tailWord_1758478
  simp only [CollatzResearch.WordTrace]
  refine ⟨8017120215417750622185511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42757974482228003318322725 8017120215417750622185511)
  ·
    refine ⟨12025680323126625933278267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8017120215417750622185511 12025680323126625933278267)
    ·
      refine ⟨18038520484689938899917401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12025680323126625933278267 18038520484689938899917401)
      ·
        refine ⟨13528890363517454174938051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18038520484689938899917401 13528890363517454174938051)
        ·
          refine ⟨20293335545276181262407077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13528890363517454174938051 20293335545276181262407077)
          ·
            refine ⟨3805000414739283986701327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20293335545276181262407077 3805000414739283986701327)
            ·
              refine ⟨5707500622108925980051991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3805000414739283986701327 5707500622108925980051991)
              ·
                refine ⟨8561250933163388970077987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5707500622108925980051991 8561250933163388970077987)
                ·
                  refine ⟨12841876399745083455116981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8561250933163388970077987 12841876399745083455116981)
                  ·
                    refine ⟨1203925912476101573917217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12841876399745083455116981 1203925912476101573917217)
                    ·
                      refine ⟨902944434357076180437913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1203925912476101573917217 902944434357076180437913)
                      ·
                        rfl

theorem cell23_1758478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_1758478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758478 prefixEnd_1758478 := by exact prefixLift 1758478
  have htrace : WordTrace (prefixWord ++ tailWord_1758478) baseStart_1758478 baseEnd_1758478 := by
    simpa [prefixWord, tailWord_1758478, baseEnd_1758478] using wordTrace_append hprefix tailTrace_1758478
  have hstable : (prefixWord ++ tailWord_1758478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758478).length < 2 ^ (prefixWord ++ tailWord_1758478).sum := by decide
  have hdescent : baseEnd_1758478 < baseStart_1758478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758488 : List Nat := [2, 1, 2, 3, 1, 3, 4, 1, 1, 5]
def baseStart_1758488 : Nat := 118140960795 + 1758488 * 2 ^ 59
def prefixEnd_1758488 : Nat := 4983230072969 + 3 ^ 40 * 1758488 * 2
def baseEnd_1758488 : Nat := 300983189721207047104289

theorem tailTrace_1758488 : CollatzResearch.WordTrace tailWord_1758488 prefixEnd_1758488 300983189721207047104289 := by
  unfold tailWord_1758488
  simp only [CollatzResearch.WordTrace]
  refine ⟨32068663226652888342674059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42758217635537184456898745 32068663226652888342674059)
  ·
    refine ⟨48102994839979332514011089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32068663226652888342674059 48102994839979332514011089)
    ·
      refine ⟨36077246129984499385508317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48102994839979332514011089 36077246129984499385508317)
      ·
        refine ⟨13528967298744187269565619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36077246129984499385508317 13528967298744187269565619)
        ·
          refine ⟨20293450948116280904348429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13528967298744187269565619 20293450948116280904348429)
          ·
            refine ⟨7610044105543605339130661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20293450948116280904348429 7610044105543605339130661)
            ·
              refine ⟨1426883269789426001086999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7610044105543605339130661 1426883269789426001086999)
              ·
                refine ⟨2140324904684139001630499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1426883269789426001086999 2140324904684139001630499)
                ·
                  refine ⟨3210487357026208502445749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2140324904684139001630499 3210487357026208502445749)
                  ·
                    refine ⟨300983189721207047104289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3210487357026208502445749 300983189721207047104289)
                    ·
                      rfl

theorem cell23_1758488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 1, 5].length) (baseStart_1758488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758488 prefixEnd_1758488 := by exact prefixLift 1758488
  have htrace : WordTrace (prefixWord ++ tailWord_1758488) baseStart_1758488 baseEnd_1758488 := by
    simpa [prefixWord, tailWord_1758488, baseEnd_1758488] using wordTrace_append hprefix tailTrace_1758488
  have hstable : (prefixWord ++ tailWord_1758488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758488).length < 2 ^ (prefixWord ++ tailWord_1758488).sum := by decide
  have hdescent : baseEnd_1758488 < baseStart_1758488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758528 : List Nat := [2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 3]
def baseStart_1758528 : Nat := 118140960795 + 1758528 * 2 ^ 59
def prefixEnd_1758528 : Nat := 4983230072969 + 3 ^ 40 * 1758528 * 2
def baseEnd_1758528 : Nat := 902970108389800984812683

theorem tailTrace_1758528 : CollatzResearch.WordTrace tailWord_1758528 prefixEnd_1758528 902970108389800984812683 := by
  unfold tailWord_1758528
  simp only [CollatzResearch.WordTrace]
  refine ⟨32069392686580431758402119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42759190248773909011202825 32069392686580431758402119)
  ·
    refine ⟨48104089029870647637603179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32069392686580431758402119 48104089029870647637603179)
    ·
      refine ⟨72156133544805971456404769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48104089029870647637603179 72156133544805971456404769)
      ·
        refine ⟨54117100158604478592303577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72156133544805971456404769 54117100158604478592303577)
        ·
          refine ⟨40587825118953358944227683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54117100158604478592303577 40587825118953358944227683)
          ·
            refine ⟨60881737678430038416341525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40587825118953358944227683 60881737678430038416341525)
            ·
              refine ⟨2853831453676408050766009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60881737678430038416341525 2853831453676408050766009)
              ·
                refine ⟨2140373590257306038074507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2853831453676408050766009 2140373590257306038074507)
                ·
                  refine ⟨3210560385385959057111761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2140373590257306038074507 3210560385385959057111761)
                  ·
                    refine ⟨2407920289039469292833821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3210560385385959057111761 2407920289039469292833821)
                    ·
                      refine ⟨902970108389800984812683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2407920289039469292833821 902970108389800984812683)
                      ·
                        rfl

theorem cell23_1758528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 3].length) (baseStart_1758528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758528 prefixEnd_1758528 := by exact prefixLift 1758528
  have htrace : WordTrace (prefixWord ++ tailWord_1758528) baseStart_1758528 baseEnd_1758528 := by
    simpa [prefixWord, tailWord_1758528, baseEnd_1758528] using wordTrace_append hprefix tailTrace_1758528
  have hstable : (prefixWord ++ tailWord_1758528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758528).length < 2 ^ (prefixWord ++ tailWord_1758528).sum := by decide
  have hdescent : baseEnd_1758528 < baseStart_1758528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758584 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 2, 2, 9]
def baseStart_1758584 : Nat := 118140960795 + 1758584 * 2 ^ 59
def prefixEnd_1758584 : Nat := 4983230072969 + 3 ^ 40 * 1758584 * 2
def baseEnd_1758584 : Nat := 902998863306452765712425

theorem tailTrace_1758584 : CollatzResearch.WordTrace tailWord_1758584 prefixEnd_1758584 902998863306452765712425 := by
  unfold tailWord_1758584
  simp only [CollatzResearch.WordTrace]
  refine ⟨32070413930478992540421403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42760551907305323387228537 32070413930478992540421403)
  ·
    refine ⟨48105620895718488810632105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32070413930478992540421403 48105620895718488810632105)
    ·
      refine ⟨36079215671788866607974079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48105620895718488810632105 36079215671788866607974079)
      ·
        refine ⟨54118823507683299911961119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36079215671788866607974079 54118823507683299911961119)
        ·
          refine ⟨81178235261524949867941679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54118823507683299911961119 81178235261524949867941679)
          ·
            refine ⟨121767352892287424801912519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81178235261524949867941679 121767352892287424801912519)
            ·
              refine ⟨182651029338431137202868779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121767352892287424801912519 182651029338431137202868779)
              ·
                refine ⟨273976544007646705804303169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182651029338431137202868779 273976544007646705804303169)
                ·
                  refine ⟨205482408005735029353227377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273976544007646705804303169 205482408005735029353227377)
                  ·
                    refine ⟨154111806004301272014920533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 205482408005735029353227377 154111806004301272014920533)
                    ·
                      refine ⟨902998863306452765712425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 154111806004301272014920533 902998863306452765712425)
                      ·
                        rfl

theorem cell23_1758584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_1758584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758584 prefixEnd_1758584 := by exact prefixLift 1758584
  have htrace : WordTrace (prefixWord ++ tailWord_1758584) baseStart_1758584 baseEnd_1758584 := by
    simpa [prefixWord, tailWord_1758584, baseEnd_1758584] using wordTrace_append hprefix tailTrace_1758584
  have hstable : (prefixWord ++ tailWord_1758584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758584).length < 2 ^ (prefixWord ++ tailWord_1758584).sum := by decide
  have hdescent : baseEnd_1758584 < baseStart_1758584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758585 : List Nat := [1, 2, 1, 3, 2, 1, 5, 2, 1, 3, 2]
def baseStart_1758585 : Nat := 118140960795 + 1758585 * 2 ^ 59
def prefixEnd_1758585 : Nat := 4983230072969 + 3 ^ 40 * 1758585 * 2
def baseEnd_1758585 : Nat := 902999376787107261799921

theorem tailTrace_1758585 : CollatzResearch.WordTrace tailWord_1758585 prefixEnd_1758585 902999376787107261799921 := by
  unfold tailWord_1758585
  simp only [CollatzResearch.WordTrace]
  refine ⟨64140864333954362251629209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42760576222636241501086139 64140864333954362251629209)
  ·
    refine ⟨48105648250465771688721907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64140864333954362251629209 48105648250465771688721907)
    ·
      refine ⟨72158472375698657533082861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48105648250465771688721907 72158472375698657533082861)
      ·
        refine ⟨27059427140886996574906073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72158472375698657533082861 27059427140886996574906073)
        ·
          refine ⟨20294570355665247431179555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27059427140886996574906073 20294570355665247431179555)
          ·
            refine ⟨30441855533497871146769333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20294570355665247431179555 30441855533497871146769333)
            ·
              refine ⟨2853923956265425420009625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30441855533497871146769333 2853923956265425420009625)
              ·
                refine ⟨2140442967199069065007219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2853923956265425420009625 2140442967199069065007219)
                ·
                  refine ⟨3210664450798603597510829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2140442967199069065007219 3210664450798603597510829)
                  ·
                    refine ⟨1203999169049476349066561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3210664450798603597510829 1203999169049476349066561)
                    ·
                      refine ⟨902999376787107261799921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1203999169049476349066561 902999376787107261799921)
                      ·
                        rfl

theorem cell23_1758585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 3, 2].length) (baseStart_1758585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758585 prefixEnd_1758585 := by exact prefixLift 1758585
  have htrace : WordTrace (prefixWord ++ tailWord_1758585) baseStart_1758585 baseEnd_1758585 := by
    simpa [prefixWord, tailWord_1758585, baseEnd_1758585] using wordTrace_append hprefix tailTrace_1758585
  have hstable : (prefixWord ++ tailWord_1758585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758585).length < 2 ^ (prefixWord ++ tailWord_1758585).sum := by decide
  have hdescent : baseEnd_1758585 < baseStart_1758585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758610 : List Nat := [3, 2, 3, 3, 2, 1, 2, 2, 1, 2, 2]
def baseStart_1758610 : Nat := 118140960795 + 1758610 * 2 ^ 59
def prefixEnd_1758610 : Nat := 4983230072969 + 3 ^ 40 * 1758610 * 2
def baseEnd_1758610 : Nat := 903012213803469663987307

theorem tailTrace_1758610 : CollatzResearch.WordTrace tailWord_1758610 prefixEnd_1758610 903012213803469663987307 := by
  unfold tailWord_1758610
  simp only [CollatzResearch.WordTrace]
  refine ⟨16035444039715947880322321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42761184105909194347526189 16035444039715947880322321)
  ·
    refine ⟨12026583029786960910241741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16035444039715947880322321 12026583029786960910241741)
    ·
      refine ⟨4509968636170110341340653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12026583029786960910241741 4509968636170110341340653)
      ·
        refine ⟨1691238238563791378002745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4509968636170110341340653 1691238238563791378002745)
        ·
          refine ⟨1268428678922843533502059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1691238238563791378002745 1268428678922843533502059)
          ·
            refine ⟨1902643018384265300253089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1268428678922843533502059 1902643018384265300253089)
            ·
              refine ⟨1426982263788198975189817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1902643018384265300253089 1426982263788198975189817)
              ·
                refine ⟨1070236697841149231392363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1426982263788198975189817 1070236697841149231392363)
                ·
                  refine ⟨1605355046761723847088545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1070236697841149231392363 1605355046761723847088545)
                  ·
                    refine ⟨1204016285071292885316409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1605355046761723847088545 1204016285071292885316409)
                    ·
                      refine ⟨903012213803469663987307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1204016285071292885316409 903012213803469663987307)
                      ·
                        rfl

theorem cell23_1758610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_1758610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758610 prefixEnd_1758610 := by exact prefixLift 1758610
  have htrace : WordTrace (prefixWord ++ tailWord_1758610) baseStart_1758610 baseEnd_1758610 := by
    simpa [prefixWord, tailWord_1758610, baseEnd_1758610] using wordTrace_append hprefix tailTrace_1758610
  have hstable : (prefixWord ++ tailWord_1758610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758610).length < 2 ^ (prefixWord ++ tailWord_1758610).sum := by decide
  have hdescent : baseEnd_1758610 < baseStart_1758610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758688 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 1, 6, 2]
def baseStart_1758688 : Nat := 118140960795 + 1758688 * 2 ^ 59
def prefixEnd_1758688 : Nat := 4983230072969 + 3 ^ 40 * 1758688 * 2
def baseEnd_1758688 : Nat := 903052265294520358811947

theorem tailTrace_1758688 : CollatzResearch.WordTrace tailWord_1758688 prefixEnd_1758688 903052265294520358811947 := by
  unfold tailWord_1758688
  simp only [CollatzResearch.WordTrace]
  refine ⟨32072310526290605421314359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42763080701720807228419145 32072310526290605421314359)
  ·
    refine ⟨48108465789435908131971539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32072310526290605421314359 48108465789435908131971539)
    ·
      refine ⟨72162698684153862197957309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48108465789435908131971539 72162698684153862197957309)
      ·
        refine ⟨27061012006557698324233991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72162698684153862197957309 27061012006557698324233991)
        ·
          refine ⟨40591518009836547486350987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27061012006557698324233991 40591518009836547486350987)
          ·
            refine ⟨60887277014754821229526481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40591518009836547486350987 60887277014754821229526481)
            ·
              refine ⟨45665457761066115922144861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60887277014754821229526481 45665457761066115922144861)
              ·
                refine ⟨17124546660399793470804323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45665457761066115922144861 17124546660399793470804323)
                ·
                  refine ⟨25686819990599690206206485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17124546660399793470804323 25686819990599690206206485)
                  ·
                    refine ⟨1204069687059360478415929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25686819990599690206206485 1204069687059360478415929)
                    ·
                      refine ⟨903052265294520358811947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1204069687059360478415929 903052265294520358811947)
                      ·
                        rfl

theorem cell23_1758688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 1, 6, 2].length) (baseStart_1758688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758688 prefixEnd_1758688 := by exact prefixLift 1758688
  have htrace : WordTrace (prefixWord ++ tailWord_1758688) baseStart_1758688 baseEnd_1758688 := by
    simpa [prefixWord, tailWord_1758688, baseEnd_1758688] using wordTrace_append hprefix tailTrace_1758688
  have hstable : (prefixWord ++ tailWord_1758688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758688).length < 2 ^ (prefixWord ++ tailWord_1758688).sum := by decide
  have hdescent : baseEnd_1758688 < baseStart_1758688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758722 : List Nat := [3, 4, 1, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_1758722 : Nat := 118140960795 + 1758722 * 2 ^ 59
def prefixEnd_1758722 : Nat := 4983230072969 + 3 ^ 40 * 1758722 * 2
def baseEnd_1758722 : Nat := 903069723636773225786791

theorem tailTrace_1758722 : CollatzResearch.WordTrace tailWord_1758722 prefixEnd_1758722 903069723636773225786791 := by
  unfold tailWord_1758722
  simp only [CollatzResearch.WordTrace]
  refine ⟨16036465283614508662341605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42763907422972023099577613 16036465283614508662341605)
  ·
    refine ⟨3006837240677720374189051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16036465283614508662341605 3006837240677720374189051)
    ·
      refine ⟨4510255861016580561283577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3006837240677720374189051 4510255861016580561283577)
      ·
        refine ⟨3382691895762435420962683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4510255861016580561283577 3382691895762435420962683)
        ·
          refine ⟨5074037843643653131444025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3382691895762435420962683 5074037843643653131444025)
          ·
            refine ⟨3805528382732739848583019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5074037843643653131444025 3805528382732739848583019)
            ·
              refine ⟨5708292574099109772874529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3805528382732739848583019 5708292574099109772874529)
              ·
                refine ⟨4281219430574332329655897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5708292574099109772874529 4281219430574332329655897)
                ·
                  refine ⟨3210914572930749247241923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4281219430574332329655897 3210914572930749247241923)
                  ·
                    refine ⟨4816371859396123870862885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3210914572930749247241923 4816371859396123870862885)
                    ·
                      refine ⟨903069723636773225786791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4816371859396123870862885 903069723636773225786791)
                      ·
                        rfl

theorem cell23_1758722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_1758722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758722 prefixEnd_1758722 := by exact prefixLift 1758722
  have htrace : WordTrace (prefixWord ++ tailWord_1758722) baseStart_1758722 baseEnd_1758722 := by
    simpa [prefixWord, tailWord_1758722, baseEnd_1758722] using wordTrace_append hprefix tailTrace_1758722
  have hstable : (prefixWord ++ tailWord_1758722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758722).length < 2 ^ (prefixWord ++ tailWord_1758722).sum := by decide
  have hdescent : baseEnd_1758722 < baseStart_1758722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758732 : List Nat := [2, 2, 1, 2, 5, 2, 1, 1, 3, 4]
def baseStart_1758732 : Nat := 118140960795 + 1758732 * 2 ^ 59
def prefixEnd_1758732 : Nat := 4983230072969 + 3 ^ 40 * 1758732 * 2
def baseEnd_1758732 : Nat := 301024952814439395553915

theorem tailTrace_1758732 : CollatzResearch.WordTrace tailWord_1758732 prefixEnd_1758732 301024952814439395553915 := by
  unfold tailWord_1758732
  simp only [CollatzResearch.WordTrace]
  refine ⟨32073112932210903178615225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42764150576281204238153633 32073112932210903178615225)
  ·
    refine ⟨24054834699158177383961419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32073112932210903178615225 24054834699158177383961419)
    ·
      refine ⟨36082252048737266075942129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24054834699158177383961419 36082252048737266075942129)
      ·
        refine ⟨27061689036552949556956597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36082252048737266075942129 27061689036552949556956597)
        ·
          refine ⟨2537033347176839020964681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27061689036552949556956597 2537033347176839020964681)
          ·
            refine ⟨1902775010382629265723511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2537033347176839020964681 1902775010382629265723511)
            ·
              refine ⟨2854162515573943898585267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1902775010382629265723511 2854162515573943898585267)
              ·
                refine ⟨4281243773360915847877901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2854162515573943898585267 4281243773360915847877901)
                ·
                  refine ⟨1605466415010343442954213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4281243773360915847877901 1605466415010343442954213)
                  ·
                    refine ⟨301024952814439395553915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1605466415010343442954213 301024952814439395553915)
                    ·
                      rfl

theorem cell23_1758732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 3, 4].length) (baseStart_1758732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758732 prefixEnd_1758732 := by exact prefixLift 1758732
  have htrace : WordTrace (prefixWord ++ tailWord_1758732) baseStart_1758732 baseEnd_1758732 := by
    simpa [prefixWord, tailWord_1758732, baseEnd_1758732] using wordTrace_append hprefix tailTrace_1758732
  have hstable : (prefixWord ++ tailWord_1758732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758732).length < 2 ^ (prefixWord ++ tailWord_1758732).sum := by decide
  have hdescent : baseEnd_1758732 < baseStart_1758732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758798 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5]
def baseStart_1758798 : Nat := 118140960795 + 1758798 * 2 ^ 59
def prefixEnd_1758798 : Nat := 4983230072969 + 3 ^ 40 * 1758798 * 2
def baseEnd_1758798 : Nat := 903108748166514928436441

theorem tailTrace_1758798 : CollatzResearch.WordTrace tailWord_1758798 prefixEnd_1758798 903108748166514928436441 := by
  unfold tailWord_1758798
  simp only [CollatzResearch.WordTrace]
  refine ⟨8018579135272837453641631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42765755388121799752755365 8018579135272837453641631)
  ·
    refine ⟨12027868702909256180462447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8018579135272837453641631 12027868702909256180462447)
    ·
      refine ⟨18041803054363884270693671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12027868702909256180462447 18041803054363884270693671)
      ·
        refine ⟨27062704581545826406040507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18041803054363884270693671 27062704581545826406040507)
        ·
          refine ⟨40594056872318739609060761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27062704581545826406040507 40594056872318739609060761)
          ·
            refine ⟨30445542654239054706795571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40594056872318739609060761 30445542654239054706795571)
            ·
              refine ⟨45668313981358582060193357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30445542654239054706795571 45668313981358582060193357)
              ·
                refine ⟨17125617743009468272572509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45668313981358582060193357 17125617743009468272572509)
                ·
                  refine ⟨6422106653628550602214691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17125617743009468272572509 6422106653628550602214691)
                  ·
                    refine ⟨9633159980442825903322037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6422106653628550602214691 9633159980442825903322037)
                    ·
                      refine ⟨903108748166514928436441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9633159980442825903322037 903108748166514928436441)
                      ·
                        rfl

theorem cell23_1758798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_1758798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758798 prefixEnd_1758798 := by exact prefixLift 1758798
  have htrace : WordTrace (prefixWord ++ tailWord_1758798) baseStart_1758798 baseEnd_1758798 := by
    simpa [prefixWord, tailWord_1758798, baseEnd_1758798] using wordTrace_append hprefix tailTrace_1758798
  have hstable : (prefixWord ++ tailWord_1758798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758798).length < 2 ^ (prefixWord ++ tailWord_1758798).sum := by decide
  have hdescent : baseEnd_1758798 < baseStart_1758798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758832 : List Nat := [2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 3]
def baseStart_1758832 : Nat := 118140960795 + 1758832 * 2 ^ 59
def prefixEnd_1758832 : Nat := 4983230072969 + 3 ^ 40 * 1758832 * 2
def baseEnd_1758832 : Nat := 903126206508767795411285

theorem tailTrace_1758832 : CollatzResearch.WordTrace tailWord_1758832 prefixEnd_1758832 903126206508767795411285 := by
  unfold tailWord_1758832
  simp only [CollatzResearch.WordTrace]
  refine ⟨32074936582029761717935375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42766582109373015623913833 32074936582029761717935375)
  ·
    refine ⟨48112404873044642576903063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32074936582029761717935375 48112404873044642576903063)
    ·
      refine ⟨72168607309566963865354595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48112404873044642576903063 72168607309566963865354595)
      ·
        refine ⟨108252910964350445798031893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72168607309566963865354595 108252910964350445798031893)
        ·
          refine ⟨5074355201453927146782745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 108252910964350445798031893 5074355201453927146782745)
          ·
            refine ⟨3805766401090445360087059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5074355201453927146782745 3805766401090445360087059)
            ·
              refine ⟨5708649601635668040130589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3805766401090445360087059 5708649601635668040130589)
              ·
                refine ⟨2140743600613375515048971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5708649601635668040130589 2140743600613375515048971)
                ·
                  refine ⟨3211115400920063272573457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2140743600613375515048971 3211115400920063272573457)
                  ·
                    refine ⟨2408336550690047454430093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3211115400920063272573457 2408336550690047454430093)
                    ·
                      refine ⟨903126206508767795411285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2408336550690047454430093 903126206508767795411285)
                      ·
                        rfl

theorem cell23_1758832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 3].length) (baseStart_1758832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758832 prefixEnd_1758832 := by exact prefixLift 1758832
  have htrace : WordTrace (prefixWord ++ tailWord_1758832) baseStart_1758832 baseEnd_1758832 := by
    simpa [prefixWord, tailWord_1758832, baseEnd_1758832] using wordTrace_append hprefix tailTrace_1758832
  have hstable : (prefixWord ++ tailWord_1758832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758832).length < 2 ^ (prefixWord ++ tailWord_1758832).sum := by decide
  have hdescent : baseEnd_1758832 < baseStart_1758832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758856 : List Nat := [2, 1, 3, 5, 1, 1, 3, 1, 2, 4]
def baseStart_1758856 : Nat := 118140960795 + 1758856 * 2 ^ 59
def prefixEnd_1758856 : Nat := 4983230072969 + 3 ^ 40 * 1758856 * 2
def baseEnd_1758856 : Nat := 301046176681491900503725

theorem tailTrace_1758856 : CollatzResearch.WordTrace tailWord_1758856 prefixEnd_1758856 301046176681491900503725 := by
  unfold tailWord_1758856
  simp only [CollatzResearch.WordTrace]
  refine ⟨32075374257986287767372211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42767165677315050356496281 32075374257986287767372211)
  ·
    refine ⟨48113061386979431651058317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32075374257986287767372211 48113061386979431651058317)
    ·
      refine ⟨18042398020117286869146869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48113061386979431651058317 18042398020117286869146869)
      ·
        refine ⟨1691474814385995643982519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18042398020117286869146869 1691474814385995643982519)
        ·
          refine ⟨2537212221578993465973779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1691474814385995643982519 2537212221578993465973779)
          ·
            refine ⟨3805818332368490198960669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2537212221578993465973779 3805818332368490198960669)
            ·
              refine ⟨1427181874638183824610251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3805818332368490198960669 1427181874638183824610251)
              ·
                refine ⟨2140772811957275736915377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1427181874638183824610251 2140772811957275736915377)
                ·
                  refine ⟨1605579608967956802686533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2140772811957275736915377 1605579608967956802686533)
                  ·
                    refine ⟨301046176681491900503725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1605579608967956802686533 301046176681491900503725)
                    ·
                      rfl

theorem cell23_1758856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_1758856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758856 prefixEnd_1758856 := by exact prefixLift 1758856
  have htrace : WordTrace (prefixWord ++ tailWord_1758856) baseStart_1758856 baseEnd_1758856 := by
    simpa [prefixWord, tailWord_1758856, baseEnd_1758856] using wordTrace_append hprefix tailTrace_1758856
  have hstable : (prefixWord ++ tailWord_1758856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758856).length < 2 ^ (prefixWord ++ tailWord_1758856).sum := by decide
  have hdescent : baseEnd_1758856 < baseStart_1758856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758862 : List Nat := [4, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3]
def baseStart_1758862 : Nat := 118140960795 + 1758862 * 2 ^ 59
def prefixEnd_1758862 : Nat := 4983230072969 + 3 ^ 40 * 1758862 * 2
def baseEnd_1758862 : Nat := 903141610928402678036147

theorem tailTrace_1758862 : CollatzResearch.WordTrace tailWord_1758862 prefixEnd_1758862 903141610928402678036147 := by
  unfold tailWord_1758862
  simp only [CollatzResearch.WordTrace]
  refine ⟨8018870919243854819932855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42767311569300559039641893 8018870919243854819932855)
  ·
    refine ⟨12028306378865782229899283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8018870919243854819932855 12028306378865782229899283)
    ·
      refine ⟨18042459568298673344848925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12028306378865782229899283 18042459568298673344848925)
      ·
        refine ⟨6765922338112002504318347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18042459568298673344848925 6765922338112002504318347)
        ·
          refine ⟨10148883507168003756477521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6765922338112002504318347 10148883507168003756477521)
          ·
            refine ⟨7611662630376002817358141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10148883507168003756477521 7611662630376002817358141)
            ·
              refine ⟨2854373486391001056509303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7611662630376002817358141 2854373486391001056509303)
              ·
                refine ⟨4281560229586501584763955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2854373486391001056509303 4281560229586501584763955)
                ·
                  refine ⟨6422340344379752377145933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4281560229586501584763955 6422340344379752377145933)
                  ·
                    refine ⟨2408377629142407141429725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6422340344379752377145933 2408377629142407141429725)
                    ·
                      refine ⟨903141610928402678036147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2408377629142407141429725 903141610928402678036147)
                      ·
                        rfl

theorem cell23_1758862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_1758862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758862 prefixEnd_1758862 := by exact prefixLift 1758862
  have htrace : WordTrace (prefixWord ++ tailWord_1758862) baseStart_1758862 baseEnd_1758862 := by
    simpa [prefixWord, tailWord_1758862, baseEnd_1758862] using wordTrace_append hprefix tailTrace_1758862
  have hstable : (prefixWord ++ tailWord_1758862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758862).length < 2 ^ (prefixWord ++ tailWord_1758862).sum := by decide
  have hdescent : baseEnd_1758862 < baseStart_1758862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758919 : List Nat := [1, 1, 4, 1, 1, 1, 5, 3, 2, 2, 2]
def baseStart_1758919 : Nat := 118140960795 + 1758919 * 2 ^ 59
def prefixEnd_1758919 : Nat := 4983230072969 + 3 ^ 40 * 1758919 * 2
def baseEnd_1758919 : Nat := 903170879325708955023385

theorem tailTrace_1758919 : CollatzResearch.WordTrace tailWord_1758919 prefixEnd_1758919 903170879325708955023385 := by
  unfold tailWord_1758919
  simp only [CollatzResearch.WordTrace]
  refine ⟨64153046314744337294287811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42768697543162891529525207 64153046314744337294287811)
  ·
    refine ⟨96229569472116505941431717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64153046314744337294287811 96229569472116505941431717)
    ·
      refine ⟨18043044276021844864018447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96229569472116505941431717 18043044276021844864018447)
      ·
        refine ⟨27064566414032767296027671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18043044276021844864018447 27064566414032767296027671)
        ·
          refine ⟨40596849621049150944041507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27064566414032767296027671 40596849621049150944041507)
          ·
            refine ⟨60895274431573726416062261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40596849621049150944041507 60895274431573726416062261)
            ·
              refine ⟨5708931977960036851505837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60895274431573726416062261 5708931977960036851505837)
              ·
                refine ⟨2140849491735013819314689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5708931977960036851505837 2140849491735013819314689)
                ·
                  refine ⟨1605637118801260364486017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2140849491735013819314689 1605637118801260364486017)
                  ·
                    refine ⟨1204227839100945273364513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1605637118801260364486017 1204227839100945273364513)
                    ·
                      refine ⟨903170879325708955023385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1204227839100945273364513 903170879325708955023385)
                      ·
                        rfl

theorem cell23_1758919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2, 2, 2].length) (baseStart_1758919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758919 prefixEnd_1758919 := by exact prefixLift 1758919
  have htrace : WordTrace (prefixWord ++ tailWord_1758919) baseStart_1758919 baseEnd_1758919 := by
    simpa [prefixWord, tailWord_1758919, baseEnd_1758919] using wordTrace_append hprefix tailTrace_1758919
  have hstable : (prefixWord ++ tailWord_1758919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758919).length < 2 ^ (prefixWord ++ tailWord_1758919).sum := by decide
  have hdescent : baseEnd_1758919 < baseStart_1758919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758955 : List Nat := [1, 1, 1, 1, 2, 4, 4, 2, 2, 5]
def baseStart_1758955 : Nat := 118140960795 + 1758955 * 2 ^ 59
def prefixEnd_1758955 : Nat := 4983230072969 + 3 ^ 40 * 1758955 * 2
def baseEnd_1758955 : Nat := 301063121543090271391073

theorem tailTrace_1758955 : CollatzResearch.WordTrace tailWord_1758955 prefixEnd_1758955 301063121543090271391073 := by
  unfold tailWord_1758955
  simp only [CollatzResearch.WordTrace]
  refine ⟨64154359342613915442598319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42769572895075943628398879 64154359342613915442598319)
  ·
    refine ⟨96231539013920873163897479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64154359342613915442598319 96231539013920873163897479)
    ·
      refine ⟨144347308520881309745846219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96231539013920873163897479 144347308520881309745846219)
      ·
        refine ⟨216520962781321964618769329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144347308520881309745846219 216520962781321964618769329)
        ·
          refine ⟨162390722085991473464076997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216520962781321964618769329 162390722085991473464076997)
          ·
            refine ⟨30448260391123401274514437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162390722085991473464076997 30448260391123401274514437)
            ·
              refine ⟨5709048823335637738971457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30448260391123401274514437 5709048823335637738971457)
              ·
                refine ⟨4281786617501728304228593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5709048823335637738971457 4281786617501728304228593)
                ·
                  refine ⟨3211339963126296228171445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4281786617501728304228593 3211339963126296228171445)
                  ·
                    refine ⟨301063121543090271391073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3211339963126296228171445 301063121543090271391073)
                    ·
                      rfl

theorem cell23_1758955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 5].length) (baseStart_1758955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758955 prefixEnd_1758955 := by exact prefixLift 1758955
  have htrace : WordTrace (prefixWord ++ tailWord_1758955) baseStart_1758955 baseEnd_1758955 := by
    simpa [prefixWord, tailWord_1758955, baseEnd_1758955] using wordTrace_append hprefix tailTrace_1758955
  have hstable : (prefixWord ++ tailWord_1758955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758955).length < 2 ^ (prefixWord ++ tailWord_1758955).sum := by decide
  have hdescent : baseEnd_1758955 < baseStart_1758955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758962 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 1, 7, 2]
def baseStart_1758962 : Nat := 118140960795 + 1758962 * 2 ^ 59
def prefixEnd_1758962 : Nat := 4983230072969 + 3 ^ 40 * 1758962 * 2
def baseEnd_1758962 : Nat := 903192958993852286785687

theorem tailTrace_1758962 : CollatzResearch.WordTrace tailWord_1758962 prefixEnd_1758962 903192958993852286785687 := by
  unfold tailWord_1758962
  simp only [CollatzResearch.WordTrace]
  refine ⟨16038653663397138909525785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42769743102392370425402093 16038653663397138909525785)
  ·
    refine ⟨12028990247547854182144339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16038653663397138909525785 12028990247547854182144339)
    ·
      refine ⟨18043485371321781273216509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12028990247547854182144339 18043485371321781273216509)
      ·
        refine ⟨6766307014245667977456191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18043485371321781273216509 6766307014245667977456191)
        ·
          refine ⟨10149460521368501966184287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6766307014245667977456191 10149460521368501966184287)
          ·
            refine ⟨15224190782052752949276431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10149460521368501966184287 15224190782052752949276431)
            ·
              refine ⟨22836286173079129423914647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15224190782052752949276431 22836286173079129423914647)
              ·
                refine ⟨34254429259618694135871971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22836286173079129423914647 34254429259618694135871971)
                ·
                  refine ⟨51381643889428041203807957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34254429259618694135871971 51381643889428041203807957)
                  ·
                    refine ⟨1204257278658469715714249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51381643889428041203807957 1204257278658469715714249)
                    ·
                      refine ⟨903192958993852286785687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1204257278658469715714249 903192958993852286785687)
                      ·
                        rfl

theorem cell23_1758962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_1758962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758962 prefixEnd_1758962 := by exact prefixLift 1758962
  have htrace : WordTrace (prefixWord ++ tailWord_1758962) baseStart_1758962 baseEnd_1758962 := by
    simpa [prefixWord, tailWord_1758962, baseEnd_1758962] using wordTrace_append hprefix tailTrace_1758962
  have hstable : (prefixWord ++ tailWord_1758962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758962).length < 2 ^ (prefixWord ++ tailWord_1758962).sum := by decide
  have hdescent : baseEnd_1758962 < baseStart_1758962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758975 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 4]
def baseStart_1758975 : Nat := 118140960795 + 1758975 * 2 ^ 59
def prefixEnd_1758975 : Nat := 4983230072969 + 3 ^ 40 * 1758975 * 2
def baseEnd_1758975 : Nat := 903199634242360735923127

theorem tailTrace_1758975 : CollatzResearch.WordTrace tailWord_1758975 prefixEnd_1758975 903199634242360735923127 := by
  unfold tailWord_1758975
  simp only [CollatzResearch.WordTrace]
  refine ⟨64155088802541458858326379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42770059201694305905550919 64155088802541458858326379)
  ·
    refine ⟨96232633203812188287489569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64155088802541458858326379 96232633203812188287489569)
    ·
      refine ⟨72174474902859141215617177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96232633203812188287489569 72174474902859141215617177)
      ·
        refine ⟨54130856177144355911712883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72174474902859141215617177 54130856177144355911712883)
        ·
          refine ⟨81196284265716533867569325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54130856177144355911712883 81196284265716533867569325)
          ·
            refine ⟨30448606599643700200338497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81196284265716533867569325 30448606599643700200338497)
            ·
              refine ⟨22836454949732775150253873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30448606599643700200338497 22836454949732775150253873)
              ·
                refine ⟨17127341212299581362690405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22836454949732775150253873 17127341212299581362690405)
                ·
                  refine ⟨3211376477306171505504451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17127341212299581362690405 3211376477306171505504451)
                  ·
                    refine ⟨4817064715959257258256677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3211376477306171505504451 4817064715959257258256677)
                    ·
                      refine ⟨903199634242360735923127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4817064715959257258256677 903199634242360735923127)
                      ·
                        rfl

theorem cell23_1758975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_1758975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1758975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1758975 prefixEnd_1758975 := by exact prefixLift 1758975
  have htrace : WordTrace (prefixWord ++ tailWord_1758975) baseStart_1758975 baseEnd_1758975 := by
    simpa [prefixWord, tailWord_1758975, baseEnd_1758975] using wordTrace_append hprefix tailTrace_1758975
  have hstable : (prefixWord ++ tailWord_1758975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758975).length < 2 ^ (prefixWord ++ tailWord_1758975).sum := by decide
  have hdescent : baseEnd_1758975 < baseStart_1758975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759046 : List Nat := [6, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_1759046 : Nat := 118140960795 + 1759046 * 2 ^ 59
def prefixEnd_1759046 : Nat := 4983230072969 + 3 ^ 40 * 1759046 * 2
def baseEnd_1759046 : Nat := 903236091368829958135301

theorem tailTrace_1759046 : CollatzResearch.WordTrace tailWord_1759046 prefixEnd_1759046 903236091368829958135301 := by
  unfold tailWord_1759046
  simp only [CollatzResearch.WordTrace]
  refine ⟨2004927449540132437005031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42771785590189491989440661 2004927449540132437005031)
  ·
    refine ⟨3007391174310198655507547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2004927449540132437005031 3007391174310198655507547)
    ·
      refine ⟨4511086761465297983261321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3007391174310198655507547 4511086761465297983261321)
      ·
        refine ⟨3383315071098973487445991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4511086761465297983261321 3383315071098973487445991)
        ·
          refine ⟨5074972606648460231168987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3383315071098973487445991 5074972606648460231168987)
          ·
            refine ⟨7612458909972690346753481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5074972606648460231168987 7612458909972690346753481)
            ·
              refine ⟨5709344182479517760065111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7612458909972690346753481 5709344182479517760065111)
              ·
                refine ⟨8564016273719276640097667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5709344182479517760065111 8564016273719276640097667)
                ·
                  refine ⟨12846024410578914960146501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8564016273719276640097667 12846024410578914960146501)
                  ·
                    refine ⟨2408629576983546555027469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12846024410578914960146501 2408629576983546555027469)
                    ·
                      refine ⟨903236091368829958135301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2408629576983546555027469 903236091368829958135301)
                      ·
                        rfl

theorem cell23_1759046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_1759046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759046 prefixEnd_1759046 := by exact prefixLift 1759046
  have htrace : WordTrace (prefixWord ++ tailWord_1759046) baseStart_1759046 baseEnd_1759046 := by
    simpa [prefixWord, tailWord_1759046, baseEnd_1759046] using wordTrace_append hprefix tailTrace_1759046
  have hstable : (prefixWord ++ tailWord_1759046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759046).length < 2 ^ (prefixWord ++ tailWord_1759046).sum := by decide
  have hdescent : baseEnd_1759046 < baseStart_1759046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759053 : List Nat := [1, 6, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_1759053 : Nat := 118140960795 + 1759053 * 2 ^ 59
def prefixEnd_1759053 : Nat := 4983230072969 + 3 ^ 40 * 1759053 * 2
def baseEnd_1759053 : Nat := 301079895244470476915923

theorem tailTrace_1759053 : CollatzResearch.WordTrace tailWord_1759053 prefixEnd_1759053 301079895244470476915923 := by
  unfold tailWord_1759053
  simp only [CollatzResearch.WordTrace]
  refine ⟨64157933696258878179665813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42771955797505918786443875 64157933696258878179665813)
  ·
    refine ⟨3007403142012134914671835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 64157933696258878179665813 3007403142012134914671835)
    ·
      refine ⟨4511104713018202372007753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3007403142012134914671835 4511104713018202372007753)
      ·
        refine ⟨3383328534763651779005815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4511104713018202372007753 3383328534763651779005815)
        ·
          refine ⟨5074992802145477668508723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3383328534763651779005815 5074992802145477668508723)
          ·
            refine ⟨7612489203218216502763085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5074992802145477668508723 7612489203218216502763085)
            ·
              refine ⟨2854683451206831188536157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7612489203218216502763085 2854683451206831188536157)
              ·
                refine ⟨1070506294202561695701059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2854683451206831188536157 1070506294202561695701059)
                ·
                  refine ⟨1605759441303842543551589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1070506294202561695701059 1605759441303842543551589)
                  ·
                    refine ⟨301079895244470476915923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1605759441303842543551589 301079895244470476915923)
                    ·
                      rfl

theorem cell23_1759053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_1759053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759053 prefixEnd_1759053 := by exact prefixLift 1759053
  have htrace : WordTrace (prefixWord ++ tailWord_1759053) baseStart_1759053 baseEnd_1759053 := by
    simpa [prefixWord, tailWord_1759053, baseEnd_1759053] using wordTrace_append hprefix tailTrace_1759053
  have hstable : (prefixWord ++ tailWord_1759053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759053).length < 2 ^ (prefixWord ++ tailWord_1759053).sum := by decide
  have hdescent : baseEnd_1759053 < baseStart_1759053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759099 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 5, 2, 2]
def baseStart_1759099 : Nat := 118140960795 + 1759099 * 2 ^ 59
def prefixEnd_1759099 : Nat := 4983230072969 + 3 ^ 40 * 1759099 * 2
def baseEnd_1759099 : Nat := 903263305843518250772557

theorem tailTrace_1759099 : CollatzResearch.WordTrace tailWord_1759099 prefixEnd_1759099 903263305843518250772557 := by
  unfold tailWord_1759099
  simp only [CollatzResearch.WordTrace]
  refine ⟨64159611454092228035840351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42773074302728152023893567 64159611454092228035840351)
  ·
    refine ⟨96239417181138342053760527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64159611454092228035840351 96239417181138342053760527)
    ·
      refine ⟨144359125771707513080640791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96239417181138342053760527 144359125771707513080640791)
      ·
        refine ⟨216538688657561269620961187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144359125771707513080640791 216538688657561269620961187)
        ·
          refine ⟨324808032986341904431441781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216538688657561269620961187 324808032986341904431441781)
          ·
            refine ⟨30450753092469553540447667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 324808032986341904431441781 30450753092469553540447667)
            ·
              refine ⟨45676129638704330310671501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30450753092469553540447667 45676129638704330310671501)
              ·
                refine ⟨17128548614514123866501813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45676129638704330310671501 17128548614514123866501813)
                ·
                  refine ⟨1605801432610699112484545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17128548614514123866501813 1605801432610699112484545)
                  ·
                    refine ⟨1204351074458024334363409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1605801432610699112484545 1204351074458024334363409)
                    ·
                      refine ⟨903263305843518250772557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1204351074458024334363409 903263305843518250772557)
                      ·
                        rfl

theorem cell23_1759099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5, 2, 2].length) (baseStart_1759099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759099 prefixEnd_1759099 := by exact prefixLift 1759099
  have htrace : WordTrace (prefixWord ++ tailWord_1759099) baseStart_1759099 baseEnd_1759099 := by
    simpa [prefixWord, tailWord_1759099, baseEnd_1759099] using wordTrace_append hprefix tailTrace_1759099
  have hstable : (prefixWord ++ tailWord_1759099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759099).length < 2 ^ (prefixWord ++ tailWord_1759099).sum := by decide
  have hdescent : baseEnd_1759099 < baseStart_1759099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759122 : List Nat := [3, 2, 3, 2, 1, 12]
def baseStart_1759122 : Nat := 118140960795 + 1759122 * 2 ^ 59
def prefixEnd_1759122 : Nat := 4983230072969 + 3 ^ 40 * 1759122 * 2
def baseEnd_1759122 : Nat := 3717181546907702307757

theorem tailTrace_1759122 : CollatzResearch.WordTrace tailWord_1759122 prefixEnd_1759122 3717181546907702307757 := by
  unfold tailWord_1759122
  simp only [CollatzResearch.WordTrace]
  refine ⟨16040112583252225740981905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42773633555339268642618413 16040112583252225740981905)
  ·
    refine ⟨12030084437439169305736429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16040112583252225740981905 12030084437439169305736429)
    ·
      refine ⟨4511281664039688489651161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12030084437439169305736429 4511281664039688489651161)
      ·
        refine ⟨3383461248029766367238371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4511281664039688489651161 3383461248029766367238371)
        ·
          refine ⟨5075191872044649550857557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3383461248029766367238371 5075191872044649550857557)
          ·
            refine ⟨3717181546907702307757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 5075191872044649550857557 3717181546907702307757)
            ·
              rfl

theorem cell23_1759122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 12].length) (baseStart_1759122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759122 prefixEnd_1759122 := by exact prefixLift 1759122
  have htrace : WordTrace (prefixWord ++ tailWord_1759122) baseStart_1759122 baseEnd_1759122 := by
    simpa [prefixWord, tailWord_1759122, baseEnd_1759122] using wordTrace_append hprefix tailTrace_1759122
  have hstable : (prefixWord ++ tailWord_1759122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759122).length < 2 ^ (prefixWord ++ tailWord_1759122).sum := by decide
  have hdescent : baseEnd_1759122 < baseStart_1759122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759182 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 4, 6]
def baseStart_1759182 : Nat := 118140960795 + 1759182 * 2 ^ 59
def prefixEnd_1759182 : Nat := 4983230072969 + 3 ^ 40 * 1759182 * 2
def baseEnd_1759182 : Nat := 301101974912613808678225

theorem tailTrace_1759182 : CollatzResearch.WordTrace tailWord_1759182 prefixEnd_1759182 301101974912613808678225 := by
  unfold tailWord_1759182
  simp only [CollatzResearch.WordTrace]
  refine ⟨8020329839098941651388975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42775092475194355474074533 8020329839098941651388975)
  ·
    refine ⟨12030494758648412477083463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8020329839098941651388975 12030494758648412477083463)
    ·
      refine ⟨18045742137972618715625195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12030494758648412477083463 18045742137972618715625195)
      ·
        refine ⟨27068613206958928073437793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18045742137972618715625195 27068613206958928073437793)
        ·
          refine ⟨20301459905219196055078345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27068613206958928073437793 20301459905219196055078345)
          ·
            refine ⟨15226094928914397041308759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20301459905219196055078345 15226094928914397041308759)
            ·
              refine ⟨22839142393371595561963139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15226094928914397041308759 22839142393371595561963139)
              ·
                refine ⟨34258713590057393342944709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22839142393371595561963139 34258713590057393342944709)
                ·
                  refine ⟨6423508798135761251802133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34258713590057393342944709 6423508798135761251802133)
                  ·
                    refine ⟨301101974912613808678225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6423508798135761251802133 301101974912613808678225)
                    ·
                      rfl

theorem cell23_1759182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_1759182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759182 prefixEnd_1759182 := by exact prefixLift 1759182
  have htrace : WordTrace (prefixWord ++ tailWord_1759182) baseStart_1759182 baseEnd_1759182 := by
    simpa [prefixWord, tailWord_1759182, baseEnd_1759182] using wordTrace_append hprefix tailTrace_1759182
  have hstable : (prefixWord ++ tailWord_1759182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759182).length < 2 ^ (prefixWord ++ tailWord_1759182).sum := by decide
  have hdescent : baseEnd_1759182 < baseStart_1759182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759279 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 3, 6, 2]
def baseStart_1759279 : Nat := 118140960795 + 1759279 * 2 ^ 59
def prefixEnd_1759279 : Nat := 4983230072969 + 3 ^ 40 * 1759279 * 2
def baseEnd_1759279 : Nat := 903355732361327546521729

theorem tailTrace_1759279 : CollatzResearch.WordTrace tailWord_1759279 prefixEnd_1759279 903355732361327546521729 := by
  unfold tailWord_1759279
  simp only [CollatzResearch.WordTrace]
  refine ⟨64166176593440118777392891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42777451062293412518261927 64166176593440118777392891)
  ·
    refine ⟨96249264890160178166089337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64166176593440118777392891 96249264890160178166089337)
    ·
      refine ⟨72186948667620133624567003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96249264890160178166089337 72186948667620133624567003)
      ·
        refine ⟨108280423001430200436850505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72186948667620133624567003 108280423001430200436850505)
        ·
          refine ⟨81210317251072650327637879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108280423001430200436850505 81210317251072650327637879)
          ·
            refine ⟨121815475876608975491456819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81210317251072650327637879 121815475876608975491456819)
            ·
              refine ⟨182723213814913463237185229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121815475876608975491456819 182723213814913463237185229)
              ·
                refine ⟨68521205180592548713944461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182723213814913463237185229 68521205180592548713944461)
                ·
                  refine ⟨25695451942722205767729173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68521205180592548713944461 25695451942722205767729173)
                  ·
                    refine ⟨1204474309815103395362305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25695451942722205767729173 1204474309815103395362305)
                    ·
                      refine ⟨903355732361327546521729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1204474309815103395362305 903355732361327546521729)
                      ·
                        rfl

theorem cell23_1759279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 6, 2].length) (baseStart_1759279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759279 prefixEnd_1759279 := by exact prefixLift 1759279
  have htrace : WordTrace (prefixWord ++ tailWord_1759279) baseStart_1759279 baseEnd_1759279 := by
    simpa [prefixWord, tailWord_1759279, baseEnd_1759279] using wordTrace_append hprefix tailTrace_1759279
  have hstable : (prefixWord ++ tailWord_1759279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759279).length < 2 ^ (prefixWord ++ tailWord_1759279).sum := by decide
  have hdescent : baseEnd_1759279 < baseStart_1759279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759299 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 4, 2, 3]
def baseStart_1759299 : Nat := 118140960795 + 1759299 * 2 ^ 59
def prefixEnd_1759299 : Nat := 4983230072969 + 3 ^ 40 * 1759299 * 2
def baseEnd_1759299 : Nat := 903366001974417468271637

theorem tailTrace_1759299 : CollatzResearch.WordTrace tailWord_1759299 prefixEnd_1759299 903366001974417468271637 := by
  unfold tailWord_1759299
  simp only [CollatzResearch.WordTrace]
  refine ⟨64166906053367662193120951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42777937368911774795413967 64166906053367662193120951)
  ·
    refine ⟨96250359080051493289681427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64166906053367662193120951 96250359080051493289681427)
    ·
      refine ⟨144375538620077239934522141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96250359080051493289681427 144375538620077239934522141)
      ·
        refine ⟨54140826982528964975445803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144375538620077239934522141 54140826982528964975445803)
        ·
          refine ⟨81211240473793447463168705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54140826982528964975445803 81211240473793447463168705)
          ·
            refine ⟨60908430355345085597376529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81211240473793447463168705 60908430355345085597376529)
            ·
              refine ⟨45681322766508814198032397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60908430355345085597376529 45681322766508814198032397)
              ·
                refine ⟨17130496037440805324262149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45681322766508814198032397 17130496037440805324262149)
                ·
                  refine ⟨3211968007020150998299153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17130496037440805324262149 3211968007020150998299153)
                  ·
                    refine ⟨2408976005265113248724365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3211968007020150998299153 2408976005265113248724365)
                    ·
                      refine ⟨903366001974417468271637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2408976005265113248724365 903366001974417468271637)
                      ·
                        rfl

theorem cell23_1759299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2, 3].length) (baseStart_1759299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759299 prefixEnd_1759299 := by exact prefixLift 1759299
  have htrace : WordTrace (prefixWord ++ tailWord_1759299) baseStart_1759299 baseEnd_1759299 := by
    simpa [prefixWord, tailWord_1759299, baseEnd_1759299] using wordTrace_append hprefix tailTrace_1759299
  have hstable : (prefixWord ++ tailWord_1759299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759299).length < 2 ^ (prefixWord ++ tailWord_1759299).sum := by decide
  have hdescent : baseEnd_1759299 < baseStart_1759299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759319 : List Nat := [1, 1, 3, 2, 2, 1, 4, 3, 6]
def baseStart_1759319 : Nat := 118140960795 + 1759319 * 2 ^ 59
def prefixEnd_1759319 : Nat := 4983230072969 + 3 ^ 40 * 1759319 * 2
def baseEnd_1759319 : Nat := 100375141287500821113505

theorem tailTrace_1759319 : CollatzResearch.WordTrace tailWord_1759319 prefixEnd_1759319 100375141287500821113505 := by
  unfold tailWord_1759319
  simp only [CollatzResearch.WordTrace]
  refine ⟨64167635513295205608849011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42778423675530137072566007 64167635513295205608849011)
  ·
    refine ⟨96251453269942808413273517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64167635513295205608849011 96251453269942808413273517)
    ·
      refine ⟨36094294976228553154977569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96251453269942808413273517 36094294976228553154977569)
      ·
        refine ⟨27070721232171414866233177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36094294976228553154977569 27070721232171414866233177)
        ·
          refine ⟨20303040924128561149674883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27070721232171414866233177 20303040924128561149674883)
          ·
            refine ⟨30454561386192841724512325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20303040924128561149674883 30454561386192841724512325)
            ·
              refine ⟨5710230259911157823346061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30454561386192841724512325 5710230259911157823346061)
              ·
                refine ⟨2141336347466684183754773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5710230259911157823346061 2141336347466684183754773)
                ·
                  refine ⟨100375141287500821113505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2141336347466684183754773 100375141287500821113505)
                  ·
                    rfl

theorem cell23_1759319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 6].length) (baseStart_1759319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759319 prefixEnd_1759319 := by exact prefixLift 1759319
  have htrace : WordTrace (prefixWord ++ tailWord_1759319) baseStart_1759319 baseEnd_1759319 := by
    simpa [prefixWord, tailWord_1759319, baseEnd_1759319] using wordTrace_append hprefix tailTrace_1759319
  have hstable : (prefixWord ++ tailWord_1759319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759319).length < 2 ^ (prefixWord ++ tailWord_1759319).sum := by decide
  have hdescent : baseEnd_1759319 < baseStart_1759319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759330 : List Nat := [3, 3, 2, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_1759330 : Nat := 118140960795 + 1759330 * 2 ^ 59
def prefixEnd_1759330 : Nat := 4983230072969 + 3 ^ 40 * 1759330 * 2
def baseEnd_1759330 : Nat := 903381919874706846983995

theorem tailTrace_1759330 : CollatzResearch.WordTrace tailWord_1759330 prefixEnd_1759330 903381919874706846983995 := by
  unfold tailWord_1759330
  simp only [CollatzResearch.WordTrace]
  refine ⟨16042009179063838621874861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42778691144170236324999629 16042009179063838621874861)
  ·
    refine ⟨6015753442148939483203073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16042009179063838621874861 6015753442148939483203073)
    ·
      refine ⟨4511815081611704612402305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6015753442148939483203073 4511815081611704612402305)
      ·
        refine ⟨3383861311208778459301729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4511815081611704612402305 3383861311208778459301729)
        ·
          refine ⟨2537895983406583844476297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3383861311208778459301729 2537895983406583844476297)
          ·
            refine ⟨1903421987554937883357223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2537895983406583844476297 1903421987554937883357223)
            ·
              refine ⟨2855132981332406825035835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1903421987554937883357223 2855132981332406825035835)
              ·
                refine ⟨4282699471998610237553753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2855132981332406825035835 4282699471998610237553753)
                ·
                  refine ⟨3212024603998957678165315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4282699471998610237553753 3212024603998957678165315)
                  ·
                    refine ⟨4818036905998436517247973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3212024603998957678165315 4818036905998436517247973)
                    ·
                      refine ⟨903381919874706846983995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4818036905998436517247973 903381919874706846983995)
                      ·
                        rfl

theorem cell23_1759330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_1759330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759330 prefixEnd_1759330 := by exact prefixLift 1759330
  have htrace : WordTrace (prefixWord ++ tailWord_1759330) baseStart_1759330 baseEnd_1759330 := by
    simpa [prefixWord, tailWord_1759330, baseEnd_1759330] using wordTrace_append hprefix tailTrace_1759330
  have hstable : (prefixWord ++ tailWord_1759330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759330).length < 2 ^ (prefixWord ++ tailWord_1759330).sum := by decide
  have hdescent : baseEnd_1759330 < baseStart_1759330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759333 : List Nat := [1, 3, 1, 3, 2, 4, 1, 1, 2, 2, 3]
def baseStart_1759333 : Nat := 118140960795 + 1759333 * 2 ^ 59
def prefixEnd_1759333 : Nat := 4983230072969 + 3 ^ 40 * 1759333 * 2
def baseEnd_1759333 : Nat := 903383460316670335246481

theorem tailTrace_1759333 : CollatzResearch.WordTrace tailWord_1759333 prefixEnd_1759333 903383460316670335246481 := by
  unfold tailWord_1759333
  simp only [CollatzResearch.WordTrace]
  refine ⟨64168146135244485999858653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42778764090162990666572435 64168146135244485999858653)
  ·
    refine ⟨24063054800716682249946995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64168146135244485999858653 24063054800716682249946995)
    ·
      refine ⟨36094582201075023374920493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24063054800716682249946995 36094582201075023374920493)
      ·
        refine ⟨13535468325403133765595185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36094582201075023374920493 13535468325403133765595185)
        ·
          refine ⟨10151601244052350324196389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13535468325403133765595185 10151601244052350324196389)
          ·
            refine ⟨1903425233259815685786823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10151601244052350324196389 1903425233259815685786823)
            ·
              refine ⟨2855137849889723528680235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1903425233259815685786823 2855137849889723528680235)
              ·
                refine ⟨4282706774834585293020353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2855137849889723528680235 4282706774834585293020353)
                ·
                  refine ⟨3212030081125938969765265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4282706774834585293020353 3212030081125938969765265)
                  ·
                    refine ⟨2409022560844454227323949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3212030081125938969765265 2409022560844454227323949)
                    ·
                      refine ⟨903383460316670335246481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2409022560844454227323949 903383460316670335246481)
                      ·
                        rfl

theorem cell23_1759333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_1759333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759333 prefixEnd_1759333 := by exact prefixLift 1759333
  have htrace : WordTrace (prefixWord ++ tailWord_1759333) baseStart_1759333 baseEnd_1759333 := by
    simpa [prefixWord, tailWord_1759333, baseEnd_1759333] using wordTrace_append hprefix tailTrace_1759333
  have hstable : (prefixWord ++ tailWord_1759333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759333).length < 2 ^ (prefixWord ++ tailWord_1759333).sum := by decide
  have hdescent : baseEnd_1759333 < baseStart_1759333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759363 : List Nat := [1, 1, 1, 3, 3, 4, 2, 1, 3, 1, 3]
def baseStart_1759363 : Nat := 118140960795 + 1759363 * 2 ^ 59
def prefixEnd_1759363 : Nat := 4983230072969 + 3 ^ 40 * 1759363 * 2
def baseEnd_1759363 : Nat := 903398864736305217871343

theorem tailTrace_1759363 : CollatzResearch.WordTrace tailWord_1759363 prefixEnd_1759363 903398864736305217871343 := by
  unfold tailWord_1759363
  simp only [CollatzResearch.WordTrace]
  refine ⟨64169240325135801123450743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42779493550090534082300495 64169240325135801123450743)
  ·
    refine ⟨96253860487703701685176115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64169240325135801123450743 96253860487703701685176115)
    ·
      refine ⟨144380790731555552527764173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96253860487703701685176115 144380790731555552527764173)
      ·
        refine ⟨54142796524333332197911565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144380790731555552527764173 54142796524333332197911565)
        ·
          refine ⟨20303548696624999574216837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54142796524333332197911565 20303548696624999574216837)
          ·
            refine ⟨3806915380617187420165657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20303548696624999574216837 3806915380617187420165657)
            ·
              refine ⟨2855186535462890565124243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3806915380617187420165657 2855186535462890565124243)
              ·
                refine ⟨4282779803194335847686365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2855186535462890565124243 4282779803194335847686365)
                ·
                  refine ⟨1606042426197875942882387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4282779803194335847686365 1606042426197875942882387)
                  ·
                    refine ⟨2409063639296813914323581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1606042426197875942882387 2409063639296813914323581)
                    ·
                      refine ⟨903398864736305217871343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2409063639296813914323581 903398864736305217871343)
                      ·
                        rfl

theorem cell23_1759363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3, 1, 3].length) (baseStart_1759363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759363 prefixEnd_1759363 := by exact prefixLift 1759363
  have htrace : WordTrace (prefixWord ++ tailWord_1759363) baseStart_1759363 baseEnd_1759363 := by
    simpa [prefixWord, tailWord_1759363, baseEnd_1759363] using wordTrace_append hprefix tailTrace_1759363
  have hstable : (prefixWord ++ tailWord_1759363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759363).length < 2 ^ (prefixWord ++ tailWord_1759363).sum := by decide
  have hdescent : baseEnd_1759363 < baseStart_1759363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759383 : List Nat := [1, 1, 3, 3, 4, 1, 2, 2, 1, 5]
def baseStart_1759383 : Nat := 118140960795 + 1759383 * 2 ^ 59
def prefixEnd_1759383 : Nat := 4983230072969 + 3 ^ 40 * 1759383 * 2
def baseEnd_1759383 : Nat := 301136378116465046540417

theorem tailTrace_1759383 : CollatzResearch.WordTrace tailWord_1759383 prefixEnd_1759383 301136378116465046540417 := by
  unfold tailWord_1759383
  simp only [CollatzResearch.WordTrace]
  refine ⟨64169969785063344539178803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42779979856708896359452535 64169969785063344539178803)
  ·
    refine ⟨96254954677595016808768205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64169969785063344539178803 96254954677595016808768205)
    ·
      refine ⟨36095608004098131303288077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96254954677595016808768205 36095608004098131303288077)
      ·
        refine ⟨13535853001536799238733029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36095608004098131303288077 13535853001536799238733029)
        ·
          refine ⟨2537972437788149857262443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13535853001536799238733029 2537972437788149857262443)
          ·
            refine ⟨3806958656682224785893665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2537972437788149857262443 3806958656682224785893665)
            ·
              refine ⟨2855218992511668589420249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3806958656682224785893665 2855218992511668589420249)
              ·
                refine ⟨2141414244383751442065187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2855218992511668589420249 2141414244383751442065187)
                ·
                  refine ⟨3212121366575627163097781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2141414244383751442065187 3212121366575627163097781)
                  ·
                    refine ⟨301136378116465046540417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3212121366575627163097781 301136378116465046540417)
                    ·
                      rfl

theorem cell23_1759383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 5].length) (baseStart_1759383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759383 prefixEnd_1759383 := by exact prefixLift 1759383
  have htrace : WordTrace (prefixWord ++ tailWord_1759383) baseStart_1759383 baseEnd_1759383 := by
    simpa [prefixWord, tailWord_1759383, baseEnd_1759383] using wordTrace_append hprefix tailTrace_1759383
  have hstable : (prefixWord ++ tailWord_1759383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759383).length < 2 ^ (prefixWord ++ tailWord_1759383).sum := by decide
  have hdescent : baseEnd_1759383 < baseStart_1759383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759449 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 1, 4, 5]
def baseStart_1759449 : Nat := 118140960795 + 1759449 * 2 ^ 59
def prefixEnd_1759449 : Nat := 4983230072969 + 3 ^ 40 * 1759449 * 2
def baseEnd_1759449 : Nat := 903443024072591881395947

theorem tailTrace_1759449 : CollatzResearch.WordTrace tailWord_1759449 prefixEnd_1759449 903443024072591881395947 := by
  unfold tailWord_1759449
  simp only [CollatzResearch.WordTrace]
  refine ⟨64172377002824237811081401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42781584668549491874054267 64172377002824237811081401)
  ·
    refine ⟨48129282752118178358311051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64172377002824237811081401 48129282752118178358311051)
    ·
      refine ⟨72193924128177267537466577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48129282752118178358311051 72193924128177267537466577)
      ·
        refine ⟨54145443096132950653099933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72193924128177267537466577 54145443096132950653099933)
        ·
          refine ⟨20304541161049856494912475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54145443096132950653099933 20304541161049856494912475)
          ·
            refine ⟨30456811741574784742368713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20304541161049856494912475 30456811741574784742368713)
            ·
              refine ⟨22842608806181088556776535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30456811741574784742368713 22842608806181088556776535)
              ·
                refine ⟨34263913209271632835164803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22842608806181088556776535 34263913209271632835164803)
                ·
                  refine ⟨51395869813907449252747205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34263913209271632835164803 51395869813907449252747205)
                  ·
                    refine ⟨9636725590107646734890101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51395869813907449252747205 9636725590107646734890101)
                    ·
                      refine ⟨903443024072591881395947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9636725590107646734890101 903443024072591881395947)
                      ·
                        rfl

theorem cell23_1759449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_1759449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759449 prefixEnd_1759449 := by exact prefixLift 1759449
  have htrace : WordTrace (prefixWord ++ tailWord_1759449) baseStart_1759449 baseEnd_1759449 := by
    simpa [prefixWord, tailWord_1759449, baseEnd_1759449] using wordTrace_append hprefix tailTrace_1759449
  have hstable : (prefixWord ++ tailWord_1759449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759449).length < 2 ^ (prefixWord ++ tailWord_1759449).sum := by decide
  have hdescent : baseEnd_1759449 < baseStart_1759449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759453 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_1759453 : Nat := 118140960795 + 1759453 * 2 ^ 59
def prefixEnd_1759453 : Nat := 4983230072969 + 3 ^ 40 * 1759453 * 2
def baseEnd_1759453 : Nat := 903445077995209865745929

theorem tailTrace_1759453 : CollatzResearch.WordTrace tailWord_1759453 prefixEnd_1759453 903445077995209865745929 := by
  unfold tailWord_1759453
  simp only [CollatzResearch.WordTrace]
  refine ⟨64172522894809746494227013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42781681929873164329484675 64172522894809746494227013)
  ·
    refine ⟨12032348042776827467667565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64172522894809746494227013 12032348042776827467667565)
    ·
      refine ⟨4512130516041310300375337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12032348042776827467667565 4512130516041310300375337)
      ·
        refine ⟨3384097887030982725281503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4512130516041310300375337 3384097887030982725281503)
        ·
          refine ⟨5076146830546474087922255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3384097887030982725281503 5076146830546474087922255)
          ·
            refine ⟨7614220245819711131883383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5076146830546474087922255 7614220245819711131883383)
            ·
              refine ⟨11421330368729566697825075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7614220245819711131883383 11421330368729566697825075)
              ·
                refine ⟨17131995553094350046737613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11421330368729566697825075 17131995553094350046737613)
                ·
                  refine ⟨6424498332410381267526605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17131995553094350046737613 6424498332410381267526605)
                  ·
                    refine ⟨2409186874653892975322477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6424498332410381267526605 2409186874653892975322477)
                    ·
                      refine ⟨903445077995209865745929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2409186874653892975322477 903445077995209865745929)
                      ·
                        rfl

theorem cell23_1759453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_1759453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759453 prefixEnd_1759453 := by exact prefixLift 1759453
  have htrace : WordTrace (prefixWord ++ tailWord_1759453) baseStart_1759453 baseEnd_1759453 := by
    simpa [prefixWord, tailWord_1759453, baseEnd_1759453] using wordTrace_append hprefix tailTrace_1759453
  have hstable : (prefixWord ++ tailWord_1759453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759453).length < 2 ^ (prefixWord ++ tailWord_1759453).sum := by decide
  have hdescent : baseEnd_1759453 < baseStart_1759453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759514 : List Nat := [3, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2]
def baseStart_1759514 : Nat := 118140960795 + 1759514 * 2 ^ 59
def prefixEnd_1759514 : Nat := 4983230072969 + 3 ^ 40 * 1759514 * 2
def baseEnd_1759514 : Nat := 903476400315134127083149

theorem tailTrace_1759514 : CollatzResearch.WordTrace tailWord_1759514 prefixEnd_1759514 903476400315134127083149 := by
  unfold tailWord_1759514
  simp only [CollatzResearch.WordTrace]
  refine ⟨16043686936897188478049399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42783165165059169274798397 16043686936897188478049399)
  ·
    refine ⟨24065530405345782717074099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16043686936897188478049399 24065530405345782717074099)
    ·
      refine ⟨36098295608018674075611149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24065530405345782717074099 36098295608018674075611149)
      ·
        refine ⟨13536860853007002778354181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36098295608018674075611149 13536860853007002778354181)
        ·
          refine ⟨2538161409938813020941409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13536860853007002778354181 2538161409938813020941409)
          ·
            refine ⟨1903621057454109765706057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2538161409938813020941409 1903621057454109765706057)
            ·
              refine ⟨1427715793090582324279543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1903621057454109765706057 1427715793090582324279543)
              ·
                refine ⟨2141573689635873486419315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1427715793090582324279543 2141573689635873486419315)
                ·
                  refine ⟨3212360534453810229628973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2141573689635873486419315 3212360534453810229628973)
                  ·
                    refine ⟨1204635200420178836110865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3212360534453810229628973 1204635200420178836110865)
                    ·
                      refine ⟨903476400315134127083149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1204635200420178836110865 903476400315134127083149)
                      ·
                        rfl

theorem cell23_1759514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_1759514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759514 prefixEnd_1759514 := by exact prefixLift 1759514
  have htrace : WordTrace (prefixWord ++ tailWord_1759514) baseStart_1759514 baseEnd_1759514 := by
    simpa [prefixWord, tailWord_1759514, baseEnd_1759514] using wordTrace_append hprefix tailTrace_1759514
  have hstable : (prefixWord ++ tailWord_1759514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759514).length < 2 ^ (prefixWord ++ tailWord_1759514).sum := by decide
  have hdescent : baseEnd_1759514 < baseStart_1759514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759546 : List Nat := [3, 1, 1, 1, 4, 2, 1, 2, 1, 7]
def baseStart_1759546 : Nat := 118140960795 + 1759546 * 2 ^ 59
def prefixEnd_1759546 : Nat := 4983230072969 + 3 ^ 40 * 1759546 * 2
def baseEnd_1759546 : Nat := 301164277232026000627667

theorem tailTrace_1759546 : CollatzResearch.WordTrace tailWord_1759546 prefixEnd_1759546 301164277232026000627667 := by
  unfold tailWord_1759546
  simp only [CollatzResearch.WordTrace]
  refine ⟨16043978720868205844340623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42783943255648548918241661 16043978720868205844340623)
  ·
    refine ⟨24065968081302308766510935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16043978720868205844340623 24065968081302308766510935)
    ·
      refine ⟨36098952121953463149766403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24065968081302308766510935 36098952121953463149766403)
      ·
        refine ⟨54148428182930194724649605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36098952121953463149766403 54148428182930194724649605)
        ·
          refine ⟨10152830284299411510871801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54148428182930194724649605 10152830284299411510871801)
          ·
            refine ⟨7614622713224558633153851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10152830284299411510871801 7614622713224558633153851)
            ·
              refine ⟨11421934069836837949730777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7614622713224558633153851 11421934069836837949730777)
              ·
                refine ⟨8566450552377628462298083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11421934069836837949730777 8566450552377628462298083)
                ·
                  refine ⟨12849675828566442693447125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8566450552377628462298083 12849675828566442693447125)
                  ·
                    refine ⟨301164277232026000627667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12849675828566442693447125 301164277232026000627667)
                    ·
                      rfl

theorem cell23_1759546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 1, 7].length) (baseStart_1759546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759546 prefixEnd_1759546 := by exact prefixLift 1759546
  have htrace : WordTrace (prefixWord ++ tailWord_1759546) baseStart_1759546 baseEnd_1759546 := by
    simpa [prefixWord, tailWord_1759546, baseEnd_1759546] using wordTrace_append hprefix tailTrace_1759546
  have hstable : (prefixWord ++ tailWord_1759546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759546).length < 2 ^ (prefixWord ++ tailWord_1759546).sum := by decide
  have hdescent : baseEnd_1759546 < baseStart_1759546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759583 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 4, 4, 2]
def baseStart_1759583 : Nat := 118140960795 + 1759583 * 2 ^ 59
def prefixEnd_1759583 : Nat := 4983230072969 + 3 ^ 40 * 1759583 * 2
def baseEnd_1759583 : Nat := 903511830480294357120331

theorem tailTrace_1759583 : CollatzResearch.WordTrace tailWord_1759583 prefixEnd_1759583 903511830480294357120331 := by
  unfold tailWord_1759583
  simp only [CollatzResearch.WordTrace]
  refine ⟨64177264384338778696459403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42784842922892519130972935 64177264384338778696459403)
  ·
    refine ⟨96265896576508168044689105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64177264384338778696459403 96265896576508168044689105)
    ·
      refine ⟨72199422432381126033516829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96265896576508168044689105 72199422432381126033516829)
      ·
        refine ⟨27074783412142922262568811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72199422432381126033516829 27074783412142922262568811)
        ·
          refine ⟨40612175118214383393853217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27074783412142922262568811 40612175118214383393853217)
          ·
            refine ⟨30459131338660787545389913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40612175118214383393853217 30459131338660787545389913)
            ·
              refine ⟨22844348503995590659042435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30459131338660787545389913 22844348503995590659042435)
              ·
                refine ⟨34266522755993385988563653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22844348503995590659042435 34266522755993385988563653)
                ·
                  refine ⟨6424973016748759872855685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34266522755993385988563653 6424973016748759872855685)
                  ·
                    refine ⟨1204682440640392476160441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6424973016748759872855685 1204682440640392476160441)
                    ·
                      refine ⟨903511830480294357120331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1204682440640392476160441 903511830480294357120331)
                      ·
                        rfl

theorem cell23_1759583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 4, 2].length) (baseStart_1759583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759583 prefixEnd_1759583 := by exact prefixLift 1759583
  have htrace : WordTrace (prefixWord ++ tailWord_1759583) baseStart_1759583 baseEnd_1759583 := by
    simpa [prefixWord, tailWord_1759583, baseEnd_1759583] using wordTrace_append hprefix tailTrace_1759583
  have hstable : (prefixWord ++ tailWord_1759583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759583).length < 2 ^ (prefixWord ++ tailWord_1759583).sum := by decide
  have hdescent : baseEnd_1759583 < baseStart_1759583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759620 : List Nat := [2, 3, 2, 1, 1, 2, 4, 1, 2, 2, 3]
def baseStart_1759620 : Nat := 118140960795 + 1759620 * 2 ^ 59
def prefixEnd_1759620 : Nat := 4983230072969 + 3 ^ 40 * 1759620 * 2
def baseEnd_1759620 : Nat := 903530829264510712357661

theorem tailTrace_1759620 : CollatzResearch.WordTrace tailWord_1759620 prefixEnd_1759620 903530829264510712357661 := by
  unfold tailWord_1759620
  simp only [CollatzResearch.WordTrace]
  refine ⟨32089306942602367007778157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42785742590136489343704209 32089306942602367007778157)
  ·
    refine ⟨12033490103475887627916809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32089306942602367007778157 12033490103475887627916809)
    ·
      refine ⟨9025117577606915720937607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12033490103475887627916809 9025117577606915720937607)
      ·
        refine ⟨13537676366410373581406411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9025117577606915720937607 13537676366410373581406411)
        ·
          refine ⟨20306514549615560372109617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13537676366410373581406411 20306514549615560372109617)
          ·
            refine ⟨15229885912211670279082213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20306514549615560372109617 15229885912211670279082213)
            ·
              refine ⟨2855603608539688177327915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15229885912211670279082213 2855603608539688177327915)
              ·
                refine ⟨4283405412809532265991873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2855603608539688177327915 4283405412809532265991873)
                ·
                  refine ⟨3212554059607149199493905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4283405412809532265991873 3212554059607149199493905)
                  ·
                    refine ⟨2409415544705361899620429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3212554059607149199493905 2409415544705361899620429)
                    ·
                      refine ⟨903530829264510712357661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2409415544705361899620429 903530829264510712357661)
                      ·
                        rfl

theorem cell23_1759620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_1759620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759620 prefixEnd_1759620 := by exact prefixLift 1759620
  have htrace : WordTrace (prefixWord ++ tailWord_1759620) baseStart_1759620 baseEnd_1759620 := by
    simpa [prefixWord, tailWord_1759620, baseEnd_1759620] using wordTrace_append hprefix tailTrace_1759620
  have hstable : (prefixWord ++ tailWord_1759620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759620).length < 2 ^ (prefixWord ++ tailWord_1759620).sum := by decide
  have hdescent : baseEnd_1759620 < baseStart_1759620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759640 : List Nat := [2, 1, 2, 5, 1, 2, 2, 2, 6]
def baseStart_1759640 : Nat := 118140960795 + 1759640 * 2 ^ 59
def prefixEnd_1759640 : Nat := 4983230072969 + 3 ^ 40 * 1759640 * 2
def baseEnd_1759640 : Nat := 100393455430844514900841

theorem tailTrace_1759640 : CollatzResearch.WordTrace tailWord_1759640 prefixEnd_1759640 100393455430844514900841 := by
  unfold tailWord_1759640
  simp only [CollatzResearch.WordTrace]
  refine ⟨32089671672566138715642187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42786228896754851620856249 32089671672566138715642187)
  ·
    refine ⟨48134507508849208073463281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32089671672566138715642187 48134507508849208073463281)
    ·
      refine ⟨36100880631636906055097461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48134507508849208073463281 36100880631636906055097461)
      ·
        refine ⟨3384457559215959942665387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36100880631636906055097461 3384457559215959942665387)
        ·
          refine ⟨5076686338823939913998081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3384457559215959942665387 5076686338823939913998081)
          ·
            refine ⟨3807514754117954935498561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5076686338823939913998081 3807514754117954935498561)
            ·
              refine ⟨2855636065588466201623921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3807514754117954935498561 2855636065588466201623921)
              ·
                refine ⟨2141727049191349651217941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2855636065588466201623921 2141727049191349651217941)
                ·
                  refine ⟨100393455430844514900841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2141727049191349651217941 100393455430844514900841)
                  ·
                    rfl

theorem cell23_1759640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 6].length) (baseStart_1759640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759640 prefixEnd_1759640 := by exact prefixLift 1759640
  have htrace : WordTrace (prefixWord ++ tailWord_1759640) baseStart_1759640 baseEnd_1759640 := by
    simpa [prefixWord, tailWord_1759640, baseEnd_1759640] using wordTrace_append hprefix tailTrace_1759640
  have hstable : (prefixWord ++ tailWord_1759640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759640).length < 2 ^ (prefixWord ++ tailWord_1759640).sum := by decide
  have hdescent : baseEnd_1759640 < baseStart_1759640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759677 : List Nat := [1, 4, 1, 2, 2, 2, 3, 1, 2, 3, 2]
def baseStart_1759677 : Nat := 118140960795 + 1759677 * 2 ^ 59
def prefixEnd_1759677 : Nat := 4983230072969 + 3 ^ 40 * 1759677 * 2
def baseEnd_1759677 : Nat := 903560097661816989344899

theorem tailTrace_1759677 : CollatzResearch.WordTrace tailWord_1759677 prefixEnd_1759677 903560097661816989344899 := by
  unfold tailWord_1759677
  simp only [CollatzResearch.WordTrace]
  refine ⟨64180692845998232750381285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42787128563998821833587523 64180692845998232750381285)
  ·
    refine ⟨12033879908624668640696491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64180692845998232750381285 12033879908624668640696491)
    ·
      refine ⟨18050819862937002961044737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12033879908624668640696491 18050819862937002961044737)
      ·
        refine ⟨13538114897202752220783553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18050819862937002961044737 13538114897202752220783553)
        ·
          refine ⟨10153586172902064165587665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13538114897202752220783553 10153586172902064165587665)
          ·
            refine ⟨7615189629676548124190749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10153586172902064165587665 7615189629676548124190749)
            ·
              refine ⟨2855696111128705546571531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7615189629676548124190749 2855696111128705546571531)
              ·
                refine ⟨4283544166693058319857297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2855696111128705546571531 4283544166693058319857297)
                ·
                  refine ⟨3212658125019793739892973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4283544166693058319857297 3212658125019793739892973)
                  ·
                    refine ⟨1204746796882422652459865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3212658125019793739892973 1204746796882422652459865)
                    ·
                      refine ⟨903560097661816989344899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1204746796882422652459865 903560097661816989344899)
                      ·
                        rfl

theorem cell23_1759677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_1759677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759677 prefixEnd_1759677 := by exact prefixLift 1759677
  have htrace : WordTrace (prefixWord ++ tailWord_1759677) baseStart_1759677 baseEnd_1759677 := by
    simpa [prefixWord, tailWord_1759677, baseEnd_1759677] using wordTrace_append hprefix tailTrace_1759677
  have hstable : (prefixWord ++ tailWord_1759677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759677).length < 2 ^ (prefixWord ++ tailWord_1759677).sum := by decide
  have hdescent : baseEnd_1759677 < baseStart_1759677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759683 : List Nat := [1, 1, 1, 3, 1, 1, 3, 4, 4, 4]
def baseStart_1759683 : Nat := 118140960795 + 1759683 * 2 ^ 59
def prefixEnd_1759683 : Nat := 4983230072969 + 3 ^ 40 * 1759683 * 2
def baseEnd_1759683 : Nat := 301187726181914655289957

theorem tailTrace_1759683 : CollatzResearch.WordTrace tailWord_1759683 prefixEnd_1759683 301187726181914655289957 := by
  unfold tailWord_1759683
  simp only [CollatzResearch.WordTrace]
  refine ⟨64180911683976495775099703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42787274455984330516733135 64180911683976495775099703)
  ·
    refine ⟨96271367525964743662649555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64180911683976495775099703 96271367525964743662649555)
    ·
      refine ⟨144407051288947115493974333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96271367525964743662649555 144407051288947115493974333)
      ·
        refine ⟨54152644233355168310240375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144407051288947115493974333 54152644233355168310240375)
        ·
          refine ⟨81228966350032752465360563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54152644233355168310240375 81228966350032752465360563)
          ·
            refine ⟨121843449525049128698040845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81228966350032752465360563 121843449525049128698040845)
            ·
              refine ⟨45691293571893423261765317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121843449525049128698040845 45691293571893423261765317)
              ·
                refine ⟨8567117544730016861580997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45691293571893423261765317 8567117544730016861580997)
                ·
                  refine ⟨1606334539636878161546437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8567117544730016861580997 1606334539636878161546437)
                  ·
                    refine ⟨301187726181914655289957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1606334539636878161546437 301187726181914655289957)
                    ·
                      rfl

theorem cell23_1759683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4, 4].length) (baseStart_1759683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759683 prefixEnd_1759683 := by exact prefixLift 1759683
  have htrace : WordTrace (prefixWord ++ tailWord_1759683) baseStart_1759683 baseEnd_1759683 := by
    simpa [prefixWord, tailWord_1759683, baseEnd_1759683] using wordTrace_append hprefix tailTrace_1759683
  have hstable : (prefixWord ++ tailWord_1759683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759683).length < 2 ^ (prefixWord ++ tailWord_1759683).sum := by decide
  have hdescent : baseEnd_1759683 < baseStart_1759683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759687 : List Nat := [1, 1, 4, 1, 1, 6, 2, 1, 1, 5]
def baseStart_1759687 : Nat := 118140960795 + 1759687 * 2 ^ 59
def prefixEnd_1759687 : Nat := 4983230072969 + 3 ^ 40 * 1759687 * 2
def baseEnd_1759687 : Nat := 301188410822787316739951

theorem tailTrace_1759687 : CollatzResearch.WordTrace tailWord_1759687 prefixEnd_1759687 301188410822787316739951 := by
  unfold tailWord_1759687
  simp only [CollatzResearch.WordTrace]
  refine ⟨64181057575962004458245315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42787371717308002972163543 64181057575962004458245315)
  ·
    refine ⟨96271586363943006687367973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64181057575962004458245315 96271586363943006687367973)
    ·
      refine ⟨18050922443239313753881495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96271586363943006687367973 18050922443239313753881495)
      ·
        refine ⟨27076383664858970630822243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18050922443239313753881495 27076383664858970630822243)
        ·
          refine ⟨40614575497288455946233365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27076383664858970630822243 40614575497288455946233365)
          ·
            refine ⟨1903808226435396372479689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40614575497288455946233365 1903808226435396372479689)
            ·
              refine ⟨1427856169826547279359767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1903808226435396372479689 1427856169826547279359767)
              ·
                refine ⟨2141784254739820919039651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1427856169826547279359767 2141784254739820919039651)
                ·
                  refine ⟨3212676382109731378559477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2141784254739820919039651 3212676382109731378559477)
                  ·
                    refine ⟨301188410822787316739951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3212676382109731378559477 301188410822787316739951)
                    ·
                      rfl

theorem cell23_1759687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_1759687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759687 prefixEnd_1759687 := by exact prefixLift 1759687
  have htrace : WordTrace (prefixWord ++ tailWord_1759687) baseStart_1759687 baseEnd_1759687 := by
    simpa [prefixWord, tailWord_1759687, baseEnd_1759687] using wordTrace_append hprefix tailTrace_1759687
  have hstable : (prefixWord ++ tailWord_1759687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759687).length < 2 ^ (prefixWord ++ tailWord_1759687).sum := by decide
  have hdescent : baseEnd_1759687 < baseStart_1759687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759690 : List Nat := [3, 1, 2, 1, 2, 2, 3, 3, 1, 1, 4]
def baseStart_1759690 : Nat := 118140960795 + 1759690 * 2 ^ 59
def prefixEnd_1759690 : Nat := 4983230072969 + 3 ^ 40 * 1759690 * 2
def baseEnd_1759690 : Nat := 903566772910325438482339

theorem tailTrace_1759690 : CollatzResearch.WordTrace tailWord_1759690 prefixEnd_1759690 903566772910325438482339 := by
  unfold tailWord_1759690
  simp only [CollatzResearch.WordTrace]
  refine ⟨16045291748737783992651131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42787444663300757313736349 16045291748737783992651131)
  ·
    refine ⟨24067937623106675988976697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16045291748737783992651131 24067937623106675988976697)
    ·
      refine ⟨18050953217330006991732523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24067937623106675988976697 18050953217330006991732523)
      ·
        refine ⟨27076429825995010487598785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18050953217330006991732523 27076429825995010487598785)
        ·
          refine ⟨20307322369496257865699089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27076429825995010487598785 20307322369496257865699089)
          ·
            refine ⟨15230491777122193399274317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20307322369496257865699089 15230491777122193399274317)
            ·
              refine ⟨5711434416420822524727869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15230491777122193399274317 5711434416420822524727869)
              ·
                refine ⟨2141787906157808446772951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5711434416420822524727869 2141787906157808446772951)
                ·
                  refine ⟨3212681859236712670159427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2141787906157808446772951 3212681859236712670159427)
                  ·
                    refine ⟨4819022788855069005239141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3212681859236712670159427 4819022788855069005239141)
                    ·
                      refine ⟨903566772910325438482339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4819022788855069005239141 903566772910325438482339)
                      ·
                        rfl

theorem cell23_1759690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_1759690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759690 prefixEnd_1759690 := by exact prefixLift 1759690
  have htrace : WordTrace (prefixWord ++ tailWord_1759690) baseStart_1759690 baseEnd_1759690 := by
    simpa [prefixWord, tailWord_1759690, baseEnd_1759690] using wordTrace_append hprefix tailTrace_1759690
  have hstable : (prefixWord ++ tailWord_1759690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759690).length < 2 ^ (prefixWord ++ tailWord_1759690).sum := by decide
  have hdescent : baseEnd_1759690 < baseStart_1759690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759717 : List Nat := [1, 3, 1, 5, 2, 2, 1, 1, 1, 6]
def baseStart_1759717 : Nat := 118140960795 + 1759717 * 2 ^ 59
def prefixEnd_1759717 : Nat := 4983230072969 + 3 ^ 40 * 1759717 * 2
def baseEnd_1759717 : Nat := 301193545629332277614905

theorem tailTrace_1759717 : CollatzResearch.WordTrace tailWord_1759717 prefixEnd_1759717 301193545629332277614905 := by
  unfold tailWord_1759717
  simp only [CollatzResearch.WordTrace]
  refine ⟨64182151765853319581837405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42788101177235546387891603 64182151765853319581837405)
  ·
    refine ⟨24068306912194994843189027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64182151765853319581837405 24068306912194994843189027)
    ·
      refine ⟨36102460368292492264783541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24068306912194994843189027 36102460368292492264783541)
      ·
        refine ⟨3384605659527421149823457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36102460368292492264783541 3384605659527421149823457)
        ·
          refine ⟨2538454244645565862367593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3384605659527421149823457 2538454244645565862367593)
          ·
            refine ⟨1903840683484174396775695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2538454244645565862367593 1903840683484174396775695)
            ·
              refine ⟨2855761025226261595163543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1903840683484174396775695 2855761025226261595163543)
              ·
                refine ⟨4283641537839392392745315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2855761025226261595163543 4283641537839392392745315)
                ·
                  refine ⟨6425462306759088589117973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4283641537839392392745315 6425462306759088589117973)
                  ·
                    refine ⟨301193545629332277614905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6425462306759088589117973 301193545629332277614905)
                    ·
                      rfl

theorem cell23_1759717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 6].length) (baseStart_1759717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759717 prefixEnd_1759717 := by exact prefixLift 1759717
  have htrace : WordTrace (prefixWord ++ tailWord_1759717) baseStart_1759717 baseEnd_1759717 := by
    simpa [prefixWord, tailWord_1759717, baseEnd_1759717] using wordTrace_append hprefix tailTrace_1759717
  have hstable : (prefixWord ++ tailWord_1759717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759717).length < 2 ^ (prefixWord ++ tailWord_1759717).sum := by decide
  have hdescent : baseEnd_1759717 < baseStart_1759717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759720 : List Nat := [2, 1, 4, 1, 1, 3, 3, 1, 1, 2, 4]
def baseStart_1759720 : Nat := 118140960795 + 1759720 * 2 ^ 59
def prefixEnd_1759720 : Nat := 4983230072969 + 3 ^ 40 * 1759720 * 2
def baseEnd_1759720 : Nat := 903582177329960321107201

theorem tailTrace_1759720 : CollatzResearch.WordTrace tailWord_1759720 prefixEnd_1759720 903582177329960321107201 := by
  unfold tailWord_1759720
  simp only [CollatzResearch.WordTrace]
  refine ⟨32091130592421225547098307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42788174123228300729464409 32091130592421225547098307)
  ·
    refine ⟨48136695888631838320647461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32091130592421225547098307 48136695888631838320647461)
    ·
      refine ⟨9025630479118469685121399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48136695888631838320647461 9025630479118469685121399)
      ·
        refine ⟨13538445718677704527682099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9025630479118469685121399 13538445718677704527682099)
        ·
          refine ⟨20307668578016556791523149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13538445718677704527682099 20307668578016556791523149)
          ·
            refine ⟨7615375716756208796821181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20307668578016556791523149 7615375716756208796821181)
            ·
              refine ⟨2855765893783578298807943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7615375716756208796821181 2855765893783578298807943)
              ·
                refine ⟨4283648840675367448211915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2855765893783578298807943 4283648840675367448211915)
                ·
                  refine ⟨6425473261013051172317873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4283648840675367448211915 6425473261013051172317873)
                  ·
                    refine ⟨4819104945759788379238405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6425473261013051172317873 4819104945759788379238405)
                    ·
                      refine ⟨903582177329960321107201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4819104945759788379238405 903582177329960321107201)
                      ·
                        rfl

theorem cell23_1759720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_1759720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759720 prefixEnd_1759720 := by exact prefixLift 1759720
  have htrace : WordTrace (prefixWord ++ tailWord_1759720) baseStart_1759720 baseEnd_1759720 := by
    simpa [prefixWord, tailWord_1759720, baseEnd_1759720] using wordTrace_append hprefix tailTrace_1759720
  have hstable : (prefixWord ++ tailWord_1759720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759720).length < 2 ^ (prefixWord ++ tailWord_1759720).sum := by decide
  have hdescent : baseEnd_1759720 < baseStart_1759720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759730 : List Nat := [3, 2, 1, 4, 2, 1, 1, 9]
def baseStart_1759730 : Nat := 118140960795 + 1759730 * 2 ^ 59
def prefixEnd_1759730 : Nat := 4983230072969 + 3 ^ 40 * 1759730 * 2
def baseEnd_1759730 : Nat := 33466196745796491925265

theorem tailTrace_1759730 : CollatzResearch.WordTrace tailWord_1759730 prefixEnd_1759730 33466196745796491925265 := by
  unfold tailWord_1759730
  simp only [CollatzResearch.WordTrace]
  refine ⟨16045656478701555700515161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42788417276537481868040429 16045656478701555700515161)
  ·
    refine ⟨12034242359026166775386371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16045656478701555700515161 12034242359026166775386371)
    ·
      refine ⟨18051363538539250163079557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12034242359026166775386371 18051363538539250163079557)
      ·
        refine ⟨3384630663476109405577417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18051363538539250163079557 3384630663476109405577417)
        ·
          refine ⟨2538472997607082054183063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3384630663476109405577417 2538472997607082054183063)
          ·
            refine ⟨3807709496410623081274595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2538472997607082054183063 3807709496410623081274595)
            ·
              refine ⟨5711564244615934621911893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3807709496410623081274595 5711564244615934621911893)
              ·
                refine ⟨33466196745796491925265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5711564244615934621911893 33466196745796491925265)
                ·
                  rfl

theorem cell23_1759730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 9].length) (baseStart_1759730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759730 prefixEnd_1759730 := by exact prefixLift 1759730
  have htrace : WordTrace (prefixWord ++ tailWord_1759730) baseStart_1759730 baseEnd_1759730 := by
    simpa [prefixWord, tailWord_1759730, baseEnd_1759730] using wordTrace_append hprefix tailTrace_1759730
  have hstable : (prefixWord ++ tailWord_1759730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759730).length < 2 ^ (prefixWord ++ tailWord_1759730).sum := by decide
  have hdescent : baseEnd_1759730 < baseStart_1759730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759758 : List Nat := [4, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2]
def baseStart_1759758 : Nat := 118140960795 + 1759758 * 2 ^ 59
def prefixEnd_1759758 : Nat := 4983230072969 + 3 ^ 40 * 1759758 * 2
def baseEnd_1759758 : Nat := 903601689594831172432027

theorem tailTrace_1759758 : CollatzResearch.WordTrace tailWord_1759758 prefixEnd_1759758 903601689594831172432027 := by
  unfold tailWord_1759758
  simp only [CollatzResearch.WordTrace]
  refine ⟨8022955894838097948009991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42789098105803189056053285 8022955894838097948009991)
  ·
    refine ⟨12034433842257146922014987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8022955894838097948009991 12034433842257146922014987)
    ·
      refine ⟨18051650763385720383022481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12034433842257146922014987 18051650763385720383022481)
      ·
        refine ⟨13538738072539290287266861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18051650763385720383022481 13538738072539290287266861)
        ·
          refine ⟨5077026777202233857725073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13538738072539290287266861 5077026777202233857725073)
          ·
            refine ⟨3807770082901675393293805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5077026777202233857725073 3807770082901675393293805)
            ·
              refine ⟨1427913781088128272485177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3807770082901675393293805 1427913781088128272485177)
              ·
                refine ⟨1070935335816096204363883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1427913781088128272485177 1070935335816096204363883)
                ·
                  refine ⟨1606403003724144306545825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1070935335816096204363883 1606403003724144306545825)
                  ·
                    refine ⟨1204802252793108229909369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1606403003724144306545825 1204802252793108229909369)
                    ·
                      refine ⟨903601689594831172432027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1204802252793108229909369 903601689594831172432027)
                      ·
                        rfl

theorem cell23_1759758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_1759758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759758 prefixEnd_1759758 := by exact prefixLift 1759758
  have htrace : WordTrace (prefixWord ++ tailWord_1759758) baseStart_1759758 baseEnd_1759758 := by
    simpa [prefixWord, tailWord_1759758, baseEnd_1759758] using wordTrace_append hprefix tailTrace_1759758
  have hstable : (prefixWord ++ tailWord_1759758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759758).length < 2 ^ (prefixWord ++ tailWord_1759758).sum := by decide
  have hdescent : baseEnd_1759758 < baseStart_1759758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759763 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 4]
def baseStart_1759763 : Nat := 118140960795 + 1759763 * 2 ^ 59
def prefixEnd_1759763 : Nat := 4983230072969 + 3 ^ 40 * 1759763 * 2
def baseEnd_1759763 : Nat := 903604256998103652869503

theorem tailTrace_1759763 : CollatzResearch.WordTrace tailWord_1759763 prefixEnd_1759763 903604256998103652869503 := by
  unfold tailWord_1759763
  simp only [CollatzResearch.WordTrace]
  refine ⟨64183829523686669438011943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42789219682457779625341295 64183829523686669438011943)
  ·
    refine ⟨96275744285530004157017915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64183829523686669438011943 96275744285530004157017915)
    ·
      refine ⟨144413616428295006235526873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96275744285530004157017915 144413616428295006235526873)
      ·
        refine ⟨108310212321221254676645155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144413616428295006235526873 108310212321221254676645155)
        ·
          refine ⟨162465318481831882014967733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108310212321221254676645155 162465318481831882014967733)
          ·
            refine ⟨15231123607671738938903225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162465318481831882014967733 15231123607671738938903225)
            ·
              refine ⟨11423342705753804204177419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15231123607671738938903225 11423342705753804204177419)
              ·
                refine ⟨17135014058630706306266129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11423342705753804204177419 17135014058630706306266129)
                ·
                  refine ⟨12851260543973029729699597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17135014058630706306266129 12851260543973029729699597)
                  ·
                    refine ⟨4819222703989886148637349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12851260543973029729699597 4819222703989886148637349)
                    ·
                      refine ⟨903604256998103652869503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4819222703989886148637349 903604256998103652869503)
                      ·
                        rfl

theorem cell23_1759763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 4].length) (baseStart_1759763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759763 prefixEnd_1759763 := by exact prefixLift 1759763
  have htrace : WordTrace (prefixWord ++ tailWord_1759763) baseStart_1759763 baseEnd_1759763 := by
    simpa [prefixWord, tailWord_1759763, baseEnd_1759763] using wordTrace_append hprefix tailTrace_1759763
  have hstable : (prefixWord ++ tailWord_1759763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759763).length < 2 ^ (prefixWord ++ tailWord_1759763).sum := by decide
  have hdescent : baseEnd_1759763 < baseStart_1759763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759784 : List Nat := [2, 1, 5, 2, 1, 2, 1, 1, 3, 3, 2]
def baseStart_1759784 : Nat := 118140960795 + 1759784 * 2 ^ 59
def prefixEnd_1759784 : Nat := 4983230072969 + 3 ^ 40 * 1759784 * 2
def baseEnd_1759784 : Nat := 903615040091848070706907

theorem tailTrace_1759784 : CollatzResearch.WordTrace tailWord_1759784 prefixEnd_1759784 903615040091848070706907 := by
  unfold tailWord_1759784
  simp only [CollatzResearch.WordTrace]
  refine ⟨32092297728305295012263203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42789730304407060016350937 32092297728305295012263203)
  ·
    refine ⟨48138446592457942518394805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32092297728305295012263203 48138446592457942518394805)
    ·
      refine ⟨4512979368042932111099513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48138446592457942518394805 4512979368042932111099513)
      ·
        refine ⟨3384734526032199083324635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4512979368042932111099513 3384734526032199083324635)
        ·
          refine ⟨5077101789048298624986953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3384734526032199083324635 5077101789048298624986953)
          ·
            refine ⟨3807826341786223968740215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5077101789048298624986953 3807826341786223968740215)
            ·
              refine ⟨5711739512679335953110323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3807826341786223968740215 5711739512679335953110323)
              ·
                refine ⟨8567609269019003929665485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5711739512679335953110323 8567609269019003929665485)
                ·
                  refine ⟨3212853475882126473624557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8567609269019003929665485 3212853475882126473624557)
                  ·
                    refine ⟨1204820053455797427609209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3212853475882126473624557 1204820053455797427609209)
                    ·
                      refine ⟨903615040091848070706907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1204820053455797427609209 903615040091848070706907)
                      ·
                        rfl

theorem cell23_1759784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_1759784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759784 prefixEnd_1759784 := by exact prefixLift 1759784
  have htrace : WordTrace (prefixWord ++ tailWord_1759784) baseStart_1759784 baseEnd_1759784 := by
    simpa [prefixWord, tailWord_1759784, baseEnd_1759784] using wordTrace_append hprefix tailTrace_1759784
  have hstable : (prefixWord ++ tailWord_1759784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759784).length < 2 ^ (prefixWord ++ tailWord_1759784).sum := by decide
  have hdescent : baseEnd_1759784 < baseStart_1759784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759797 : List Nat := [1, 3, 3, 1, 1, 2, 3, 2, 1, 4, 2]
def baseStart_1759797 : Nat := 118140960795 + 1759797 * 2 ^ 59
def prefixEnd_1759797 : Nat := 4983230072969 + 3 ^ 40 * 1759797 * 2
def baseEnd_1759797 : Nat := 903621715340356519844347

theorem tailTrace_1759797 : CollatzResearch.WordTrace tailWord_1759797 prefixEnd_1759797 903621715340356519844347 := by
  unfold tailWord_1759797
  simp only [CollatzResearch.WordTrace]
  refine ⟨64185069605563493244749645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42790046403708995496499763 64185069605563493244749645)
  ·
    refine ⟨24069401102086309966781117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64185069605563493244749645 24069401102086309966781117)
    ·
      refine ⟨9026025413282366237542919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24069401102086309966781117 9026025413282366237542919)
      ·
        refine ⟨13539038119923549356314379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9026025413282366237542919 13539038119923549356314379)
        ·
          refine ⟨20308557179885324034471569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13539038119923549356314379 20308557179885324034471569)
          ·
            refine ⟨15231417884913993025853677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20308557179885324034471569 15231417884913993025853677)
            ·
              refine ⟨5711781706842747384695129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15231417884913993025853677 5711781706842747384695129)
              ·
                refine ⟨4283836280132060538521347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5711781706842747384695129 4283836280132060538521347)
                ·
                  refine ⟨6425754420198090807782021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4283836280132060538521347 6425754420198090807782021)
                  ·
                    refine ⟨1204828953787142026459129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6425754420198090807782021 1204828953787142026459129)
                    ·
                      refine ⟨903621715340356519844347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1204828953787142026459129 903621715340356519844347)
                      ·
                        rfl

theorem cell23_1759797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_1759797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759797 prefixEnd_1759797 := by exact prefixLift 1759797
  have htrace : WordTrace (prefixWord ++ tailWord_1759797) baseStart_1759797 baseEnd_1759797 := by
    simpa [prefixWord, tailWord_1759797, baseEnd_1759797] using wordTrace_append hprefix tailTrace_1759797
  have hstable : (prefixWord ++ tailWord_1759797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759797).length < 2 ^ (prefixWord ++ tailWord_1759797).sum := by decide
  have hdescent : baseEnd_1759797 < baseStart_1759797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759850 : List Nat := [3, 1, 3, 2, 1, 1, 3, 1, 1, 7]
def baseStart_1759850 : Nat := 118140960795 + 1759850 * 2 ^ 59
def prefixEnd_1759850 : Nat := 4983230072969 + 3 ^ 40 * 1759850 * 2
def baseEnd_1759850 : Nat := 301216309938348270827201

theorem tailTrace_1759850 : CollatzResearch.WordTrace tailWord_1759850 prefixEnd_1759850 301216309938348270827201 := by
  unfold tailWord_1759850
  simp only [CollatzResearch.WordTrace]
  refine ⟨16046750668592870824107251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42791335116247655530952669 16046750668592870824107251)
  ·
    refine ⟨24070126002889306236160877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16046750668592870824107251 24070126002889306236160877)
    ·
      refine ⟨9026297251083489838560329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24070126002889306236160877 9026297251083489838560329)
      ·
        refine ⟨6769722938312617378920247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9026297251083489838560329 6769722938312617378920247)
        ·
          refine ⟨10154584407468926068380371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6769722938312617378920247 10154584407468926068380371)
          ·
            refine ⟨15231876611203389102570557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10154584407468926068380371 15231876611203389102570557)
            ·
              refine ⟨5711953729201270913463959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15231876611203389102570557 5711953729201270913463959)
              ·
                refine ⟨8567930593801906370195939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5711953729201270913463959 8567930593801906370195939)
                ·
                  refine ⟨12851895890702859555293909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8567930593801906370195939 12851895890702859555293909)
                  ·
                    refine ⟨301216309938348270827201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12851895890702859555293909 301216309938348270827201)
                    ·
                      rfl

theorem cell23_1759850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_1759850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759850 prefixEnd_1759850 := by exact prefixLift 1759850
  have htrace : WordTrace (prefixWord ++ tailWord_1759850) baseStart_1759850 baseEnd_1759850 := by
    simpa [prefixWord, tailWord_1759850, baseEnd_1759850] using wordTrace_append hprefix tailTrace_1759850
  have hstable : (prefixWord ++ tailWord_1759850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759850).length < 2 ^ (prefixWord ++ tailWord_1759850).sum := by decide
  have hdescent : baseEnd_1759850 < baseStart_1759850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759854 : List Nat := [4, 1, 2, 2, 2, 2, 2, 3, 5]
def baseStart_1759854 : Nat := 118140960795 + 1759854 * 2 ^ 59
def prefixEnd_1759854 : Nat := 4983230072969 + 3 ^ 40 * 1759854 * 2
def baseEnd_1759854 : Nat := 100405664859740310759065

theorem tailTrace_1759854 : CollatzResearch.WordTrace tailWord_1759854 prefixEnd_1759854 100405664859740310759065 := by
  unfold tailWord_1759854
  simp only [CollatzResearch.WordTrace]
  refine ⟨8023393570794623997446827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42791432377571327986383077 8023393570794623997446827)
  ·
    refine ⟨12035090356191935996170241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8023393570794623997446827 12035090356191935996170241)
    ·
      refine ⟨9026317767143951997127681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12035090356191935996170241 9026317767143951997127681)
      ·
        refine ⟨6769738325357963997845761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9026317767143951997127681 6769738325357963997845761)
        ·
          refine ⟨5077303744018472998384321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6769738325357963997845761 5077303744018472998384321)
          ·
            refine ⟨3807977808013854748788241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5077303744018472998384321 3807977808013854748788241)
            ·
              refine ⟨2855983356010391061591181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3807977808013854748788241 2855983356010391061591181)
              ·
                refine ⟨1070993758503896648096693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2855983356010391061591181 1070993758503896648096693)
                ·
                  refine ⟨100405664859740310759065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1070993758503896648096693 100405664859740310759065)
                  ·
                    rfl

theorem cell23_1759854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3, 5].length) (baseStart_1759854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759854 prefixEnd_1759854 := by exact prefixLift 1759854
  have htrace : WordTrace (prefixWord ++ tailWord_1759854) baseStart_1759854 baseEnd_1759854 := by
    simpa [prefixWord, tailWord_1759854, baseEnd_1759854] using wordTrace_append hprefix tailTrace_1759854
  have hstable : (prefixWord ++ tailWord_1759854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759854).length < 2 ^ (prefixWord ++ tailWord_1759854).sum := by decide
  have hdescent : baseEnd_1759854 < baseStart_1759854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759944 : List Nat := [2, 1, 3, 1, 2, 5, 2, 1, 6]
def baseStart_1759944 : Nat := 118140960795 + 1759944 * 2 ^ 59
def prefixEnd_1759944 : Nat := 4983230072969 + 3 ^ 40 * 1759944 * 2
def baseEnd_1759944 : Nat := 100410799666285271634019

theorem tailTrace_1759944 : CollatzResearch.WordTrace tailWord_1759944 prefixEnd_1759944 100410799666285271634019 := by
  unfold tailWord_1759944
  simp only [CollatzResearch.WordTrace]
  refine ⟨32095215568015468675175443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42793620757353958233567257 32095215568015468675175443)
  ·
    refine ⟨48142823352023203012763165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32095215568015468675175443 48142823352023203012763165)
    ·
      refine ⟨18053558757008701129786187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48142823352023203012763165 18053558757008701129786187)
      ·
        refine ⟨27080338135513051694679281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18053558757008701129786187 27080338135513051694679281)
        ·
          refine ⟨20310253601634788771009461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27080338135513051694679281 20310253601634788771009461)
          ·
            refine ⟨1904086275153261447282137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20310253601634788771009461 1904086275153261447282137)
            ·
              refine ⟨1428064706364946085461603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1904086275153261447282137 1428064706364946085461603)
              ·
                refine ⟨2142097059547419128192405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1428064706364946085461603 2142097059547419128192405)
                ·
                  refine ⟨100410799666285271634019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2142097059547419128192405 100410799666285271634019)
                  ·
                    rfl

theorem cell23_1759944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 6].length) (baseStart_1759944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759944 prefixEnd_1759944 := by exact prefixLift 1759944
  have htrace : WordTrace (prefixWord ++ tailWord_1759944) baseStart_1759944 baseEnd_1759944 := by
    simpa [prefixWord, tailWord_1759944, baseEnd_1759944] using wordTrace_append hprefix tailTrace_1759944
  have hstable : (prefixWord ++ tailWord_1759944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759944).length < 2 ^ (prefixWord ++ tailWord_1759944).sum := by decide
  have hdescent : baseEnd_1759944 < baseStart_1759944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759977 : List Nat := [1, 2, 1, 1, 1, 2, 4, 5, 1, 1, 4]
def baseStart_1759977 : Nat := 118140960795 + 1759977 * 2 ^ 59
def prefixEnd_1759977 : Nat := 4983230072969 + 3 ^ 40 * 1759977 * 2
def baseEnd_1759977 : Nat := 903714141858165815593519

theorem tailTrace_1759977 : CollatzResearch.WordTrace tailWord_1759977 prefixEnd_1759977 903714141858165815593519 := by
  unfold tailWord_1759977
  simp only [CollatzResearch.WordTrace]
  refine ⟨64191634744911383986302185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42794423163274255990868123 64191634744911383986302185)
  ·
    refine ⟨48143726058683537989726639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64191634744911383986302185 48143726058683537989726639)
    ·
      refine ⟨72215589088025306984589959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48143726058683537989726639 72215589088025306984589959)
      ·
        refine ⟨108323383632037960476884939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72215589088025306984589959 108323383632037960476884939)
        ·
          refine ⟨162485075448056940715327409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108323383632037960476884939 162485075448056940715327409)
          ·
            refine ⟨121863806586042705536495557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162485075448056940715327409 121863806586042705536495557)
            ·
              refine ⟨22849463734883007288092917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121863806586042705536495557 22849463734883007288092917)
              ·
                refine ⟨2142137225145281933258711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22849463734883007288092917 2142137225145281933258711)
                ·
                  refine ⟨3213205837717922899888067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2142137225145281933258711 3213205837717922899888067)
                  ·
                    refine ⟨4819808756576884349832101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3213205837717922899888067 4819808756576884349832101)
                    ·
                      refine ⟨903714141858165815593519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4819808756576884349832101 903714141858165815593519)
                      ·
                        rfl

theorem cell23_1759977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 1, 4].length) (baseStart_1759977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759977 prefixEnd_1759977 := by exact prefixLift 1759977
  have htrace : WordTrace (prefixWord ++ tailWord_1759977) baseStart_1759977 baseEnd_1759977 := by
    simpa [prefixWord, tailWord_1759977, baseEnd_1759977] using wordTrace_append hprefix tailTrace_1759977
  have hstable : (prefixWord ++ tailWord_1759977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759977).length < 2 ^ (prefixWord ++ tailWord_1759977).sum := by decide
  have hdescent : baseEnd_1759977 < baseStart_1759977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759997 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 5, 2, 3]
def baseStart_1759997 : Nat := 118140960795 + 1759997 * 2 ^ 59
def prefixEnd_1759997 : Nat := 4983230072969 + 3 ^ 40 * 1759997 * 2
def baseEnd_1759997 : Nat := 903724411471255737343427

theorem tailTrace_1759997 : CollatzResearch.WordTrace tailWord_1759997 prefixEnd_1759997 903724411471255737343427 := by
  unfold tailWord_1759997
  simp only [CollatzResearch.WordTrace]
  refine ⟨64192364204838927402030245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42794909469892618268020163 64192364204838927402030245)
  ·
    refine ⟨12036068288407298887880671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64192364204838927402030245 12036068288407298887880671)
    ·
      refine ⟨18054102432610948331821007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12036068288407298887880671 18054102432610948331821007)
      ·
        refine ⟨27081153648916422497731511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18054102432610948331821007 27081153648916422497731511)
        ·
          refine ⟨40621730473374633746597267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27081153648916422497731511 40621730473374633746597267)
          ·
            refine ⟨60932595710061950619895901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40621730473374633746597267 60932595710061950619895901)
            ·
              refine ⟨22849723391273231482460963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60932595710061950619895901 22849723391273231482460963)
              ·
                refine ⟨34274585086909847223691445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22849723391273231482460963 34274585086909847223691445)
                ·
                  refine ⟨3213242351897798177221073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34274585086909847223691445 3213242351897798177221073)
                  ·
                    refine ⟨2409931763923348632915805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3213242351897798177221073 2409931763923348632915805)
                    ·
                      refine ⟨903724411471255737343427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2409931763923348632915805 903724411471255737343427)
                      ·
                        rfl

theorem cell23_1759997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_1759997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1759997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1759997 prefixEnd_1759997 := by exact prefixLift 1759997
  have htrace : WordTrace (prefixWord ++ tailWord_1759997) baseStart_1759997 baseEnd_1759997 := by
    simpa [prefixWord, tailWord_1759997, baseEnd_1759997] using wordTrace_append hprefix tailTrace_1759997
  have hstable : (prefixWord ++ tailWord_1759997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759997).length < 2 ^ (prefixWord ++ tailWord_1759997).sum := by decide
  have hdescent : baseEnd_1759997 < baseStart_1759997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760004 : List Nat := [2, 3, 2, 2, 1, 1, 1, 5, 2, 4]
def baseStart_1760004 : Nat := 118140960795 + 1760004 * 2 ^ 59
def prefixEnd_1760004 : Nat := 4983230072969 + 3 ^ 40 * 1760004 * 2
def baseEnd_1760004 : Nat := 301242668611945736651965

theorem tailTrace_1760004 : CollatzResearch.WordTrace tailWord_1760004 prefixEnd_1760004 301242668611945736651965 := by
  unfold tailWord_1760004
  simp only [CollatzResearch.WordTrace]
  refine ⟨32096309757906783798767533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42795079677209045065023377 32096309757906783798767533)
  ·
    refine ⟨12036116159215043924537825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32096309757906783798767533 12036116159215043924537825)
    ·
      refine ⟨9027087119411282943403369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12036116159215043924537825 9027087119411282943403369)
      ·
        refine ⟨6770315339558462207552527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9027087119411282943403369 6770315339558462207552527)
        ·
          refine ⟨10155473009337693311328791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6770315339558462207552527 10155473009337693311328791)
          ·
            refine ⟨15233209514006539966993187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10155473009337693311328791 15233209514006539966993187)
            ·
              refine ⟨22849814271009809950489781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15233209514006539966993187 22849814271009809950489781)
              ·
                refine ⟨2142170087907169682858417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22849814271009809950489781 2142170087907169682858417)
                ·
                  refine ⟨1606627565930377262143813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2142170087907169682858417 1606627565930377262143813)
                  ·
                    refine ⟨301242668611945736651965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1606627565930377262143813 301242668611945736651965)
                    ·
                      rfl

theorem cell23_1760004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_1760004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760004 prefixEnd_1760004 := by exact prefixLift 1760004
  have htrace : WordTrace (prefixWord ++ tailWord_1760004) baseStart_1760004 baseEnd_1760004 := by
    simpa [prefixWord, tailWord_1760004, baseEnd_1760004] using wordTrace_append hprefix tailTrace_1760004
  have hstable : (prefixWord ++ tailWord_1760004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760004).length < 2 ^ (prefixWord ++ tailWord_1760004).sum := by decide
  have hdescent : baseEnd_1760004 < baseStart_1760004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760014 : List Nat := [4, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3]
def baseStart_1760014 : Nat := 118140960795 + 1760014 * 2 ^ 59
def prefixEnd_1760014 : Nat := 4983230072969 + 3 ^ 40 * 1760014 * 2
def baseEnd_1760014 : Nat := 903733140642382170830849

theorem tailTrace_1760014 : CollatzResearch.WordTrace tailWord_1760014 prefixEnd_1760014 903733140642382170830849 := by
  unfold tailWord_1760014
  simp only [CollatzResearch.WordTrace]
  refine ⟨8024123030722167413174887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42795322830518226203599397 8024123030722167413174887)
  ·
    refine ⟨12036184546083251119762331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8024123030722167413174887 12036184546083251119762331)
    ·
      refine ⟨18054276819124876679643497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12036184546083251119762331 18054276819124876679643497)
      ·
        refine ⟨13540707614343657509732623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18054276819124876679643497 13540707614343657509732623)
        ·
          refine ⟨20311061421515486264598935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13540707614343657509732623 20311061421515486264598935)
          ·
            refine ⟨30466592132273229396898403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20311061421515486264598935 30466592132273229396898403)
            ·
              refine ⟨45699888198409844095347605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30466592132273229396898403 45699888198409844095347605)
              ·
                refine ⟨2142182259300461441969419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45699888198409844095347605 2142182259300461441969419)
                ·
                  refine ⟨3213273388950692162954129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2142182259300461441969419 3213273388950692162954129)
                  ·
                    refine ⟨2409955041713019122215597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3213273388950692162954129 2409955041713019122215597)
                    ·
                      refine ⟨903733140642382170830849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2409955041713019122215597 903733140642382170830849)
                      ·
                        rfl

theorem cell23_1760014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_1760014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760014 prefixEnd_1760014 := by exact prefixLift 1760014
  have htrace : WordTrace (prefixWord ++ tailWord_1760014) baseStart_1760014 baseEnd_1760014 := by
    simpa [prefixWord, tailWord_1760014, baseEnd_1760014] using wordTrace_append hprefix tailTrace_1760014
  have hstable : (prefixWord ++ tailWord_1760014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760014).length < 2 ^ (prefixWord ++ tailWord_1760014).sum := by decide
  have hdescent : baseEnd_1760014 < baseStart_1760014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760028 : List Nat := [2, 2, 3, 1, 1, 3, 1, 5, 1, 2, 2]
def baseStart_1760028 : Nat := 118140960795 + 1760028 * 2 ^ 59
def prefixEnd_1760028 : Nat := 4983230072969 + 3 ^ 40 * 1760028 * 2
def baseEnd_1760028 : Nat := 903740329371545116055785

theorem tailTrace_1760028 : CollatzResearch.WordTrace tailWord_1760028 prefixEnd_1760028 903740329371545116055785 := by
  unfold tailWord_1760028
  simp only [CollatzResearch.WordTrace]
  refine ⟨32096747433863309848204369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42795663245151079797605825 32096747433863309848204369)
  ·
    refine ⟨24072560575397482386153277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32096747433863309848204369 24072560575397482386153277)
    ·
      refine ⟨9027210215774055894807479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24072560575397482386153277 9027210215774055894807479)
      ·
        refine ⟨13540815323661083842211219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9027210215774055894807479 13540815323661083842211219)
        ·
          refine ⟨20311222985491625763316829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13540815323661083842211219 20311222985491625763316829)
          ·
            refine ⟨7616708619559359661243811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20311222985491625763316829 7616708619559359661243811)
            ·
              refine ⟨11425062929339039491865717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7616708619559359661243811 11425062929339039491865717)
              ·
                refine ⟨1071099649625534952362411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11425062929339039491865717 1071099649625534952362411)
                ·
                  refine ⟨1606649474438302428543617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1071099649625534952362411 1606649474438302428543617)
                  ·
                    refine ⟨1204987105828726821407713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1606649474438302428543617 1204987105828726821407713)
                    ·
                      refine ⟨903740329371545116055785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1204987105828726821407713 903740329371545116055785)
                      ·
                        rfl

theorem cell23_1760028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_1760028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760028 prefixEnd_1760028 := by exact prefixLift 1760028
  have htrace : WordTrace (prefixWord ++ tailWord_1760028) baseStart_1760028 baseEnd_1760028 := by
    simpa [prefixWord, tailWord_1760028, baseEnd_1760028] using wordTrace_append hprefix tailTrace_1760028
  have hstable : (prefixWord ++ tailWord_1760028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760028).length < 2 ^ (prefixWord ++ tailWord_1760028).sum := by decide
  have hdescent : baseEnd_1760028 < baseStart_1760028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760031 : List Nat := [1, 1, 2, 4, 2, 2, 4, 1, 1, 2, 3]
def baseStart_1760031 : Nat := 118140960795 + 1760031 * 2 ^ 59
def prefixEnd_1760031 : Nat := 4983230072969 + 3 ^ 40 * 1760031 * 2
def baseEnd_1760031 : Nat := 903741869813508604318271

theorem tailTrace_1760031 : CollatzResearch.WordTrace tailWord_1760031 prefixEnd_1760031 903741869813508604318271 := by
  unfold tailWord_1760031
  simp only [CollatzResearch.WordTrace]
  refine ⟨64193604286715751208767947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42795736191143834139178631 64193604286715751208767947)
  ·
    refine ⟨96290406430073626813151921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64193604286715751208767947 96290406430073626813151921)
    ·
      refine ⟨72217804822555220109863941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96290406430073626813151921 72217804822555220109863941)
      ·
        refine ⟨13540838404229103770599489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72217804822555220109863941 13540838404229103770599489)
        ·
          refine ⟨10155628803171827827949617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13540838404229103770599489 10155628803171827827949617)
          ·
            refine ⟨7616721602378870870962213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10155628803171827827949617 7616721602378870870962213)
            ·
              refine ⟨1428135300446038288305415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7616721602378870870962213 1428135300446038288305415)
              ·
                refine ⟨2142202950669057432458123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1428135300446038288305415 2142202950669057432458123)
                ·
                  refine ⟨3213304426003586148687185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2142202950669057432458123 3213304426003586148687185)
                  ·
                    refine ⟨2409978319502689611515389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3213304426003586148687185 2409978319502689611515389)
                    ·
                      refine ⟨903741869813508604318271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2409978319502689611515389 903741869813508604318271)
                      ·
                        rfl

theorem cell23_1760031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_1760031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760031 prefixEnd_1760031 := by exact prefixLift 1760031
  have htrace : WordTrace (prefixWord ++ tailWord_1760031) baseStart_1760031 baseEnd_1760031 := by
    simpa [prefixWord, tailWord_1760031, baseEnd_1760031] using wordTrace_append hprefix tailTrace_1760031
  have hstable : (prefixWord ++ tailWord_1760031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760031).length < 2 ^ (prefixWord ++ tailWord_1760031).sum := by decide
  have hdescent : baseEnd_1760031 < baseStart_1760031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760044 : List Nat := [2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 3]
def baseStart_1760044 : Nat := 118140960795 + 1760044 * 2 ^ 59
def prefixEnd_1760044 : Nat := 4983230072969 + 3 ^ 40 * 1760044 * 2
def baseEnd_1760044 : Nat := 903748545062017053455711

theorem tailTrace_1760044 : CollatzResearch.WordTrace tailWord_1760044 prefixEnd_1760044 903748545062017053455711 := by
  unfold tailWord_1760044
  simp only [CollatzResearch.WordTrace]
  refine ⟨32097039217834327214495593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42796052290445769619327457 32097039217834327214495593)
  ·
    refine ⟨24072779413375745410871695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32097039217834327214495593 24072779413375745410871695)
    ·
      refine ⟨36109169120063618116307543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24072779413375745410871695 36109169120063618116307543)
      ·
        refine ⟨54163753680095427174461315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36109169120063618116307543 54163753680095427174461315)
        ·
          refine ⟨81245630520143140761691973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54163753680095427174461315 81245630520143140761691973)
          ·
            refine ⟨15233555722526838892817245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81245630520143140761691973 15233555722526838892817245)
            ·
              refine ⟨5712583395947564584806467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15233555722526838892817245 5712583395947564584806467)
              ·
                refine ⟨8568875093921346877209701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5712583395947564584806467 8568875093921346877209701)
                ·
                  refine ⟨1606664080110252539476819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8568875093921346877209701 1606664080110252539476819)
                  ·
                    refine ⟨2409996120165378809215229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1606664080110252539476819 2409996120165378809215229)
                    ·
                      refine ⟨903748545062017053455711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2409996120165378809215229 903748545062017053455711)
                      ·
                        rfl

theorem cell23_1760044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 3].length) (baseStart_1760044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760044 prefixEnd_1760044 := by exact prefixLift 1760044
  have htrace : WordTrace (prefixWord ++ tailWord_1760044) baseStart_1760044 baseEnd_1760044 := by
    simpa [prefixWord, tailWord_1760044, baseEnd_1760044] using wordTrace_append hprefix tailTrace_1760044
  have hstable : (prefixWord ++ tailWord_1760044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760044).length < 2 ^ (prefixWord ++ tailWord_1760044).sum := by decide
  have hdescent : baseEnd_1760044 < baseStart_1760044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760068 : List Nat := [2, 3, 4, 2, 1, 2, 2, 7]
def baseStart_1760068 : Nat := 118140960795 + 1760068 * 2 ^ 59
def prefixEnd_1760068 : Nat := 4983230072969 + 3 ^ 40 * 1760068 * 2
def baseEnd_1760068 : Nat := 33472624762878702205763

theorem tailTrace_1760068 : CollatzResearch.WordTrace tailWord_1760068 prefixEnd_1760068 33472624762878702205763 := by
  unfold tailWord_1760068
  simp only [CollatzResearch.WordTrace]
  refine ⟨32097476893790853263932429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42796635858387804351909905 32097476893790853263932429)
  ·
    refine ⟨12036553835171569973974661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32097476893790853263932429 12036553835171569973974661)
    ·
      refine ⟨2256853844094669370120249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12036553835171569973974661 2256853844094669370120249)
      ·
        refine ⟨1692640383071002027590187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2256853844094669370120249 1692640383071002027590187)
        ·
          refine ⟨2538960574606503041385281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1692640383071002027590187 2538960574606503041385281)
          ·
            refine ⟨1904220430954877281038961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2538960574606503041385281 1904220430954877281038961)
            ·
              refine ⟨1428165323216157960779221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1904220430954877281038961 1428165323216157960779221)
              ·
                refine ⟨33472624762878702205763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1428165323216157960779221 33472624762878702205763)
                ·
                  rfl

theorem cell23_1760068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 7].length) (baseStart_1760068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760068 prefixEnd_1760068 := by exact prefixLift 1760068
  have htrace : WordTrace (prefixWord ++ tailWord_1760068) baseStart_1760068 baseEnd_1760068 := by
    simpa [prefixWord, tailWord_1760068, baseEnd_1760068] using wordTrace_append hprefix tailTrace_1760068
  have hstable : (prefixWord ++ tailWord_1760068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760068).length < 2 ^ (prefixWord ++ tailWord_1760068).sum := by decide
  have hdescent : baseEnd_1760068 < baseStart_1760068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760087 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 5]
def baseStart_1760087 : Nat := 118140960795 + 1760087 * 2 ^ 59
def prefixEnd_1760087 : Nat := 4983230072969 + 3 ^ 40 * 1760087 * 2
def baseEnd_1760087 : Nat := 903770624730160385218013

theorem tailTrace_1760087 : CollatzResearch.WordTrace tailWord_1760087 prefixEnd_1760087 903770624730160385218013 := by
  unfold tailWord_1760087
  simp only [CollatzResearch.WordTrace]
  refine ⟨64195646774512872772806515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42797097849675248515204343 64195646774512872772806515)
  ·
    refine ⟨96293470161769309159209773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64195646774512872772806515 96293470161769309159209773)
    ·
      refine ⟨36110051310663490934703665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96293470161769309159209773 36110051310663490934703665)
      ·
        refine ⟨27082538482997618201027749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36110051310663490934703665 27082538482997618201027749)
        ·
          refine ⟨5077975965562053412692703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27082538482997618201027749 5077975965562053412692703)
          ·
            refine ⟨7616963948343080119039055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5077975965562053412692703 7616963948343080119039055)
            ·
              refine ⟨11425445922514620178558583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7616963948343080119039055 11425445922514620178558583)
              ·
                refine ⟨17138168883771930267837875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11425445922514620178558583 17138168883771930267837875)
                ·
                  refine ⟨25707253325657895401756813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17138168883771930267837875 25707253325657895401756813)
                  ·
                    refine ⟨9640219997121710775658805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25707253325657895401756813 9640219997121710775658805)
                    ·
                      refine ⟨903770624730160385218013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9640219997121710775658805 903770624730160385218013)
                      ·
                        rfl

theorem cell23_1760087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_1760087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760087 prefixEnd_1760087 := by exact prefixLift 1760087
  have htrace : WordTrace (prefixWord ++ tailWord_1760087) baseStart_1760087 baseEnd_1760087 := by
    simpa [prefixWord, tailWord_1760087, baseEnd_1760087] using wordTrace_append hprefix tailTrace_1760087
  have hstable : (prefixWord ++ tailWord_1760087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760087).length < 2 ^ (prefixWord ++ tailWord_1760087).sum := by decide
  have hdescent : baseEnd_1760087 < baseStart_1760087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760097 : List Nat := [1, 2, 3, 1, 1, 1, 2, 4, 2, 2, 4]
def baseStart_1760097 : Nat := 118140960795 + 1760097 * 2 ^ 59
def prefixEnd_1760097 : Nat := 4983230072969 + 3 ^ 40 * 1760097 * 2
def baseEnd_1760097 : Nat := 903775759536705346092967

theorem tailTrace_1760097 : CollatzResearch.WordTrace tailWord_1760097 prefixEnd_1760097 903775759536705346092967 := by
  unfold tailWord_1760097
  simp only [CollatzResearch.WordTrace]
  refine ⟨64196011504476644480670545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42797341002984429653780363 64196011504476644480670545)
  ·
    refine ⟨48147008628357483360502909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64196011504476644480670545 48147008628357483360502909)
    ·
      refine ⟨18055128235634056260188591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48147008628357483360502909 18055128235634056260188591)
      ·
        refine ⟨27082692353451084390282887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18055128235634056260188591 27082692353451084390282887)
        ·
          refine ⟨40624038530176626585424331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27082692353451084390282887 40624038530176626585424331)
          ·
            refine ⟨60936057795264939878136497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40624038530176626585424331 60936057795264939878136497)
            ·
              refine ⟨45702043346448704908602373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60936057795264939878136497 45702043346448704908602373)
              ·
                refine ⟨8569133127459132170362945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45702043346448704908602373 8569133127459132170362945)
                ·
                  refine ⟨6426849845594349127772209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8569133127459132170362945 6426849845594349127772209)
                  ·
                    refine ⟨4820137384195761845829157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6426849845594349127772209 4820137384195761845829157)
                    ·
                      refine ⟨903775759536705346092967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4820137384195761845829157 903775759536705346092967)
                      ·
                        rfl

theorem cell23_1760097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_1760097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760097 prefixEnd_1760097 := by exact prefixLift 1760097
  have htrace : WordTrace (prefixWord ++ tailWord_1760097) baseStart_1760097 baseEnd_1760097 := by
    simpa [prefixWord, tailWord_1760097, baseEnd_1760097] using wordTrace_append hprefix tailTrace_1760097
  have hstable : (prefixWord ++ tailWord_1760097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760097).length < 2 ^ (prefixWord ++ tailWord_1760097).sum := by decide
  have hdescent : baseEnd_1760097 < baseStart_1760097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760101 : List Nat := [1, 3, 1, 3, 1, 1, 4, 1, 4, 2, 2]
def baseStart_1760101 : Nat := 118140960795 + 1760101 * 2 ^ 59
def prefixEnd_1760101 : Nat := 4983230072969 + 3 ^ 40 * 1760101 * 2
def baseEnd_1760101 : Nat := 903777813459323330442949

theorem tailTrace_1760101 : CollatzResearch.WordTrace tailWord_1760101 prefixEnd_1760101 903777813459323330442949 := by
  unfold tailWord_1760101
  simp only [CollatzResearch.WordTrace]
  refine ⟨64196157396462153163816157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42797438264308102109210771 64196157396462153163816157)
  ·
    refine ⟨24073559023673307436431059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64196157396462153163816157 24073559023673307436431059)
    ·
      refine ⟨36110338535509961154646589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24073559023673307436431059 36110338535509961154646589)
      ·
        refine ⟨13541376950816235432992471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36110338535509961154646589 13541376950816235432992471)
        ·
          refine ⟨20312065426224353149488707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13541376950816235432992471 20312065426224353149488707)
          ·
            refine ⟨30468098139336529724233061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20312065426224353149488707 30468098139336529724233061)
            ·
              refine ⟨5712768401125599323293699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30468098139336529724233061 5712768401125599323293699)
              ·
                refine ⟨8569152601688398984940549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5712768401125599323293699 8569152601688398984940549)
                ·
                  refine ⟨1606716112816574809676353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8569152601688398984940549 1606716112816574809676353)
                  ·
                    refine ⟨1205037084612431107257265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1606716112816574809676353 1205037084612431107257265)
                    ·
                      refine ⟨903777813459323330442949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1205037084612431107257265 903777813459323330442949)
                      ·
                        rfl

theorem cell23_1760101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_1760101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760101 prefixEnd_1760101 := by exact prefixLift 1760101
  have htrace : WordTrace (prefixWord ++ tailWord_1760101) baseStart_1760101 baseEnd_1760101 := by
    simpa [prefixWord, tailWord_1760101, baseEnd_1760101] using wordTrace_append hprefix tailTrace_1760101
  have hstable : (prefixWord ++ tailWord_1760101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760101).length < 2 ^ (prefixWord ++ tailWord_1760101).sum := by decide
  have hdescent : baseEnd_1760101 < baseStart_1760101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760107 : List Nat := [1, 1, 1, 1, 2, 2, 7, 1, 7]
def baseStart_1760107 : Nat := 118140960795 + 1760107 * 2 ^ 59
def prefixEnd_1760107 : Nat := 4983230072969 + 3 ^ 40 * 1760107 * 2
def baseEnd_1760107 : Nat := 100420099371472256329769

theorem tailTrace_1760107 : CollatzResearch.WordTrace tailWord_1760107 prefixEnd_1760107 100420099371472256329769 := by
  unfold tailWord_1760107
  simp only [CollatzResearch.WordTrace]
  refine ⟨64196376234440416188534575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42797584156293610792356383 64196376234440416188534575)
  ·
    refine ⟨96294564351660624282801863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64196376234440416188534575 96294564351660624282801863)
    ·
      refine ⟨144441846527490936424202795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96294564351660624282801863 144441846527490936424202795)
      ·
        refine ⟨216662769791236404636304193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144441846527490936424202795 216662769791236404636304193)
        ·
          refine ⟨162497077343427303477228145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216662769791236404636304193 162497077343427303477228145)
          ·
            refine ⟨121872808007570477607921109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162497077343427303477228145 121872808007570477607921109)
            ·
              refine ⟨2856393937677433068935651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 121872808007570477607921109 2856393937677433068935651)
              ·
                refine ⟨4284590906516149603403477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2856393937677433068935651 4284590906516149603403477)
                ·
                  refine ⟨100420099371472256329769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4284590906516149603403477 100420099371472256329769)
                  ·
                    rfl

theorem cell23_1760107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 7].length) (baseStart_1760107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760107 prefixEnd_1760107 := by exact prefixLift 1760107
  have htrace : WordTrace (prefixWord ++ tailWord_1760107) baseStart_1760107 baseEnd_1760107 := by
    simpa [prefixWord, tailWord_1760107, baseEnd_1760107] using wordTrace_append hprefix tailTrace_1760107
  have hstable : (prefixWord ++ tailWord_1760107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760107).length < 2 ^ (prefixWord ++ tailWord_1760107).sum := by decide
  have hdescent : baseEnd_1760107 < baseStart_1760107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760161 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 2, 5, 2]
def baseStart_1760161 : Nat := 118140960795 + 1760161 * 2 ^ 59
def prefixEnd_1760161 : Nat := 4983230072969 + 3 ^ 40 * 1760161 * 2
def baseEnd_1760161 : Nat := 903808622298593095692673

theorem tailTrace_1760161 : CollatzResearch.WordTrace tailWord_1760161 prefixEnd_1760161 903808622298593095692673 := by
  unfold tailWord_1760161
  simp only [CollatzResearch.WordTrace]
  refine ⟨64198345776244783411000337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42798897184163188940666891 64198345776244783411000337)
  ·
    refine ⟨48148759332183587558250253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64198345776244783411000337 48148759332183587558250253)
    ·
      refine ⟨18055784749568845334343845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48148759332183587558250253 18055784749568845334343845)
      ·
        refine ⟨3385459640544158500189471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18055784749568845334343845 3385459640544158500189471)
        ·
          refine ⟨5078189460816237750284207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3385459640544158500189471 5078189460816237750284207)
          ·
            refine ⟨7617284191224356625426311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5078189460816237750284207 7617284191224356625426311)
            ·
              refine ⟨11425926286836534938139467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7617284191224356625426311 11425926286836534938139467)
              ·
                refine ⟨17138889430254802407209201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11425926286836534938139467 17138889430254802407209201)
                ·
                  refine ⟨12854167072691101805406901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17138889430254802407209201 12854167072691101805406901)
                  ·
                    refine ⟨1205078163064790794256897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12854167072691101805406901 1205078163064790794256897)
                    ·
                      refine ⟨903808622298593095692673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1205078163064790794256897 903808622298593095692673)
                      ·
                        rfl

theorem cell23_1760161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_1760161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760161 prefixEnd_1760161 := by exact prefixLift 1760161
  have htrace : WordTrace (prefixWord ++ tailWord_1760161) baseStart_1760161 baseEnd_1760161 := by
    simpa [prefixWord, tailWord_1760161, baseEnd_1760161] using wordTrace_append hprefix tailTrace_1760161
  have hstable : (prefixWord ++ tailWord_1760161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760161).length < 2 ^ (prefixWord ++ tailWord_1760161).sum := by decide
  have hdescent : baseEnd_1760161 < baseStart_1760161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760184 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 5, 4]
def baseStart_1760184 : Nat := 118140960795 + 1760184 * 2 ^ 59
def prefixEnd_1760184 : Nat := 4983230072969 + 3 ^ 40 * 1760184 * 2
def baseEnd_1760184 : Nat := 301273477451215501901689

theorem tailTrace_1760184 : CollatzResearch.WordTrace tailWord_1760184 prefixEnd_1760184 301273477451215501901689 := by
  unfold tailWord_1760184
  simp only [CollatzResearch.WordTrace]
  refine ⟨32099592327580729169543803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42799456436774305559391737 32099592327580729169543803)
  ·
    refine ⟨48149388491371093754315705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32099592327580729169543803 48149388491371093754315705)
    ·
      refine ⟨36112041368528320315736779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48149388491371093754315705 36112041368528320315736779)
      ·
        refine ⟨54168062052792480473605169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36112041368528320315736779 54168062052792480473605169)
        ·
          refine ⟨40626046539594360355203877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54168062052792480473605169 40626046539594360355203877)
          ·
            refine ⟨7617383726173942566600727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40626046539594360355203877 7617383726173942566600727)
            ·
              refine ⟨11426075589260913849901091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7617383726173942566600727 11426075589260913849901091)
              ·
                refine ⟨17139113383891370774851637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11426075589260913849901091 17139113383891370774851637)
                ·
                  refine ⟨1606791879739816010142341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17139113383891370774851637 1606791879739816010142341)
                  ·
                    refine ⟨301273477451215501901689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1606791879739816010142341 301273477451215501901689)
                    ·
                      rfl

theorem cell23_1760184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 5, 4].length) (baseStart_1760184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760184 prefixEnd_1760184 := by exact prefixLift 1760184
  have htrace : WordTrace (prefixWord ++ tailWord_1760184) baseStart_1760184 baseEnd_1760184 := by
    simpa [prefixWord, tailWord_1760184, baseEnd_1760184] using wordTrace_append hprefix tailTrace_1760184
  have hstable : (prefixWord ++ tailWord_1760184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760184).length < 2 ^ (prefixWord ++ tailWord_1760184).sum := by decide
  have hdescent : baseEnd_1760184 < baseStart_1760184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760218 : List Nat := [3, 1, 1, 2, 4, 1, 2, 4, 1, 4]
def baseStart_1760218 : Nat := 118140960795 + 1760218 * 2 ^ 59
def prefixEnd_1760218 : Nat := 4983230072969 + 3 ^ 40 * 1760218 * 2
def baseEnd_1760218 : Nat := 301279296898633124226637

theorem tailTrace_1760218 : CollatzResearch.WordTrace tailWord_1760218 prefixEnd_1760218 301279296898633124226637 := by
  unfold tailWord_1760218
  simp only [CollatzResearch.WordTrace]
  refine ⟨16050106184259570536456327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42800283158025521430550205 16050106184259570536456327)
  ·
    refine ⟨24075159276389355804684491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16050106184259570536456327 24075159276389355804684491)
    ·
      refine ⟨36112738914584033707026737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24075159276389355804684491 36112738914584033707026737)
      ·
        refine ⟨27084554185938025280270053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36112738914584033707026737 27084554185938025280270053)
        ·
          refine ⟨5078353909863379740050635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27084554185938025280270053 5078353909863379740050635)
          ·
            refine ⟨7617530864795069610075953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5078353909863379740050635 7617530864795069610075953)
            ·
              refine ⟨5713148148596302207556965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7617530864795069610075953 5713148148596302207556965)
              ·
                refine ⟨1071215277861806663916931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5713148148596302207556965 1071215277861806663916931)
                ·
                  refine ⟨1606822916792709995875397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1071215277861806663916931 1606822916792709995875397)
                  ·
                    refine ⟨301279296898633124226637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1606822916792709995875397 301279296898633124226637)
                    ·
                      rfl

theorem cell23_1760218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4, 1, 4].length) (baseStart_1760218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760218 prefixEnd_1760218 := by exact prefixLift 1760218
  have htrace : WordTrace (prefixWord ++ tailWord_1760218) baseStart_1760218 baseEnd_1760218 := by
    simpa [prefixWord, tailWord_1760218, baseEnd_1760218] using wordTrace_append hprefix tailTrace_1760218
  have hstable : (prefixWord ++ tailWord_1760218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760218).length < 2 ^ (prefixWord ++ tailWord_1760218).sum := by decide
  have hdescent : baseEnd_1760218 < baseStart_1760218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760251 : List Nat := [1, 1, 1, 1, 1, 3, 3, 5, 2, 3, 2]
def baseStart_1760251 : Nat := 118140960795 + 1760251 * 2 ^ 59
def prefixEnd_1760251 : Nat := 4983230072969 + 3 ^ 40 * 1760251 * 2
def baseEnd_1760251 : Nat := 903854835557497743567259

theorem tailTrace_1760251 : CollatzResearch.WordTrace tailWord_1760251 prefixEnd_1760251 903854835557497743567259 := by
  unfold tailWord_1760251
  simp only [CollatzResearch.WordTrace]
  refine ⟨64201628345918728781776607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42801085563945819187851071 64201628345918728781776607)
  ·
    refine ⟨96302442518878093172664911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64201628345918728781776607 96302442518878093172664911)
    ·
      refine ⟨144453663778317139758997367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96302442518878093172664911 144453663778317139758997367)
      ·
        refine ⟨216680495667475709638496051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144453663778317139758997367 216680495667475709638496051)
        ·
          refine ⟨325020743501213564457744077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216680495667475709638496051 325020743501213564457744077)
          ·
            refine ⟨121882778812955086671654029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 325020743501213564457744077 121882778812955086671654029)
            ·
              refine ⟨45706042054858157501870261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121882778812955086671654029 45706042054858157501870261)
              ·
                refine ⟨4284941442642952265800337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45706042054858157501870261 4284941442642952265800337)
                ·
                  refine ⟨3213706081982214199350253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4284941442642952265800337 3213706081982214199350253)
                  ·
                    refine ⟨1205139780743330324756345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3213706081982214199350253 1205139780743330324756345)
                    ·
                      refine ⟨903854835557497743567259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1205139780743330324756345 903854835557497743567259)
                      ·
                        rfl

theorem cell23_1760251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 3, 2].length) (baseStart_1760251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760251 prefixEnd_1760251 := by exact prefixLift 1760251
  have htrace : WordTrace (prefixWord ++ tailWord_1760251) baseStart_1760251 baseEnd_1760251 := by
    simpa [prefixWord, tailWord_1760251, baseEnd_1760251] using wordTrace_append hprefix tailTrace_1760251
  have hstable : (prefixWord ++ tailWord_1760251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760251).length < 2 ^ (prefixWord ++ tailWord_1760251).sum := by decide
  have hdescent : baseEnd_1760251 < baseStart_1760251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760268 : List Nat := [2, 2, 1, 2, 3, 3, 1, 2, 2, 3, 2]
def baseStart_1760268 : Nat := 118140960795 + 1760268 * 2 ^ 59
def prefixEnd_1760268 : Nat := 4983230072969 + 3 ^ 40 * 1760268 * 2
def baseEnd_1760268 : Nat := 903863564728624177054681

theorem tailTrace_1760268 : CollatzResearch.WordTrace tailWord_1760268 prefixEnd_1760268 903863564728624177054681 := by
  unfold tailWord_1760268
  simp only [CollatzResearch.WordTrace]
  refine ⟨32101124193428570342572729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42801498924571427123430305 32101124193428570342572729)
  ·
    refine ⟨24075843145071427756929547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32101124193428570342572729 24075843145071427756929547)
    ·
      refine ⟨36113764717607141635394321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24075843145071427756929547 36113764717607141635394321)
      ·
        refine ⟨27085323538205356226545741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36113764717607141635394321 27085323538205356226545741)
        ·
          refine ⟨10156996326827008584954653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27085323538205356226545741 10156996326827008584954653)
          ·
            refine ⟨3808873622560128219357995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10156996326827008584954653 3808873622560128219357995)
            ·
              refine ⟨5713310433840192329036993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3808873622560128219357995 5713310433840192329036993)
              ·
                refine ⟨4284982825380144246777745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5713310433840192329036993 4284982825380144246777745)
                ·
                  refine ⟨3213737119035108185083309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4284982825380144246777745 3213737119035108185083309)
                  ·
                    refine ⟨1205151419638165569406241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3213737119035108185083309 1205151419638165569406241)
                    ·
                      refine ⟨903863564728624177054681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1205151419638165569406241 903863564728624177054681)
                      ·
                        rfl

theorem cell23_1760268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 2, 3, 2].length) (baseStart_1760268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760268 prefixEnd_1760268 := by exact prefixLift 1760268
  have htrace : WordTrace (prefixWord ++ tailWord_1760268) baseStart_1760268 baseEnd_1760268 := by
    simpa [prefixWord, tailWord_1760268, baseEnd_1760268] using wordTrace_append hprefix tailTrace_1760268
  have hstable : (prefixWord ++ tailWord_1760268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760268).length < 2 ^ (prefixWord ++ tailWord_1760268).sum := by decide
  have hdescent : baseEnd_1760268 < baseStart_1760268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760295 : List Nat := [1, 1, 7, 1, 1, 3, 1, 2, 1, 5]
def baseStart_1760295 : Nat := 118140960795 + 1760295 * 2 ^ 59
def prefixEnd_1760295 : Nat := 4983230072969 + 3 ^ 40 * 1760295 * 2
def baseEnd_1760295 : Nat := 301292476235431857139019

theorem tailTrace_1760295 : CollatzResearch.WordTrace tailWord_1760295 prefixEnd_1760295 301292476235431857139019 := by
  unfold tailWord_1760295
  simp only [CollatzResearch.WordTrace]
  refine ⟨64203233157759324296378339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42802155438506216197585559 64203233157759324296378339)
  ·
    refine ⟨96304849736638986444567509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64203233157759324296378339 96304849736638986444567509)
    ·
      refine ⟨2257144915702476244794551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 96304849736638986444567509 2257144915702476244794551)
      ·
        refine ⟨3385717373553714367191827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2257144915702476244794551 3385717373553714367191827)
        ·
          refine ⟨5078576060330571550787741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3385717373553714367191827 5078576060330571550787741)
          ·
            refine ⟨1904466022623964331545403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5078576060330571550787741 1904466022623964331545403)
            ·
              refine ⟨2856699033935946497318105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1904466022623964331545403 2856699033935946497318105)
              ·
                refine ⟨2142524275451959872988579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2856699033935946497318105 2142524275451959872988579)
                ·
                  refine ⟨3213786413177939809482869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2142524275451959872988579 3213786413177939809482869)
                  ·
                    refine ⟨301292476235431857139019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3213786413177939809482869 301292476235431857139019)
                    ·
                      rfl

theorem cell23_1760295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_1760295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760295 prefixEnd_1760295 := by exact prefixLift 1760295
  have htrace : WordTrace (prefixWord ++ tailWord_1760295) baseStart_1760295 baseEnd_1760295 := by
    simpa [prefixWord, tailWord_1760295, baseEnd_1760295] using wordTrace_append hprefix tailTrace_1760295
  have hstable : (prefixWord ++ tailWord_1760295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760295).length < 2 ^ (prefixWord ++ tailWord_1760295).sum := by decide
  have hdescent : baseEnd_1760295 < baseStart_1760295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760298 : List Nat := [3, 1, 4, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_1760298 : Nat := 118140960795 + 1760298 * 2 ^ 59
def prefixEnd_1760298 : Nat := 4983230072969 + 3 ^ 40 * 1760298 * 2
def baseEnd_1760298 : Nat := 903878969148259059679543

theorem tailTrace_1760298 : CollatzResearch.WordTrace tailWord_1760298 prefixEnd_1760298 903878969148259059679543 := by
  unfold tailWord_1760298
  simp only [CollatzResearch.WordTrace]
  refine ⟨16050835644187113952184387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42802228384498970539158365 16050835644187113952184387)
  ·
    refine ⟨24076253466280670928276581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16050835644187113952184387 24076253466280670928276581)
    ·
      refine ⟨4514297524927625799051859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24076253466280670928276581 4514297524927625799051859)
      ·
        refine ⟨6771446287391438698577789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4514297524927625799051859 6771446287391438698577789)
        ·
          refine ⟨2539292357771789511966671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6771446287391438698577789 2539292357771789511966671)
          ·
            refine ⟨3808938536657684267950007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2539292357771789511966671 3808938536657684267950007)
            ·
              refine ⟨5713407804986526401925011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3808938536657684267950007 5713407804986526401925011)
              ·
                refine ⟨8570111707479789602887517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5713407804986526401925011 8570111707479789602887517)
                ·
                  refine ⟨3213791890304921101082819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8570111707479789602887517 3213791890304921101082819)
                  ·
                    refine ⟨4820687835457381651624229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3213791890304921101082819 4820687835457381651624229)
                    ·
                      refine ⟨903878969148259059679543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4820687835457381651624229 903878969148259059679543)
                      ·
                        rfl

theorem cell23_1760298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_1760298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760298 prefixEnd_1760298 := by exact prefixLift 1760298
  have htrace : WordTrace (prefixWord ++ tailWord_1760298) baseStart_1760298 baseEnd_1760298 := by
    simpa [prefixWord, tailWord_1760298, baseEnd_1760298] using wordTrace_append hprefix tailTrace_1760298
  have hstable : (prefixWord ++ tailWord_1760298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760298).length < 2 ^ (prefixWord ++ tailWord_1760298).sum := by decide
  have hdescent : baseEnd_1760298 < baseStart_1760298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760308 : List Nat := [2, 5, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_1760308 : Nat := 118140960795 + 1760308 * 2 ^ 59
def prefixEnd_1760308 : Nat := 4983230072969 + 3 ^ 40 * 1760308 * 2
def baseEnd_1760308 : Nat := 301294701318268006851499

theorem tailTrace_1760308 : CollatzResearch.WordTrace tailWord_1760308 prefixEnd_1760308 301294701318268006851499 := by
  unfold tailWord_1760308
  simp only [CollatzResearch.WordTrace]
  refine ⟨32101853653356113758300789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42802471537808151677734385 32101853653356113758300789)
  ·
    refine ⟨3009548780002135664840699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32101853653356113758300789 3009548780002135664840699)
    ·
      refine ⟨4514323170003203497261049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3009548780002135664840699 4514323170003203497261049)
      ·
        refine ⟨3385742377502402622945787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4514323170003203497261049 3385742377502402622945787)
        ·
          refine ⟨5078613566253603934418681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3385742377502402622945787 5078613566253603934418681)
          ·
            refine ⟨3808960174690202950814011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5078613566253603934418681 3808960174690202950814011)
            ·
              refine ⟨5713440262035304426221017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3808960174690202950814011 5713440262035304426221017)
              ·
                refine ⟨4285080196526478319665763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5713440262035304426221017 4285080196526478319665763)
                ·
                  refine ⟨6427620294789717479498645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4285080196526478319665763 6427620294789717479498645)
                  ·
                    refine ⟨301294701318268006851499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6427620294789717479498645 301294701318268006851499)
                    ·
                      rfl

theorem cell23_1760308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_1760308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760308 prefixEnd_1760308 := by exact prefixLift 1760308
  have htrace : WordTrace (prefixWord ++ tailWord_1760308) baseStart_1760308 baseEnd_1760308 := by
    simpa [prefixWord, tailWord_1760308, baseEnd_1760308] using wordTrace_append hprefix tailTrace_1760308
  have hstable : (prefixWord ++ tailWord_1760308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760308).length < 2 ^ (prefixWord ++ tailWord_1760308).sum := by decide
  have hdescent : baseEnd_1760308 < baseStart_1760308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760318 : List Nat := [4, 2, 1, 3, 1, 1, 3, 1, 1, 1, 5]
def baseStart_1760318 : Nat := 118140960795 + 1760318 * 2 ^ 59
def prefixEnd_1760318 : Nat := 4983230072969 + 3 ^ 40 * 1760318 * 2
def baseEnd_1760318 : Nat := 903889238761348981429451

theorem tailTrace_1760318 : CollatzResearch.WordTrace tailWord_1760318 prefixEnd_1760318 903889238761348981429451 := by
  unfold tailWord_1760318
  simp only [CollatzResearch.WordTrace]
  refine ⟨8025509004584499903058201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42802714691117332816310405 8025509004584499903058201)
  ·
    refine ⟨6019131753438374927293651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8025509004584499903058201 6019131753438374927293651)
    ·
      refine ⟨9028697630157562390940477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6019131753438374927293651 9028697630157562390940477)
      ·
        refine ⟨3385761611309085896602679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9028697630157562390940477 3385761611309085896602679)
        ·
          refine ⟨5078642416963628844904019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3385761611309085896602679 5078642416963628844904019)
          ·
            refine ⟨7617963625445443267356029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5078642416963628844904019 7617963625445443267356029)
            ·
              refine ⟨2856736359542041225258511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7617963625445443267356029 2856736359542041225258511)
              ·
                refine ⟨4285104539313061837887767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2856736359542041225258511 4285104539313061837887767)
                ·
                  refine ⟨6427656808969592756831651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4285104539313061837887767 6427656808969592756831651)
                  ·
                    refine ⟨9641485213454389135247477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6427656808969592756831651 9641485213454389135247477)
                    ·
                      refine ⟨903889238761348981429451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9641485213454389135247477 903889238761348981429451)
                      ·
                        rfl

theorem cell23_1760318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_1760318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760318 prefixEnd_1760318 := by exact prefixLift 1760318
  have htrace : WordTrace (prefixWord ++ tailWord_1760318) baseStart_1760318 baseEnd_1760318 := by
    simpa [prefixWord, tailWord_1760318, baseEnd_1760318] using wordTrace_append hprefix tailTrace_1760318
  have hstable : (prefixWord ++ tailWord_1760318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760318).length < 2 ^ (prefixWord ++ tailWord_1760318).sum := by decide
  have hdescent : baseEnd_1760318 < baseStart_1760318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760321 : List Nat := [1, 2, 5, 1, 4, 10]
def baseStart_1760321 : Nat := 118140960795 + 1760321 * 2 ^ 59
def prefixEnd_1760321 : Nat := 4983230072969 + 3 ^ 40 * 1760321 * 2
def baseEnd_1760321 : Nat := 3719715140754372303259

theorem tailTrace_1760321 : CollatzResearch.WordTrace tailWord_1760321 prefixEnd_1760321 3719715140754372303259 := by
  unfold tailWord_1760321
  simp only [CollatzResearch.WordTrace]
  refine ⟨64204181455665130736824817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42802787637110087157883211 64204181455665130736824817)
  ·
    refine ⟨48153136091748848052618613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64204181455665130736824817 48153136091748848052618613)
    ·
      refine ⟨4514356508601454504932995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48153136091748848052618613 4514356508601454504932995)
      ·
        refine ⟨6771534762902181757399493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4514356508601454504932995 6771534762902181757399493)
        ·
          refine ⟨1269662768044159079512405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6771534762902181757399493 1269662768044159079512405)
          ·
            refine ⟨3719715140754372303259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1269662768044159079512405 3719715140754372303259)
            ·
              rfl

theorem cell23_1760321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 10].length) (baseStart_1760321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760321 prefixEnd_1760321 := by exact prefixLift 1760321
  have htrace : WordTrace (prefixWord ++ tailWord_1760321) baseStart_1760321 baseEnd_1760321 := by
    simpa [prefixWord, tailWord_1760321, baseEnd_1760321] using wordTrace_append hprefix tailTrace_1760321
  have hstable : (prefixWord ++ tailWord_1760321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760321).length < 2 ^ (prefixWord ++ tailWord_1760321).sum := by decide
  have hdescent : baseEnd_1760321 < baseStart_1760321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760326 : List Nat := [6, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3]
def baseStart_1760326 : Nat := 118140960795 + 1760326 * 2 ^ 59
def prefixEnd_1760326 : Nat := 4983230072969 + 3 ^ 40 * 1760326 * 2
def baseEnd_1760326 : Nat := 903893346606584950129415

theorem tailTrace_1760326 : CollatzResearch.WordTrace tailWord_1760326 prefixEnd_1760326 903893346606584950129415 := by
  unfold tailWord_1760326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2006386369395219268461151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42802909213764677727171221 2006386369395219268461151)
  ·
    refine ⟨3009579554092828902691727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2006386369395219268461151 3009579554092828902691727)
    ·
      refine ⟨4514369331139243354037591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3009579554092828902691727 4514369331139243354037591)
      ·
        refine ⟨6771553996708865031056387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4514369331139243354037591 6771553996708865031056387)
        ·
          refine ⟨10157330995063297546584581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6771553996708865031056387 10157330995063297546584581)
          ·
            refine ⟨1904499561574368289984609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10157330995063297546584581 1904499561574368289984609)
            ·
              refine ⟨1428374671180776217488457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1904499561574368289984609 1428374671180776217488457)
              ·
                refine ⟨1071281003385582163116343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1428374671180776217488457 1071281003385582163116343)
                ·
                  refine ⟨1606921505078373244674515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1071281003385582163116343 1606921505078373244674515)
                  ·
                    refine ⟨2410382257617559867011773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1606921505078373244674515 2410382257617559867011773)
                    ·
                      refine ⟨903893346606584950129415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2410382257617559867011773 903893346606584950129415)
                      ·
                        rfl

theorem cell23_1760326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_1760326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760326 prefixEnd_1760326 := by exact prefixLift 1760326
  have htrace : WordTrace (prefixWord ++ tailWord_1760326) baseStart_1760326 baseEnd_1760326 := by
    simpa [prefixWord, tailWord_1760326, baseEnd_1760326] using wordTrace_append hprefix tailTrace_1760326
  have hstable : (prefixWord ++ tailWord_1760326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760326).length < 2 ^ (prefixWord ++ tailWord_1760326).sum := by decide
  have hdescent : baseEnd_1760326 < baseStart_1760326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760334 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 1, 9]
def baseStart_1760334 : Nat := 118140960795 + 1760334 * 2 ^ 59
def prefixEnd_1760334 : Nat := 4983230072969 + 3 ^ 40 * 1760334 * 2
def baseEnd_1760334 : Nat := 301299151483940306276459

theorem tailTrace_1760334 : CollatzResearch.WordTrace tailWord_1760334 prefixEnd_1760334 301299151483940306276459 := by
  unfold tailWord_1760334
  simp only [CollatzResearch.WordTrace]
  refine ⟨8025581950577254244631007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42803103736412022638032037 8025581950577254244631007)
  ·
    refine ⟨12038372925865881366946511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8025581950577254244631007 12038372925865881366946511)
    ·
      refine ⟨18057559388798822050419767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12038372925865881366946511 18057559388798822050419767)
      ·
        refine ⟨27086339083198233075629651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18057559388798822050419767 27086339083198233075629651)
        ·
          refine ⟨40629508624797349613444477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27086339083198233075629651 40629508624797349613444477)
          ·
            refine ⟨15236065734299006105041679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40629508624797349613444477 15236065734299006105041679)
            ·
              refine ⟨22854098601448509157562519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15236065734299006105041679 22854098601448509157562519)
              ·
                refine ⟨34281147902172763736343779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22854098601448509157562519 34281147902172763736343779)
                ·
                  refine ⟨51421721853259145604515669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34281147902172763736343779 51421721853259145604515669)
                  ·
                    refine ⟨301299151483940306276459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 51421721853259145604515669 301299151483940306276459)
                    ·
                      rfl

theorem cell23_1760334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_1760334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760334 prefixEnd_1760334 := by exact prefixLift 1760334
  have htrace : WordTrace (prefixWord ++ tailWord_1760334) baseStart_1760334 baseEnd_1760334 := by
    simpa [prefixWord, tailWord_1760334, baseEnd_1760334] using wordTrace_append hprefix tailTrace_1760334
  have hstable : (prefixWord ++ tailWord_1760334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760334).length < 2 ^ (prefixWord ++ tailWord_1760334).sum := by decide
  have hdescent : baseEnd_1760334 < baseStart_1760334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760348 : List Nat := [2, 2, 4, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_1760348 : Nat := 118140960795 + 1760348 * 2 ^ 59
def prefixEnd_1760348 : Nat := 4983230072969 + 3 ^ 40 * 1760348 * 2
def baseEnd_1760348 : Nat := 903904643180983864054313

theorem tailTrace_1760348 : CollatzResearch.WordTrace tailWord_1760348 prefixEnd_1760348 903904643180983864054313 := by
  unfold tailWord_1760348
  simp only [CollatzResearch.WordTrace]
  refine ⟨32102583113283657174028849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42803444151044876232038465 32102583113283657174028849)
  ·
    refine ⟨24076937334962742880521637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32102583113283657174028849 24076937334962742880521637)
    ·
      refine ⟨4514425750305514290097807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24076937334962742880521637 4514425750305514290097807)
      ·
        refine ⟨6771638625458271435146711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4514425750305514290097807 6771638625458271435146711)
        ·
          refine ⟨10157457938187407152720067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6771638625458271435146711 10157457938187407152720067)
          ·
            refine ⟨15236186907281110729080101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10157457938187407152720067 15236186907281110729080101)
            ·
              refine ⟨2856785045115208261702519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15236186907281110729080101 2856785045115208261702519)
              ·
                refine ⟨4285177567672812392553779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2856785045115208261702519 4285177567672812392553779)
                ·
                  refine ⟨6427766351509218588830669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4285177567672812392553779 6427766351509218588830669)
                  ·
                    refine ⟨2410412381815956970811501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6427766351509218588830669 2410412381815956970811501)
                    ·
                      refine ⟨903904643180983864054313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2410412381815956970811501 903904643180983864054313)
                      ·
                        rfl

theorem cell23_1760348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_1760348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760348 prefixEnd_1760348 := by exact prefixLift 1760348
  have htrace : WordTrace (prefixWord ++ tailWord_1760348) baseStart_1760348 baseEnd_1760348 := by
    simpa [prefixWord, tailWord_1760348, baseEnd_1760348] using wordTrace_append hprefix tailTrace_1760348
  have hstable : (prefixWord ++ tailWord_1760348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760348).length < 2 ^ (prefixWord ++ tailWord_1760348).sum := by decide
  have hdescent : baseEnd_1760348 < baseStart_1760348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760364 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 1, 8]
def baseStart_1760364 : Nat := 118140960795 + 1760364 * 2 ^ 59
def prefixEnd_1760364 : Nat := 4983230072969 + 3 ^ 40 * 1760364 * 2
def baseEnd_1760364 : Nat := 301304286290485267151413

theorem tailTrace_1760364 : CollatzResearch.WordTrace tailWord_1760364 prefixEnd_1760364 301304286290485267151413 := by
  unfold tailWord_1760364
  simp only [CollatzResearch.WordTrace]
  refine ⟨32102874897254674540320073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42803833196339566053760097 32102874897254674540320073)
  ·
    refine ⟨24077156172941005905240055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32102874897254674540320073 24077156172941005905240055)
    ·
      refine ⟨36115734259411508857860083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24077156172941005905240055 36115734259411508857860083)
      ·
        refine ⟨54173601389117263286790125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36115734259411508857860083 54173601389117263286790125)
        ·
          refine ⟨20315100520918973732546297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54173601389117263286790125 20315100520918973732546297)
          ·
            refine ⟨15236325390689230299409723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20315100520918973732546297 15236325390689230299409723)
            ·
              refine ⟨22854488086033845449114585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15236325390689230299409723 22854488086033845449114585)
              ·
                refine ⟨17140866064525384086835939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22854488086033845449114585 17140866064525384086835939)
                ·
                  refine ⟨25711299096788076130253909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17140866064525384086835939 25711299096788076130253909)
                  ·
                    refine ⟨301304286290485267151413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25711299096788076130253909 301304286290485267151413)
                    ·
                      rfl

theorem cell23_1760364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_1760364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760364 prefixEnd_1760364 := by exact prefixLift 1760364
  have htrace : WordTrace (prefixWord ++ tailWord_1760364) baseStart_1760364 baseEnd_1760364 := by
    simpa [prefixWord, tailWord_1760364, baseEnd_1760364] using wordTrace_append hprefix tailTrace_1760364
  have hstable : (prefixWord ++ tailWord_1760364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760364).length < 2 ^ (prefixWord ++ tailWord_1760364).sum := by decide
  have hdescent : baseEnd_1760364 < baseStart_1760364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760441 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 4, 5]
def baseStart_1760441 : Nat := 118140960795 + 1760441 * 2 ^ 59
def prefixEnd_1760441 : Nat := 4983230072969 + 3 ^ 40 * 1760441 * 2
def baseEnd_1760441 : Nat := 301317465627284000063795

theorem tailTrace_1760441 : CollatzResearch.WordTrace tailWord_1760441 prefixEnd_1760441 301317465627284000063795 := by
  unfold tailWord_1760441
  simp only [CollatzResearch.WordTrace]
  refine ⟨64208558215230391231193177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42805705476820260820795451 64208558215230391231193177)
  ·
    refine ⟨48156418661422793423394883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64208558215230391231193177 48156418661422793423394883)
    ·
      refine ⟨72234627992134190135092325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48156418661422793423394883 72234627992134190135092325)
      ·
        refine ⟨13543992748525160650329811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72234627992134190135092325 13543992748525160650329811)
        ·
          refine ⟨20315989122787740975494717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13543992748525160650329811 20315989122787740975494717)
          ·
            refine ⟨7618495921045402865810519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20315989122787740975494717 7618495921045402865810519)
            ·
              refine ⟨11427743881568104298715779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7618495921045402865810519 11427743881568104298715779)
              ·
                refine ⟨17141615822352156448073669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11427743881568104298715779 17141615822352156448073669)
                ·
                  refine ⟨3214052966691029334013813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17141615822352156448073669 3214052966691029334013813)
                  ·
                    refine ⟨301317465627284000063795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3214052966691029334013813 301317465627284000063795)
                    ·
                      rfl

theorem cell23_1760441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 5].length) (baseStart_1760441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760441 prefixEnd_1760441 := by exact prefixLift 1760441
  have htrace : WordTrace (prefixWord ++ tailWord_1760441) baseStart_1760441 baseEnd_1760441 := by
    simpa [prefixWord, tailWord_1760441, baseEnd_1760441] using wordTrace_append hprefix tailTrace_1760441
  have hstable : (prefixWord ++ tailWord_1760441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760441).length < 2 ^ (prefixWord ++ tailWord_1760441).sum := by decide
  have hdescent : baseEnd_1760441 < baseStart_1760441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760505 : List Nat := [1, 2, 1, 3, 1, 1, 5, 4, 1, 4]
def baseStart_1760505 : Nat := 118140960795 + 1760505 * 2 ^ 59
def prefixEnd_1760505 : Nat := 4983230072969 + 3 ^ 40 * 1760505 * 2
def baseEnd_1760505 : Nat := 301328419881246583263697

theorem tailTrace_1760505 : CollatzResearch.WordTrace tailWord_1760505 prefixEnd_1760505 301328419881246583263697 := by
  unfold tailWord_1760505
  simp only [CollatzResearch.WordTrace]
  refine ⟨64210892486998530161522969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42807261657999020107681979 64210892486998530161522969)
  ·
    refine ⟨48158169365248897621142227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64210892486998530161522969 48158169365248897621142227)
    ·
      refine ⟨72237254047873346431713341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48158169365248897621142227 72237254047873346431713341)
      ·
        refine ⟨27088970267952504911892503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72237254047873346431713341 27088970267952504911892503)
        ·
          refine ⟨40633455401928757367838755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27088970267952504911892503 40633455401928757367838755)
          ·
            refine ⟨60950183102893136051758133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40633455401928757367838755 60950183102893136051758133)
            ·
              refine ⟨5714079665896231504852325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60950183102893136051758133 5714079665896231504852325)
              ·
                refine ⟨1071389937355543407159811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5714079665896231504852325 1071389937355543407159811)
                ·
                  refine ⟨1607084906033315110739717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1071389937355543407159811 1607084906033315110739717)
                  ·
                    refine ⟨301328419881246583263697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1607084906033315110739717 301328419881246583263697)
                    ·
                      rfl

theorem cell23_1760505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4, 1, 4].length) (baseStart_1760505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760505 prefixEnd_1760505 := by exact prefixLift 1760505
  have htrace : WordTrace (prefixWord ++ tailWord_1760505) baseStart_1760505 baseEnd_1760505 := by
    simpa [prefixWord, tailWord_1760505, baseEnd_1760505] using wordTrace_append hprefix tailTrace_1760505
  have hstable : (prefixWord ++ tailWord_1760505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760505).length < 2 ^ (prefixWord ++ tailWord_1760505).sum := by decide
  have hdescent : baseEnd_1760505 < baseStart_1760505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760562 : List Nat := [3, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3]
def baseStart_1760562 : Nat := 118140960795 + 1760562 * 2 ^ 59
def prefixEnd_1760562 : Nat := 4983230072969 + 3 ^ 40 * 1760562 * 2
def baseEnd_1760562 : Nat := 904014528041046026778329

theorem tailTrace_1760562 : CollatzResearch.WordTrace tailWord_1760562 prefixEnd_1760562 904014528041046026778329 := by
  unfold tailWord_1760562
  simp only [CollatzResearch.WordTrace]
  refine ⟨16053242861948007224086985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42808647631861352597565293 16053242861948007224086985)
  ·
    refine ⟨12039932146461005418065239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16053242861948007224086985 12039932146461005418065239)
    ·
      refine ⟨18059898219691508127097859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12039932146461005418065239 18059898219691508127097859)
      ·
        refine ⟨27089847329537262190646789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18059898219691508127097859 27089847329537262190646789)
        ·
          refine ⟨5079346374288236660746273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27089847329537262190646789 5079346374288236660746273)
          ·
            refine ⟨3809509780716177495559705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5079346374288236660746273 3809509780716177495559705)
            ·
              refine ⟨2857132335537133121669779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3809509780716177495559705 2857132335537133121669779)
              ·
                refine ⟨4285698503305699682504669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2857132335537133121669779 4285698503305699682504669)
                ·
                  refine ⟨1607136938739637380939251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4285698503305699682504669 1607136938739637380939251)
                  ·
                    refine ⟨2410705408109456071408877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1607136938739637380939251 2410705408109456071408877)
                    ·
                      refine ⟨904014528041046026778329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2410705408109456071408877 904014528041046026778329)
                      ·
                        rfl

theorem cell23_1760562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_1760562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760562 prefixEnd_1760562 := by exact prefixLift 1760562
  have htrace : WordTrace (prefixWord ++ tailWord_1760562) baseStart_1760562 baseEnd_1760562 := by
    simpa [prefixWord, tailWord_1760562, baseEnd_1760562] using wordTrace_append hprefix tailTrace_1760562
  have hstable : (prefixWord ++ tailWord_1760562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760562).length < 2 ^ (prefixWord ++ tailWord_1760562).sum := by decide
  have hdescent : baseEnd_1760562 < baseStart_1760562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760608 : List Nat := [2, 1, 1, 3, 4, 3, 9]
def baseStart_1760608 : Nat := 118140960795 + 1760608 * 2 ^ 59
def prefixEnd_1760608 : Nat := 4983230072969 + 3 ^ 40 * 1760608 * 2
def baseEnd_1760608 : Nat := 11160964791989541318557

theorem tailTrace_1760608 : CollatzResearch.WordTrace tailWord_1760608 prefixEnd_1760608 11160964791989541318557 := by
  unfold tailWord_1760608
  simp only [CollatzResearch.WordTrace]
  refine ⟨32107324602812689376261239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42809766137083585835014985 32107324602812689376261239)
  ·
    refine ⟨48160986904219034064391859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32107324602812689376261239 48160986904219034064391859)
    ·
      refine ⟨72241480356328551096587789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48160986904219034064391859 72241480356328551096587789)
      ·
        refine ⟨27090555133623206661220421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72241480356328551096587789 27090555133623206661220421)
        ·
          refine ⟨5079479087554351248978829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27090555133623206661220421 5079479087554351248978829)
          ·
            refine ⟨1904804657832881718367061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5079479087554351248978829 1904804657832881718367061)
            ·
              refine ⟨11160964791989541318557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1904804657832881718367061 11160964791989541318557)
              ·
                rfl

theorem cell23_1760608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 9].length) (baseStart_1760608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760608 prefixEnd_1760608 := by exact prefixLift 1760608
  have htrace : WordTrace (prefixWord ++ tailWord_1760608) baseStart_1760608 baseEnd_1760608 := by
    simpa [prefixWord, tailWord_1760608, baseEnd_1760608] using wordTrace_append hprefix tailTrace_1760608
  have hstable : (prefixWord ++ tailWord_1760608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760608).length < 2 ^ (prefixWord ++ tailWord_1760608).sum := by decide
  have hdescent : baseEnd_1760608 < baseStart_1760608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760669 : List Nat := [1, 4, 2, 1, 3, 2, 2, 2, 2, 1, 3]
def baseStart_1760669 : Nat := 118140960795 + 1760669 * 2 ^ 59
def prefixEnd_1760669 : Nat := 4983230072969 + 3 ^ 40 * 1760669 * 2
def baseEnd_1760669 : Nat := 904069470471077108140337

theorem tailTrace_1760669 : CollatzResearch.WordTrace tailWord_1760669 prefixEnd_1760669 904069470471077108140337 := by
  unfold tailWord_1760669
  simp only [CollatzResearch.WordTrace]
  refine ⟨64216874058404386170493061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42811249372269590780328707 64216874058404386170493061)
  ·
    refine ⟨12040663885950822406967449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64216874058404386170493061 12040663885950822406967449)
    ·
      refine ⟨9030497914463116805225587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12040663885950822406967449 9030497914463116805225587)
      ·
        refine ⟨13545746871694675207838381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9030497914463116805225587 13545746871694675207838381)
        ·
          refine ⟨5079655076885503202939393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13545746871694675207838381 5079655076885503202939393)
          ·
            refine ⟨3809741307664127402204545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5079655076885503202939393 3809741307664127402204545)
            ·
              refine ⟨2857305980748095551653409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3809741307664127402204545 2857305980748095551653409)
              ·
                refine ⟨2142979485561071663740057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2857305980748095551653409 2142979485561071663740057)
                ·
                  refine ⟨1607234614170803747805043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2142979485561071663740057 1607234614170803747805043)
                  ·
                    refine ⟨2410851921256205621707565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1607234614170803747805043 2410851921256205621707565)
                    ·
                      refine ⟨904069470471077108140337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2410851921256205621707565 904069470471077108140337)
                      ·
                        rfl

theorem cell23_1760669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_1760669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760669 prefixEnd_1760669 := by exact prefixLift 1760669
  have htrace : WordTrace (prefixWord ++ tailWord_1760669) baseStart_1760669 baseEnd_1760669 := by
    simpa [prefixWord, tailWord_1760669, baseEnd_1760669] using wordTrace_append hprefix tailTrace_1760669
  have hstable : (prefixWord ++ tailWord_1760669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760669).length < 2 ^ (prefixWord ++ tailWord_1760669).sum := by decide
  have hdescent : baseEnd_1760669 < baseStart_1760669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760675 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 3, 4, 2]
def baseStart_1760675 : Nat := 118140960795 + 1760675 * 2 ^ 59
def prefixEnd_1760675 : Nat := 4983230072969 + 3 ^ 40 * 1760675 * 2
def baseEnd_1760675 : Nat := 904072551355004084665309

theorem tailTrace_1760675 : CollatzResearch.WordTrace tailWord_1760675 prefixEnd_1760675 904072551355004084665309 := by
  unfold tailWord_1760675
  simp only [CollatzResearch.WordTrace]
  refine ⟨64217092896382649195211479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42811395264255099463474319 64217092896382649195211479)
  ·
    refine ⟨96325639344573973792817219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64217092896382649195211479 96325639344573973792817219)
    ·
      refine ⟨144488459016860960689225829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96325639344573973792817219 144488459016860960689225829)
      ·
        refine ⟨27091586065661430129229843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144488459016860960689225829 27091586065661430129229843)
        ·
          refine ⟨40637379098492145193844765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27091586065661430129229843 40637379098492145193844765)
          ·
            refine ⟨15239017161934554447691787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40637379098492145193844765 15239017161934554447691787)
            ·
              refine ⟨22858525742901831671537681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15239017161934554447691787 22858525742901831671537681)
              ·
                refine ⟨17143894307176373753653261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22858525742901831671537681 17143894307176373753653261)
                ·
                  refine ⟨6428960365191140157619973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17143894307176373753653261 6428960365191140157619973)
                  ·
                    refine ⟨1205430068473338779553745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6428960365191140157619973 1205430068473338779553745)
                    ·
                      refine ⟨904072551355004084665309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1205430068473338779553745 904072551355004084665309)
                      ·
                        rfl

theorem cell23_1760675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 4, 2].length) (baseStart_1760675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760675 prefixEnd_1760675 := by exact prefixLift 1760675
  have htrace : WordTrace (prefixWord ++ tailWord_1760675) baseStart_1760675 baseEnd_1760675 := by
    simpa [prefixWord, tailWord_1760675, baseEnd_1760675] using wordTrace_append hprefix tailTrace_1760675
  have hstable : (prefixWord ++ tailWord_1760675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760675).length < 2 ^ (prefixWord ++ tailWord_1760675).sum := by decide
  have hdescent : baseEnd_1760675 < baseStart_1760675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760685 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 1, 8]
def baseStart_1760685 : Nat := 118140960795 + 1760685 * 2 ^ 59
def prefixEnd_1760685 : Nat := 4983230072969 + 3 ^ 40 * 1760685 * 2
def baseEnd_1760685 : Nat := 301359228720516348513421

theorem tailTrace_1760685 : CollatzResearch.WordTrace tailWord_1760685 prefixEnd_1760685 301359228720516348513421 := by
  unfold tailWord_1760685
  simp only [CollatzResearch.WordTrace]
  refine ⟨64217457626346420903075509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42811638417564280602050339 64217457626346420903075509)
  ·
    refine ⟨6020386652469976959663329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64217457626346420903075509 6020386652469976959663329)
    ·
      refine ⟨4515289989352482719747497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6020386652469976959663329 4515289989352482719747497)
      ·
        refine ⟨3386467492014362039810623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4515289989352482719747497 3386467492014362039810623)
        ·
          refine ⟨5079701238021543059715935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3386467492014362039810623 5079701238021543059715935)
          ·
            refine ⟨7619551857032314589573903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5079701238021543059715935 7619551857032314589573903)
            ·
              refine ⟨11429327785548471884360855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7619551857032314589573903 11429327785548471884360855)
              ·
                refine ⟨17143991678322707826541283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11429327785548471884360855 17143991678322707826541283)
                ·
                  refine ⟨25715987517484061739811925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17143991678322707826541283 25715987517484061739811925)
                  ·
                    refine ⟨301359228720516348513421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25715987517484061739811925 301359228720516348513421)
                    ·
                      rfl

theorem cell23_1760685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_1760685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760685 prefixEnd_1760685 := by exact prefixLift 1760685
  have htrace : WordTrace (prefixWord ++ tailWord_1760685) baseStart_1760685 baseEnd_1760685 := by
    simpa [prefixWord, tailWord_1760685, baseEnd_1760685] using wordTrace_append hprefix tailTrace_1760685
  have hstable : (prefixWord ++ tailWord_1760685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760685).length < 2 ^ (prefixWord ++ tailWord_1760685).sum := by decide
  have hdescent : baseEnd_1760685 < baseStart_1760685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760715 : List Nat := [1, 1, 1, 1, 3, 3, 3, 5, 5]
def baseStart_1760715 : Nat := 118140960795 + 1760715 * 2 ^ 59
def prefixEnd_1760715 : Nat := 4983230072969 + 3 ^ 40 * 1760715 * 2
def baseEnd_1760715 : Nat := 100454787842353769796125

theorem tailTrace_1760715 : CollatzResearch.WordTrace tailWord_1760715 prefixEnd_1760715 100454787842353769796125 := by
  unfold tailWord_1760715
  simp only [CollatzResearch.WordTrace]
  refine ⟨64218551816237736026667599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42812367877491824017778399 64218551816237736026667599)
  ·
    refine ⟨96327827724356604040001399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64218551816237736026667599 96327827724356604040001399)
    ·
      refine ⟨144491741586534906060002099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96327827724356604040001399 144491741586534906060002099)
      ·
        refine ⟨216737612379802359090003149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144491741586534906060002099 216737612379802359090003149)
        ·
          refine ⟨81276604642425884658751181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216737612379802359090003149 81276604642425884658751181)
          ·
            refine ⟨30478726740909706747031693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81276604642425884658751181 30478726740909706747031693)
            ·
              refine ⟨11429522527841140030136885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30478726740909706747031693 11429522527841140030136885)
              ·
                refine ⟨1071517736985106877825333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11429522527841140030136885 1071517736985106877825333)
                ·
                  refine ⟨100454787842353769796125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1071517736985106877825333 100454787842353769796125)
                  ·
                    rfl

theorem cell23_1760715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5, 5].length) (baseStart_1760715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760715 prefixEnd_1760715 := by exact prefixLift 1760715
  have htrace : WordTrace (prefixWord ++ tailWord_1760715) baseStart_1760715 baseEnd_1760715 := by
    simpa [prefixWord, tailWord_1760715, baseEnd_1760715] using wordTrace_append hprefix tailTrace_1760715
  have hstable : (prefixWord ++ tailWord_1760715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760715).length < 2 ^ (prefixWord ++ tailWord_1760715).sum := by decide
  have hdescent : baseEnd_1760715 < baseStart_1760715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760725 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 4, 3, 3]
def baseStart_1760725 : Nat := 118140960795 + 1760725 * 2 ^ 59
def prefixEnd_1760725 : Nat := 4983230072969 + 3 ^ 40 * 1760725 * 2
def baseEnd_1760725 : Nat := 904098225387728889040079

theorem tailTrace_1760725 : CollatzResearch.WordTrace tailWord_1760725 prefixEnd_1760725 904098225387728889040079 := by
  unfold tailWord_1760725
  simp only [CollatzResearch.WordTrace]
  refine ⟨64218916546201507734531629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42812611030801005156354419 64218916546201507734531629)
  ·
    refine ⟨24082093704825565400449361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64218916546201507734531629 24082093704825565400449361)
    ·
      refine ⟨18061570278619174050337021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24082093704825565400449361 18061570278619174050337021)
      ·
        refine ⟨6773088854482190268876383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18061570278619174050337021 6773088854482190268876383)
        ·
          refine ⟨10159633281723285403314575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6773088854482190268876383 10159633281723285403314575)
          ·
            refine ⟨15239449922584928104971863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10159633281723285403314575 15239449922584928104971863)
            ·
              refine ⟨22859174883877392157457795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15239449922584928104971863 22859174883877392157457795)
              ·
                refine ⟨34288762325816088236186693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22859174883877392157457795 34288762325816088236186693)
                ·
                  refine ⟨6429142936090516544285005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34288762325816088236186693 6429142936090516544285005)
                  ·
                    refine ⟨2410928601033943704106877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6429142936090516544285005 2410928601033943704106877)
                    ·
                      refine ⟨904098225387728889040079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2410928601033943704106877 904098225387728889040079)
                      ·
                        rfl

theorem cell23_1760725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_1760725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760725 prefixEnd_1760725 := by exact prefixLift 1760725
  have htrace : WordTrace (prefixWord ++ tailWord_1760725) baseStart_1760725 baseEnd_1760725 := by
    simpa [prefixWord, tailWord_1760725, baseEnd_1760725] using wordTrace_append hprefix tailTrace_1760725
  have hstable : (prefixWord ++ tailWord_1760725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760725).length < 2 ^ (prefixWord ++ tailWord_1760725).sum := by decide
  have hdescent : baseEnd_1760725 < baseStart_1760725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760726 : List Nat := [5, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2]
def baseStart_1760726 : Nat := 118140960795 + 1760726 * 2 ^ 59
def prefixEnd_1760726 : Nat := 4983230072969 + 3 ^ 40 * 1760726 * 2
def baseEnd_1760726 : Nat := 904098738868383385127575

theorem tailTrace_1760726 : CollatzResearch.WordTrace tailWord_1760726 prefixEnd_1760726 904098738868383385127575 := by
  unfold tailWord_1760726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4013684563699867806582377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42812635346131923270212021 4013684563699867806582377)
  ·
    refine ⟨3010263422774900854936783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4013684563699867806582377 3010263422774900854936783)
    ·
      refine ⟨4515395134162351282405175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3010263422774900854936783 4515395134162351282405175)
      ·
        refine ⟨6773092701243526923607763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4515395134162351282405175 6773092701243526923607763)
        ·
          refine ⟨10159639051865290385411645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6773092701243526923607763 10159639051865290385411645)
          ·
            refine ⟨3809864644449483894529367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10159639051865290385411645 3809864644449483894529367)
            ·
              refine ⟨5714796966674225841794051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3809864644449483894529367 5714796966674225841794051)
              ·
                refine ⟨8572195450011338762691077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5714796966674225841794051 8572195450011338762691077)
                ·
                  refine ⟨1607286646877126018004577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8572195450011338762691077 1607286646877126018004577)
                  ·
                    refine ⟨1205464985157844513503433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1607286646877126018004577 1205464985157844513503433)
                    ·
                      refine ⟨904098738868383385127575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1205464985157844513503433 904098738868383385127575)
                      ·
                        rfl

theorem cell23_1760726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_1760726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760726 prefixEnd_1760726 := by exact prefixLift 1760726
  have htrace : WordTrace (prefixWord ++ tailWord_1760726) baseStart_1760726 baseEnd_1760726 := by
    simpa [prefixWord, tailWord_1760726, baseEnd_1760726] using wordTrace_append hprefix tailTrace_1760726
  have hstable : (prefixWord ++ tailWord_1760726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760726).length < 2 ^ (prefixWord ++ tailWord_1760726).sum := by decide
  have hdescent : baseEnd_1760726 < baseStart_1760726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760765 : List Nat := [1, 4, 1, 1, 1, 4, 2, 1, 1, 3, 4]
def baseStart_1760765 : Nat := 118140960795 + 1760765 * 2 ^ 59
def prefixEnd_1760765 : Nat := 4983230072969 + 3 ^ 40 * 1760765 * 2
def baseEnd_1760765 : Nat := 904118764613908732539895

theorem tailTrace_1760765 : CollatzResearch.WordTrace tailWord_1760765 prefixEnd_1760765 904118764613908732539895 := by
  unfold tailWord_1760765
  simp only [CollatzResearch.WordTrace]
  refine ⟨64220375466056594565987749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42813583644037729710658499 64220375466056594565987749)
  ·
    refine ⟨12041320399885611481122703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64220375466056594565987749 12041320399885611481122703)
    ·
      refine ⟨18061980599828417221684055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12041320399885611481122703 18061980599828417221684055)
      ·
        refine ⟨27092970899742625832526083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18061980599828417221684055 27092970899742625832526083)
        ·
          refine ⟨40639456349613938748789125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27092970899742625832526083 40639456349613938748789125)
          ·
            refine ⟨7619898065552613515397961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40639456349613938748789125 7619898065552613515397961)
            ·
              refine ⟨5714923549164460136548471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7619898065552613515397961 5714923549164460136548471)
              ·
                refine ⟨8572385323746690204822707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5714923549164460136548471 8572385323746690204822707)
                ·
                  refine ⟨12858577985620035307234061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8572385323746690204822707 12858577985620035307234061)
                  ·
                    refine ⟨4821966744607513240212773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12858577985620035307234061 4821966744607513240212773)
                    ·
                      refine ⟨904118764613908732539895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4821966744607513240212773 904118764613908732539895)
                      ·
                        rfl

theorem cell23_1760765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_1760765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760765 prefixEnd_1760765 := by exact prefixLift 1760765
  have htrace : WordTrace (prefixWord ++ tailWord_1760765) baseStart_1760765 baseEnd_1760765 := by
    simpa [prefixWord, tailWord_1760765, baseEnd_1760765] using wordTrace_append hprefix tailTrace_1760765
  have hstable : (prefixWord ++ tailWord_1760765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760765).length < 2 ^ (prefixWord ++ tailWord_1760765).sum := by decide
  have hdescent : baseEnd_1760765 < baseStart_1760765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760882 : List Nat := [3, 2, 1, 2, 3, 1, 2, 2, 1, 6]
def baseStart_1760882 : Nat := 118140960795 + 1760882 * 2 ^ 59
def prefixEnd_1760882 : Nat := 4983230072969 + 3 ^ 40 * 1760882 * 2
def baseEnd_1760882 : Nat := 301392947283494924925619

theorem tailTrace_1760882 : CollatzResearch.WordTrace tailWord_1760882 prefixEnd_1760882 301392947283494924925619 := by
  unfold tailWord_1760882
  simp only [CollatzResearch.WordTrace]
  refine ⟨16056160701658180886999225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42816428537755149031997933 16056160701658180886999225)
  ·
    refine ⟨12042120526243635665249419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16056160701658180886999225 12042120526243635665249419)
    ·
      refine ⟨18063180789365453497874129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12042120526243635665249419 18063180789365453497874129)
      ·
        refine ⟨13547385592024090123405597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18063180789365453497874129 13547385592024090123405597)
        ·
          refine ⟨5080269597009033796277099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13547385592024090123405597 5080269597009033796277099)
          ·
            refine ⟨7620404395513550694415649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5080269597009033796277099 7620404395513550694415649)
            ·
              refine ⟨5715303296635163020811737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7620404395513550694415649 5715303296635163020811737)
              ·
                refine ⟨4286477472476372265608803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5715303296635163020811737 4286477472476372265608803)
                ·
                  refine ⟨6429716208714558398413205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4286477472476372265608803 6429716208714558398413205)
                  ·
                    refine ⟨301392947283494924925619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6429716208714558398413205 301392947283494924925619)
                    ·
                      rfl

theorem cell23_1760882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_1760882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760882 prefixEnd_1760882 := by exact prefixLift 1760882
  have htrace : WordTrace (prefixWord ++ tailWord_1760882) baseStart_1760882 baseEnd_1760882 := by
    simpa [prefixWord, tailWord_1760882, baseEnd_1760882] using wordTrace_append hprefix tailTrace_1760882
  have hstable : (prefixWord ++ tailWord_1760882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760882).length < 2 ^ (prefixWord ++ tailWord_1760882).sum := by decide
  have hdescent : baseEnd_1760882 < baseStart_1760882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760886 : List Nat := [5, 1, 1, 2, 2, 1, 4, 1, 1, 5]
def baseStart_1760886 : Nat := 118140960795 + 1760886 * 2 ^ 59
def prefixEnd_1760886 : Nat := 4983230072969 + 3 ^ 40 * 1760886 * 2
def baseEnd_1760886 : Nat := 301393631924367586375613

theorem tailTrace_1760886 : CollatzResearch.WordTrace tailWord_1760886 prefixEnd_1760886 301393631924367586375613 := by
  unfold tailWord_1760886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4014049293663639514446407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42816525799078821487428341 4014049293663639514446407)
  ·
    refine ⟨6021073940495459271669611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4014049293663639514446407 6021073940495459271669611)
    ·
      refine ⟨9031610910743188907504417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6021073940495459271669611 9031610910743188907504417)
      ·
        refine ⟨6773708183057391680628313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9031610910743188907504417 6773708183057391680628313)
        ·
          refine ⟨5080281137293043760471235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6773708183057391680628313 5080281137293043760471235)
          ·
            refine ⟨7620421705939565640706853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5080281137293043760471235 7620421705939565640706853)
            ·
              refine ⟨1428829069863668557632535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7620421705939565640706853 1428829069863668557632535)
              ·
                refine ⟨2143243604795502836448803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1428829069863668557632535 2143243604795502836448803)
                ·
                  refine ⟨3214865407193254254673205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2143243604795502836448803 3214865407193254254673205)
                  ·
                    refine ⟨301393631924367586375613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3214865407193254254673205 301393631924367586375613)
                    ·
                      rfl

theorem cell23_1760886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_1760886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760886 prefixEnd_1760886 := by exact prefixLift 1760886
  have htrace : WordTrace (prefixWord ++ tailWord_1760886) baseStart_1760886 baseEnd_1760886 := by
    simpa [prefixWord, tailWord_1760886, baseEnd_1760886] using wordTrace_append hprefix tailTrace_1760886
  have hstable : (prefixWord ++ tailWord_1760886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760886).length < 2 ^ (prefixWord ++ tailWord_1760886).sum := by decide
  have hdescent : baseEnd_1760886 < baseStart_1760886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760889 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 5, 2, 2]
def baseStart_1760889 : Nat := 118140960795 + 1760889 * 2 ^ 59
def prefixEnd_1760889 : Nat := 4983230072969 + 3 ^ 40 * 1760889 * 2
def baseEnd_1760889 : Nat := 904182436215066247389325

theorem tailTrace_1760889 : CollatzResearch.WordTrace tailWord_1760889 prefixEnd_1760889 904182436215066247389325 := by
  unfold tailWord_1760889
  simp only [CollatzResearch.WordTrace]
  refine ⟨64224898117607363743501721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42816598745071575829001147 64224898117607363743501721)
  ·
    refine ⟨48168673588205522807626291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64224898117607363743501721 48168673588205522807626291)
    ·
      refine ⟨72253010382308284211439437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48168673588205522807626291 72253010382308284211439437)
      ·
        refine ⟨27094878893365606579289789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72253010382308284211439437 27094878893365606579289789)
        ·
          refine ⟨10160579585012102467233671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27094878893365606579289789 10160579585012102467233671)
          ·
            refine ⟨15240869377518153700850507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10160579585012102467233671 15240869377518153700850507)
            ·
              refine ⟨22861304066277230551275761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15240869377518153700850507 22861304066277230551275761)
              ·
                refine ⟨17145978049707922913456821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22861304066277230551275761 17145978049707922913456821)
                ·
                  refine ⟨1607435442160117773136577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17145978049707922913456821 1607435442160117773136577)
                  ·
                    refine ⟨1205576581620088329852433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1607435442160117773136577 1205576581620088329852433)
                    ·
                      refine ⟨904182436215066247389325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1205576581620088329852433 904182436215066247389325)
                      ·
                        rfl

theorem cell23_1760889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5, 2, 2].length) (baseStart_1760889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760889 prefixEnd_1760889 := by exact prefixLift 1760889
  have htrace : WordTrace (prefixWord ++ tailWord_1760889) baseStart_1760889 baseEnd_1760889 := by
    simpa [prefixWord, tailWord_1760889, baseEnd_1760889] using wordTrace_append hprefix tailTrace_1760889
  have hstable : (prefixWord ++ tailWord_1760889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760889).length < 2 ^ (prefixWord ++ tailWord_1760889).sum := by decide
  have hdescent : baseEnd_1760889 < baseStart_1760889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760906 : List Nat := [3, 1, 2, 3, 2, 1, 1, 3, 3, 2, 2]
def baseStart_1760906 : Nat := 118140960795 + 1760906 * 2 ^ 59
def prefixEnd_1760906 : Nat := 4983230072969 + 3 ^ 40 * 1760906 * 2
def baseEnd_1760906 : Nat := 904191165386192680876747

theorem tailTrace_1760906 : CollatzResearch.WordTrace tailWord_1760906 prefixEnd_1760906 904191165386192680876747 := by
  unfold tailWord_1760906
  simp only [CollatzResearch.WordTrace]
  refine ⟨16056379539636443911717643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42817012105697183764580381 16056379539636443911717643)
  ·
    refine ⟨24084569309454665867576465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16056379539636443911717643 24084569309454665867576465)
    ·
      refine ⟨18063426982090999400682349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24084569309454665867576465 18063426982090999400682349)
      ·
        refine ⟨6773785118284124775255881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18063426982090999400682349 6773785118284124775255881)
        ·
          refine ⟨5080338838713093581441911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6773785118284124775255881 5080338838713093581441911)
          ·
            refine ⟨7620508258069640372162867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5080338838713093581441911 7620508258069640372162867)
            ·
              refine ⟨11430762387104460558244301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7620508258069640372162867 11430762387104460558244301)
              ·
                refine ⟨4286535895164172709341613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11430762387104460558244301 4286535895164172709341613)
                ·
                  refine ⟨1607450960686564766003105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4286535895164172709341613 1607450960686564766003105)
                  ·
                    refine ⟨1205588220514923574502329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1607450960686564766003105 1205588220514923574502329)
                    ·
                      refine ⟨904191165386192680876747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1205588220514923574502329 904191165386192680876747)
                      ·
                        rfl

theorem cell23_1760906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_1760906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760906 prefixEnd_1760906 := by exact prefixLift 1760906
  have htrace : WordTrace (prefixWord ++ tailWord_1760906) baseStart_1760906 baseEnd_1760906 := by
    simpa [prefixWord, tailWord_1760906, baseEnd_1760906] using wordTrace_append hprefix tailTrace_1760906
  have hstable : (prefixWord ++ tailWord_1760906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760906).length < 2 ^ (prefixWord ++ tailWord_1760906).sum := by decide
  have hdescent : baseEnd_1760906 < baseStart_1760906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760916 : List Nat := [2, 4, 2, 2, 2, 2, 1, 1, 1, 6]
def baseStart_1760916 : Nat := 118140960795 + 1760916 * 2 ^ 59
def prefixEnd_1760916 : Nat := 4983230072969 + 3 ^ 40 * 1760916 * 2
def baseEnd_1760916 : Nat := 301398766730912547250567

theorem tailTrace_1760916 : CollatzResearch.WordTrace tailWord_1760916 prefixEnd_1760916 301398766730912547250567 := by
  unfold tailWord_1760916
  simp only [CollatzResearch.WordTrace]
  refine ⟨32112941444254773677367301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42817255259006364903156401 32112941444254773677367301)
  ·
    refine ⟨6021176520797770064506369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32112941444254773677367301 6021176520797770064506369)
    ·
      refine ⟨4515882390598327548379777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6021176520797770064506369 4515882390598327548379777)
      ·
        refine ⟨3386911792948745661284833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4515882390598327548379777 3386911792948745661284833)
        ·
          refine ⟨2540183844711559245963625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3386911792948745661284833 2540183844711559245963625)
          ·
            refine ⟨1905137883533669434472719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2540183844711559245963625 1905137883533669434472719)
            ·
              refine ⟨2857706825300504151709079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1905137883533669434472719 2857706825300504151709079)
              ·
                refine ⟨4286560237950756227563619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2857706825300504151709079 4286560237950756227563619)
                ·
                  refine ⟨6429840356926134341345429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4286560237950756227563619 6429840356926134341345429)
                  ·
                    refine ⟨301398766730912547250567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6429840356926134341345429 301398766730912547250567)
                    ·
                      rfl

theorem cell23_1760916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_1760916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760916 prefixEnd_1760916 := by exact prefixLift 1760916
  have htrace : WordTrace (prefixWord ++ tailWord_1760916) baseStart_1760916 baseEnd_1760916 := by
    simpa [prefixWord, tailWord_1760916, baseEnd_1760916] using wordTrace_append hprefix tailTrace_1760916
  have hstable : (prefixWord ++ tailWord_1760916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760916).length < 2 ^ (prefixWord ++ tailWord_1760916).sum := by decide
  have hdescent : baseEnd_1760916 < baseStart_1760916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760919 : List Nat := [1, 1, 3, 3, 2, 4, 1, 1, 1, 2, 4]
def baseStart_1760919 : Nat := 118140960795 + 1760919 * 2 ^ 59
def prefixEnd_1760919 : Nat := 4983230072969 + 3 ^ 40 * 1760919 * 2
def baseEnd_1760919 : Nat := 904197840634701130014187

theorem tailTrace_1760919 : CollatzResearch.WordTrace tailWord_1760919 prefixEnd_1760919 904197840634701130014187 := by
  unfold tailWord_1760919
  simp only [CollatzResearch.WordTrace]
  refine ⟨64225992307498678867093811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42817328204999119244729207 64225992307498678867093811)
  ·
    refine ⟨96338988461248018300640717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64225992307498678867093811 96338988461248018300640717)
    ·
      refine ⟨36127120672968006862740269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96338988461248018300640717 36127120672968006862740269)
      ·
        refine ⟨13547670252363002573527601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36127120672968006862740269 13547670252363002573527601)
        ·
          refine ⟨10160752689272251930145701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13547670252363002573527601 10160752689272251930145701)
          ·
            refine ⟨1905141129238547236902319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10160752689272251930145701 1905141129238547236902319)
            ·
              refine ⟨2857711693857820855353479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1905141129238547236902319 2857711693857820855353479)
              ·
                refine ⟨4286567540786731283030219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2857711693857820855353479 4286567540786731283030219)
                ·
                  refine ⟨6429851311180096924545329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4286567540786731283030219 6429851311180096924545329)
                  ·
                    refine ⟨4822388483385072693408997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6429851311180096924545329 4822388483385072693408997)
                    ·
                      refine ⟨904197840634701130014187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4822388483385072693408997 904197840634701130014187)
                      ·
                        rfl

theorem cell23_1760919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_1760919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760919 prefixEnd_1760919 := by exact prefixLift 1760919
  have htrace : WordTrace (prefixWord ++ tailWord_1760919) baseStart_1760919 baseEnd_1760919 := by
    simpa [prefixWord, tailWord_1760919, baseEnd_1760919] using wordTrace_append hprefix tailTrace_1760919
  have hstable : (prefixWord ++ tailWord_1760919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760919).length < 2 ^ (prefixWord ++ tailWord_1760919).sum := by decide
  have hdescent : baseEnd_1760919 < baseStart_1760919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760926 : List Nat := [4, 3, 1, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_1760926 : Nat := 118140960795 + 1760926 * 2 ^ 59
def prefixEnd_1760926 : Nat := 4983230072969 + 3 ^ 40 * 1760926 * 2
def baseEnd_1760926 : Nat := 904201434999282602626655

theorem tailTrace_1760926 : CollatzResearch.WordTrace tailWord_1760926 prefixEnd_1760926 904201434999282602626655 := by
  unfold tailWord_1760926
  simp only [CollatzResearch.WordTrace]
  refine ⟨8028280952309164882824829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42817498412315546041732421 8028280952309164882824829)
  ·
    refine ⟨3010605357115936831059311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8028280952309164882824829 3010605357115936831059311)
    ·
      refine ⟨4515908035673905246588967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3010605357115936831059311 4515908035673905246588967)
      ·
        refine ⟨6773862053510857869883451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4515908035673905246588967 6773862053510857869883451)
        ·
          refine ⟨10160793080266286804825177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6773862053510857869883451 10160793080266286804825177)
          ·
            refine ⟨7620594810199715103618883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10160793080266286804825177 7620594810199715103618883)
            ·
              refine ⟨11430892215299572655428325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7620594810199715103618883 11430892215299572655428325)
              ·
                refine ⟨2143292290368669872892811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11430892215299572655428325 2143292290368669872892811)
                ·
                  refine ⟨3214938435553004809339217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2143292290368669872892811 3214938435553004809339217)
                  ·
                    refine ⟨2411203826664753607004413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3214938435553004809339217 2411203826664753607004413)
                    ·
                      refine ⟨904201434999282602626655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2411203826664753607004413 904201434999282602626655)
                      ·
                        rfl

theorem cell23_1760926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_1760926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760926 prefixEnd_1760926 := by exact prefixLift 1760926
  have htrace : WordTrace (prefixWord ++ tailWord_1760926) baseStart_1760926 baseEnd_1760926 := by
    simpa [prefixWord, tailWord_1760926, baseEnd_1760926] using wordTrace_append hprefix tailTrace_1760926
  have hstable : (prefixWord ++ tailWord_1760926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760926).length < 2 ^ (prefixWord ++ tailWord_1760926).sum := by decide
  have hdescent : baseEnd_1760926 < baseStart_1760926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760929 : List Nat := [1, 2, 3, 3, 2, 3, 2, 7]
def baseStart_1760929 : Nat := 118140960795 + 1760929 * 2 ^ 59
def prefixEnd_1760929 : Nat := 4983230072969 + 3 ^ 40 * 1760929 * 2
def baseEnd_1760929 : Nat := 33488999090416521884783

theorem tailTrace_1760929 : CollatzResearch.WordTrace tailWord_1760929 prefixEnd_1760929 33488999090416521884783 := by
  unfold tailWord_1760929
  simp only [CollatzResearch.WordTrace]
  refine ⟨64226357037462450574957841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42817571358308300383305227 64226357037462450574957841)
  ·
    refine ⟨48169767778096837931218381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64226357037462450574957841 48169767778096837931218381)
    ·
      refine ⟨18063662916786314224206893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48169767778096837931218381 18063662916786314224206893)
      ·
        refine ⟨6773873593794867834077585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18063662916786314224206893 6773873593794867834077585)
        ·
          refine ⟨5080405195346150875558189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6773873593794867834077585 5080405195346150875558189)
          ·
            refine ⟨1905151948254806578334321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5080405195346150875558189 1905151948254806578334321)
            ·
              refine ⟨1428863961191104933750741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1905151948254806578334321 1428863961191104933750741)
              ·
                refine ⟨33488999090416521884783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1428863961191104933750741 33488999090416521884783)
                ·
                  rfl

theorem cell23_1760929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 7].length) (baseStart_1760929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760929 prefixEnd_1760929 := by exact prefixLift 1760929
  have htrace : WordTrace (prefixWord ++ tailWord_1760929) baseStart_1760929 baseEnd_1760929 := by
    simpa [prefixWord, tailWord_1760929, baseEnd_1760929] using wordTrace_append hprefix tailTrace_1760929
  have hstable : (prefixWord ++ tailWord_1760929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760929).length < 2 ^ (prefixWord ++ tailWord_1760929).sum := by decide
  have hdescent : baseEnd_1760929 < baseStart_1760929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760955 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 4, 6]
def baseStart_1760955 : Nat := 118140960795 + 1760955 * 2 ^ 59
def prefixEnd_1760955 : Nat := 4983230072969 + 3 ^ 40 * 1760955 * 2
def baseEnd_1760955 : Nat := 301405441979420996388007

theorem tailTrace_1760955 : CollatzResearch.WordTrace tailWord_1760955 prefixEnd_1760955 301405441979420996388007 := by
  unfold tailWord_1760955
  simp only [CollatzResearch.WordTrace]
  refine ⟨64227305335368257015404319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42818203556912171343602879 64227305335368257015404319)
  ·
    refine ⟨96340958003052385523106479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64227305335368257015404319 96340958003052385523106479)
    ·
      refine ⟨144511437004578578284659719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96340958003052385523106479 144511437004578578284659719)
      ·
        refine ⟨216767155506867867426989579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144511437004578578284659719 216767155506867867426989579)
        ·
          refine ⟨325150733260301801140484369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216767155506867867426989579 325150733260301801140484369)
          ·
            refine ⟨243863049945226350855363277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325150733260301801140484369 243863049945226350855363277)
            ·
              refine ⟨91448643729459881570761229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243863049945226350855363277 91448643729459881570761229)
              ·
                refine ⟨34293241398547455589035461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91448643729459881570761229 34293241398547455589035461)
                ·
                  refine ⟨6429982762227647922944149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34293241398547455589035461 6429982762227647922944149)
                  ·
                    refine ⟨301405441979420996388007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6429982762227647922944149 301405441979420996388007)
                    ·
                      rfl

theorem cell23_1760955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 6].length) (baseStart_1760955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760955 prefixEnd_1760955 := by exact prefixLift 1760955
  have htrace : WordTrace (prefixWord ++ tailWord_1760955) baseStart_1760955 baseEnd_1760955 := by
    simpa [prefixWord, tailWord_1760955, baseEnd_1760955] using wordTrace_append hprefix tailTrace_1760955
  have hstable : (prefixWord ++ tailWord_1760955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760955).length < 2 ^ (prefixWord ++ tailWord_1760955).sum := by decide
  have hdescent : baseEnd_1760955 < baseStart_1760955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760975 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 6]
def baseStart_1760975 : Nat := 118140960795 + 1760975 * 2 ^ 59
def prefixEnd_1760975 : Nat := 4983230072969 + 3 ^ 40 * 1760975 * 2
def baseEnd_1760975 : Nat := 904226595551352910913929

theorem tailTrace_1760975 : CollatzResearch.WordTrace tailWord_1760975 prefixEnd_1760975 904226595551352910913929 := by
  unfold tailWord_1760975
  simp only [CollatzResearch.WordTrace]
  refine ⟨64228034795295800431132379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42818689863530533620754919 64228034795295800431132379)
  ·
    refine ⟨96342052192943700646698569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64228034795295800431132379 96342052192943700646698569)
    ·
      refine ⟨72256539144707775485023927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96342052192943700646698569 72256539144707775485023927)
      ·
        refine ⟨108384808717061663227535891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72256539144707775485023927 108384808717061663227535891)
        ·
          refine ⟨162577213075592494841303837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108384808717061663227535891 162577213075592494841303837)
          ·
            refine ⟨60966454903347185565488939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162577213075592494841303837 60966454903347185565488939)
            ·
              refine ⟨91449682355020778348233409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60966454903347185565488939 91449682355020778348233409)
              ·
                refine ⟨68587261766265583761175057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91449682355020778348233409 68587261766265583761175057)
                ·
                  refine ⟨51440446324699187820881293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68587261766265583761175057 51440446324699187820881293)
                  ·
                    refine ⟨19290167371762195432830485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51440446324699187820881293 19290167371762195432830485)
                    ·
                      refine ⟨904226595551352910913929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19290167371762195432830485 904226595551352910913929)
                      ·
                        rfl

theorem cell23_1760975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 6].length) (baseStart_1760975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1760975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1760975 prefixEnd_1760975 := by exact prefixLift 1760975
  have htrace : WordTrace (prefixWord ++ tailWord_1760975) baseStart_1760975 baseEnd_1760975 := by
    simpa [prefixWord, tailWord_1760975, baseEnd_1760975] using wordTrace_append hprefix tailTrace_1760975
  have hstable : (prefixWord ++ tailWord_1760975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760975).length < 2 ^ (prefixWord ++ tailWord_1760975).sum := by decide
  have hdescent : baseEnd_1760975 < baseStart_1760975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761032 : List Nat := [2, 1, 3, 2, 2, 1, 2, 2, 1, 7]
def baseStart_1761032 : Nat := 118140960795 + 1761032 * 2 ^ 59
def prefixEnd_1761032 : Nat := 4983230072969 + 3 ^ 40 * 1761032 * 2
def baseEnd_1761032 : Nat := 301418621316219729300389

theorem tailTrace_1761032 : CollatzResearch.WordTrace tailWord_1761032 prefixEnd_1761032 301418621316219729300389 := by
  unfold tailWord_1761032
  simp only [CollatzResearch.WordTrace]
  refine ⟨32115056878044649582978675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42820075837392866110638233 32115056878044649582978675)
  ·
    refine ⟨48172585317066974374468013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32115056878044649582978675 48172585317066974374468013)
    ·
      refine ⟨18064719493900115390425505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48172585317066974374468013 18064719493900115390425505)
      ·
        refine ⟨13548539620425086542819129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18064719493900115390425505 13548539620425086542819129)
        ·
          refine ⟨10161404715318814907114347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13548539620425086542819129 10161404715318814907114347)
          ·
            refine ⟨15242107072978222360671521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10161404715318814907114347 15242107072978222360671521)
            ·
              refine ⟨11431580304733666770503641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15242107072978222360671521 11431580304733666770503641)
              ·
                refine ⟨8573685228550250077877731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11431580304733666770503641 8573685228550250077877731)
                ·
                  refine ⟨12860527842825375116816597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8573685228550250077877731 12860527842825375116816597)
                  ·
                    refine ⟨301418621316219729300389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12860527842825375116816597 301418621316219729300389)
                    ·
                      rfl

theorem cell23_1761032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_1761032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761032 prefixEnd_1761032 := by exact prefixLift 1761032
  have htrace : WordTrace (prefixWord ++ tailWord_1761032) baseStart_1761032 baseEnd_1761032 := by
    simpa [prefixWord, tailWord_1761032, baseEnd_1761032] using wordTrace_append hprefix tailTrace_1761032
  have hstable : (prefixWord ++ tailWord_1761032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761032).length < 2 ^ (prefixWord ++ tailWord_1761032).sum := by decide
  have hdescent : baseEnd_1761032 < baseStart_1761032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761102 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9]
def baseStart_1761102 : Nat := 118140960795 + 1761102 * 2 ^ 59
def prefixEnd_1761102 : Nat := 4983230072969 + 3 ^ 40 * 1761102 * 2
def baseEnd_1761102 : Nat := 904291807594473914025845

theorem tailTrace_1761102 : CollatzResearch.WordTrace tailWord_1761102 prefixEnd_1761102 904291807594473914025845 := by
  unfold tailWord_1761102
  simp only [CollatzResearch.WordTrace]
  refine ⟨8029083358229462640125695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42821777910557134080670373 8029083358229462640125695)
  ·
    refine ⟨12043625037344193960188543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8029083358229462640125695 12043625037344193960188543)
    ·
      refine ⟨18065437556016290940282815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12043625037344193960188543 18065437556016290940282815)
      ·
        refine ⟨27098156334024436410424223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18065437556016290940282815 27098156334024436410424223)
        ·
          refine ⟨40647234501036654615636335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27098156334024436410424223 40647234501036654615636335)
          ·
            refine ⟨60970851751554981923454503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40647234501036654615636335 60970851751554981923454503)
            ·
              refine ⟨91456277627332472885181755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60970851751554981923454503 91456277627332472885181755)
              ·
                refine ⟨137184416440998709327772633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91456277627332472885181755 137184416440998709327772633)
                ·
                  refine ⟨102888312330749031995829475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137184416440998709327772633 102888312330749031995829475)
                  ·
                    refine ⟨154332468496123547993744213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102888312330749031995829475 154332468496123547993744213)
                    ·
                      refine ⟨904291807594473914025845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 154332468496123547993744213 904291807594473914025845)
                      ·
                        rfl

theorem cell23_1761102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_1761102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761102 prefixEnd_1761102 := by exact prefixLift 1761102
  have htrace : WordTrace (prefixWord ++ tailWord_1761102) baseStart_1761102 baseEnd_1761102 := by
    simpa [prefixWord, tailWord_1761102, baseEnd_1761102] using wordTrace_append hprefix tailTrace_1761102
  have hstable : (prefixWord ++ tailWord_1761102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761102).length < 2 ^ (prefixWord ++ tailWord_1761102).sum := by decide
  have hdescent : baseEnd_1761102 < baseStart_1761102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761130 : List Nat := [3, 1, 3, 4, 1, 2, 1, 1, 3, 4]
def baseStart_1761130 : Nat := 118140960795 + 1761130 * 2 ^ 59
def prefixEnd_1761130 : Nat := 4983230072969 + 3 ^ 40 * 1761130 * 2
def baseEnd_1761130 : Nat := 301435395017599934825239

theorem tailTrace_1761130 : CollatzResearch.WordTrace tailWord_1761130 prefixEnd_1761130 301435395017599934825239 := by
  unfold tailWord_1761130
  simp only [CollatzResearch.WordTrace]
  refine ⟨16058422027433565475756211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42822458739822841268683229 16058422027433565475756211)
  ·
    refine ⟨24087633041150348213634317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16058422027433565475756211 24087633041150348213634317)
    ·
      refine ⟨9032862390431380580112869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24087633041150348213634317 9032862390431380580112869)
      ·
        refine ⟨1693661698205883858771163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9032862390431380580112869 1693661698205883858771163)
        ·
          refine ⟨2540492547308825788156745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1693661698205883858771163 2540492547308825788156745)
          ·
            refine ⟨1905369410481619341117559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2540492547308825788156745 1905369410481619341117559)
            ·
              refine ⟨2858054115722429011676339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1905369410481619341117559 2858054115722429011676339)
              ·
                refine ⟨4287081173583643517514509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2858054115722429011676339 4287081173583643517514509)
                ·
                  refine ⟨1607655440093866319067941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4287081173583643517514509 1607655440093866319067941)
                  ·
                    refine ⟨301435395017599934825239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1607655440093866319067941 301435395017599934825239)
                    ·
                      rfl

theorem cell23_1761130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_1761130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761130 prefixEnd_1761130 := by exact prefixLift 1761130
  have htrace : WordTrace (prefixWord ++ tailWord_1761130) baseStart_1761130 baseEnd_1761130 := by
    simpa [prefixWord, tailWord_1761130, baseEnd_1761130] using wordTrace_append hprefix tailTrace_1761130
  have hstable : (prefixWord ++ tailWord_1761130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761130).length < 2 ^ (prefixWord ++ tailWord_1761130).sum := by decide
  have hdescent : baseEnd_1761130 < baseStart_1761130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761156 : List Nat := [2, 3, 2, 1, 1, 1, 5, 2, 1, 5]
def baseStart_1761156 : Nat := 118140960795 + 1761156 * 2 ^ 59
def prefixEnd_1761156 : Nat := 4983230072969 + 3 ^ 40 * 1761156 * 2
def baseEnd_1761156 : Nat := 301439845183272234250199

theorem tailTrace_1761156 : CollatzResearch.WordTrace tailWord_1761156 prefixEnd_1761156 301439845183272234250199 := by
  unfold tailWord_1761156
  simp only [CollatzResearch.WordTrace]
  refine ⟨32117318203820034171735661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42823090938426712228980881 32117318203820034171735661)
  ·
    refine ⟨12043994326432512814400873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32117318203820034171735661 12043994326432512814400873)
    ·
      refine ⟨9032995744824384610800655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12043994326432512814400873 9032995744824384610800655)
      ·
        refine ⟨13549493617236576916200983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9032995744824384610800655 13549493617236576916200983)
        ·
          refine ⟨20324240425854865374301475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13549493617236576916200983 20324240425854865374301475)
          ·
            refine ⟨30486360638782298061452213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20324240425854865374301475 30486360638782298061452213)
            ·
              refine ⟨2858096309885840443261145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30486360638782298061452213 2858096309885840443261145)
              ·
                refine ⟨2143572232414380332445859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2858096309885840443261145 2143572232414380332445859)
                ·
                  refine ⟨3215358348621570498668789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2143572232414380332445859 3215358348621570498668789)
                  ·
                    refine ⟨301439845183272234250199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3215358348621570498668789 301439845183272234250199)
                    ·
                      rfl

theorem cell23_1761156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_1761156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761156 prefixEnd_1761156 := by exact prefixLift 1761156
  have htrace : WordTrace (prefixWord ++ tailWord_1761156) baseStart_1761156 baseEnd_1761156 := by
    simpa [prefixWord, tailWord_1761156, baseEnd_1761156] using wordTrace_append hprefix tailTrace_1761156
  have hstable : (prefixWord ++ tailWord_1761156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761156).length < 2 ^ (prefixWord ++ tailWord_1761156).sum := by decide
  have hdescent : baseEnd_1761156 < baseStart_1761156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761169 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 6, 4]
def baseStart_1761169 : Nat := 118140960795 + 1761169 * 2 ^ 59
def prefixEnd_1761169 : Nat := 4983230072969 + 3 ^ 40 * 1761169 * 2
def baseEnd_1761169 : Nat := 301442070266108383962679

theorem tailTrace_1761169 : CollatzResearch.WordTrace tailWord_1761169 prefixEnd_1761169 301442070266108383962679 := by
  unfold tailWord_1761169
  simp only [CollatzResearch.WordTrace]
  refine ⟨64235110556592971563694561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42823407037728647709129707 64235110556592971563694561)
  ·
    refine ⟨48176332917444728672770921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64235110556592971563694561 48176332917444728672770921)
    ·
      refine ⟨36132249688083546504578191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48176332917444728672770921 36132249688083546504578191)
      ·
        refine ⟨54198374532125319756867287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36132249688083546504578191 54198374532125319756867287)
        ·
          refine ⟨81297561798187979635300931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54198374532125319756867287 81297561798187979635300931)
          ·
            refine ⟨121946342697281969452951397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81297561798187979635300931 121946342697281969452951397)
            ·
              refine ⟨22864939255740369272428387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121946342697281969452951397 22864939255740369272428387)
              ·
                refine ⟨34297408883610553908642581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22864939255740369272428387 34297408883610553908642581)
                ·
                  refine ⟨1607691041419244714467621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 34297408883610553908642581 1607691041419244714467621)
                  ·
                    refine ⟨301442070266108383962679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1607691041419244714467621 301442070266108383962679)
                    ·
                      rfl

theorem cell23_1761169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6, 4].length) (baseStart_1761169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761169 prefixEnd_1761169 := by exact prefixLift 1761169
  have htrace : WordTrace (prefixWord ++ tailWord_1761169) baseStart_1761169 baseEnd_1761169 := by
    simpa [prefixWord, tailWord_1761169, baseEnd_1761169] using wordTrace_append hprefix tailTrace_1761169
  have hstable : (prefixWord ++ tailWord_1761169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761169).length < 2 ^ (prefixWord ++ tailWord_1761169).sum := by decide
  have hdescent : baseEnd_1761169 < baseStart_1761169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761226 : List Nat := [3, 1, 2, 1, 2, 1, 4, 2, 1, 3, 3]
def baseStart_1761226 : Nat := 118140960795 + 1761226 * 2 ^ 59
def prefixEnd_1761226 : Nat := 4983230072969 + 3 ^ 40 * 1761226 * 2
def baseEnd_1761226 : Nat := 904355479195631428875275

theorem tailTrace_1761226 : CollatzResearch.WordTrace tailWord_1761226 prefixEnd_1761226 904355479195631428875275 := by
  unfold tailWord_1761226
  simp only [CollatzResearch.WordTrace]
  refine ⟨16059297379346617574629883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42824793011590980199013021 16059297379346617574629883)
  ·
    refine ⟨24088946069019926361944825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16059297379346617574629883 24088946069019926361944825)
    ·
      refine ⟨18066709551764944771458619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24088946069019926361944825 18066709551764944771458619)
      ·
        refine ⟨27100064327647417157187929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18066709551764944771458619 27100064327647417157187929)
        ·
          refine ⟨20325048245735562867890947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27100064327647417157187929 20325048245735562867890947)
          ·
            refine ⟨30487572368603344301836421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20325048245735562867890947 30487572368603344301836421)
            ·
              refine ⟨5716419819113127056594329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30487572368603344301836421 5716419819113127056594329)
              ·
                refine ⟨4287314864334845292445747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5716419819113127056594329 4287314864334845292445747)
                ·
                  refine ⟨6430972296502267938668621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4287314864334845292445747 6430972296502267938668621)
                  ·
                    refine ⟨2411614611188350477000733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6430972296502267938668621 2411614611188350477000733)
                    ·
                      refine ⟨904355479195631428875275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2411614611188350477000733 904355479195631428875275)
                      ·
                        rfl

theorem cell23_1761226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_1761226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761226 prefixEnd_1761226 := by exact prefixLift 1761226
  have htrace : WordTrace (prefixWord ++ tailWord_1761226) baseStart_1761226 baseEnd_1761226 := by
    simpa [prefixWord, tailWord_1761226, baseEnd_1761226] using wordTrace_append hprefix tailTrace_1761226
  have hstable : (prefixWord ++ tailWord_1761226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761226).length < 2 ^ (prefixWord ++ tailWord_1761226).sum := by decide
  have hdescent : baseEnd_1761226 < baseStart_1761226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761249 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 1, 5, 4]
def baseStart_1761249 : Nat := 118140960795 + 1761249 * 2 ^ 59
def prefixEnd_1761249 : Nat := 4983230072969 + 3 ^ 40 * 1761249 * 2
def baseEnd_1761249 : Nat := 904367289250684838887669

theorem tailTrace_1761249 : CollatzResearch.WordTrace tailWord_1761249 prefixEnd_1761249 904367289250684838887669 := by
  unfold tailWord_1761249
  simp only [CollatzResearch.WordTrace]
  refine ⟨64238028396303145226606801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42825352264202096817737867 64238028396303145226606801)
  ·
    refine ⟨48178521297227358919955101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64238028396303145226606801 48178521297227358919955101)
    ·
      refine ⟨18066945486460259594983163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48178521297227358919955101 18066945486460259594983163)
      ·
        refine ⟨27100418229690389392474745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18066945486460259594983163 27100418229690389392474745)
        ·
          refine ⟨20325313672267792044356059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27100418229690389392474745 20325313672267792044356059)
          ·
            refine ⟨30487970508401688066534089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20325313672267792044356059 30487970508401688066534089)
            ·
              refine ⟨22865977881301266049900567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30487970508401688066534089 22865977881301266049900567)
              ·
                refine ⟨34298966821951899074850851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22865977881301266049900567 34298966821951899074850851)
                ·
                  refine ⟨51448450232927848612276277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34298966821951899074850851 51448450232927848612276277)
                  ·
                    refine ⟨4823292209336985807400901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51448450232927848612276277 4823292209336985807400901)
                    ·
                      refine ⟨904367289250684838887669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4823292209336985807400901 904367289250684838887669)
                      ·
                        rfl

theorem cell23_1761249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_1761249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761249 prefixEnd_1761249 := by exact prefixLift 1761249
  have htrace : WordTrace (prefixWord ++ tailWord_1761249) baseStart_1761249 baseEnd_1761249 := by
    simpa [prefixWord, tailWord_1761249, baseEnd_1761249] using wordTrace_append hprefix tailTrace_1761249
  have hstable : (prefixWord ++ tailWord_1761249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761249).length < 2 ^ (prefixWord ++ tailWord_1761249).sum := by decide
  have hdescent : baseEnd_1761249 < baseStart_1761249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761279 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 4]
def baseStart_1761279 : Nat := 118140960795 + 1761279 * 2 ^ 59
def prefixEnd_1761279 : Nat := 4983230072969 + 3 ^ 40 * 1761279 * 2
def baseEnd_1761279 : Nat := 904382693670319721512531

theorem tailTrace_1761279 : CollatzResearch.WordTrace tailWord_1761279 prefixEnd_1761279 904382693670319721512531 := by
  unfold tailWord_1761279
  simp only [CollatzResearch.WordTrace]
  refine ⟨64239122586194460350198891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42826081724129640233465927 64239122586194460350198891)
  ·
    refine ⟨96358683879291690525298337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64239122586194460350198891 96358683879291690525298337)
    ·
      refine ⟨72269012909468767893973753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96358683879291690525298337 72269012909468767893973753)
      ·
        refine ⟨54201759682101575920480315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72269012909468767893973753 54201759682101575920480315)
        ·
          refine ⟨81302639523152363880720473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54201759682101575920480315 81302639523152363880720473)
          ·
            refine ⟨60976979642364272910540355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81302639523152363880720473 60976979642364272910540355)
            ·
              refine ⟨91465469463546409365810533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60976979642364272910540355 91465469463546409365810533)
              ·
                refine ⟨17149775524414951756089475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91465469463546409365810533 17149775524414951756089475)
                ·
                  refine ⟨25724663286622427634134213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17149775524414951756089475 25724663286622427634134213)
                  ·
                    refine ⟨4823374366241705181400165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25724663286622427634134213 4823374366241705181400165)
                    ·
                      refine ⟨904382693670319721512531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4823374366241705181400165 904382693670319721512531)
                      ·
                        rfl

theorem cell23_1761279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_1761279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761279 prefixEnd_1761279 := by exact prefixLift 1761279
  have htrace : WordTrace (prefixWord ++ tailWord_1761279) baseStart_1761279 baseEnd_1761279 := by
    simpa [prefixWord, tailWord_1761279, baseEnd_1761279] using wordTrace_append hprefix tailTrace_1761279
  have hstable : (prefixWord ++ tailWord_1761279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761279).length < 2 ^ (prefixWord ++ tailWord_1761279).sum := by decide
  have hdescent : baseEnd_1761279 < baseStart_1761279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761306 : List Nat := [3, 1, 1, 3, 1, 3, 3, 1, 7]
def baseStart_1761306 : Nat := 118140960795 + 1761306 * 2 ^ 59
def prefixEnd_1761306 : Nat := 4983230072969 + 3 ^ 40 * 1761306 * 2
def baseEnd_1761306 : Nat := 100488506405332346208323

theorem tailTrace_1761306 : CollatzResearch.WordTrace tailWord_1761306 prefixEnd_1761306 100488506405332346208323 := by
  unfold tailWord_1761306
  simp only [CollatzResearch.WordTrace]
  refine ⟨16060026839274160990357943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42826738238064429307621181 16060026839274160990357943)
  ·
    refine ⟨24090040258911241485536915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16060026839274160990357943 24090040258911241485536915)
    ·
      refine ⟨36135060388366862228305373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24090040258911241485536915 36135060388366862228305373)
      ·
        refine ⟨13550647645637573335614515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36135060388366862228305373 13550647645637573335614515)
        ·
          refine ⟨20325971468456360003421773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13550647645637573335614515 20325971468456360003421773)
          ·
            refine ⟨7622239300671135001283165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20325971468456360003421773 7622239300671135001283165)
            ·
              refine ⟨2858339737751675625481187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7622239300671135001283165 2858339737751675625481187)
              ·
                refine ⟨4287509606627513438221781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2858339737751675625481187 4287509606627513438221781)
                ·
                  refine ⟨100488506405332346208323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4287509606627513438221781 100488506405332346208323)
                  ·
                    rfl

theorem cell23_1761306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 7].length) (baseStart_1761306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761306 prefixEnd_1761306 := by exact prefixLift 1761306
  have htrace : WordTrace (prefixWord ++ tailWord_1761306) baseStart_1761306 baseEnd_1761306 := by
    simpa [prefixWord, tailWord_1761306, baseEnd_1761306] using wordTrace_append hprefix tailTrace_1761306
  have hstable : (prefixWord ++ tailWord_1761306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761306).length < 2 ^ (prefixWord ++ tailWord_1761306).sum := by decide
  have hdescent : baseEnd_1761306 < baseStart_1761306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761317 : List Nat := [1, 3, 1, 2, 2, 3, 4, 1, 2, 2, 2]
def baseStart_1761317 : Nat := 118140960795 + 1761317 * 2 ^ 59
def prefixEnd_1761317 : Nat := 4983230072969 + 3 ^ 40 * 1761317 * 2
def baseEnd_1761317 : Nat := 904402205935190572837357

theorem tailTrace_1761317 : CollatzResearch.WordTrace tailWord_1761317 prefixEnd_1761317 904402205935190572837357 := by
  unfold tailWord_1761317
  simp only [CollatzResearch.WordTrace]
  refine ⟨64240508560056792840082205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42827005706704528560054803 64240508560056792840082205)
  ·
    refine ⟨24090190710021297315030827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64240508560056792840082205 24090190710021297315030827)
    ·
      refine ⟨36135286065031945972546241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24090190710021297315030827 36135286065031945972546241)
      ·
        refine ⟨27101464548773959479409681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36135286065031945972546241 27101464548773959479409681)
        ·
          refine ⟨20326098411580469609557261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27101464548773959479409681 20326098411580469609557261)
          ·
            refine ⟨7622286904342676103583973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20326098411580469609557261 7622286904342676103583973)
            ·
              refine ⟨1429178794564251769421995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7622286904342676103583973 1429178794564251769421995)
              ·
                refine ⟨2143768191846377654132993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1429178794564251769421995 2143768191846377654132993)
                ·
                  refine ⟨1607826143884783240599745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2143768191846377654132993 1607826143884783240599745)
                  ·
                    refine ⟨1205869607913587430449809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1607826143884783240599745 1205869607913587430449809)
                    ·
                      refine ⟨904402205935190572837357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1205869607913587430449809 904402205935190572837357)
                      ·
                        rfl

theorem cell23_1761317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 2, 2, 2].length) (baseStart_1761317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761317 prefixEnd_1761317 := by exact prefixLift 1761317
  have htrace : WordTrace (prefixWord ++ tailWord_1761317) baseStart_1761317 baseEnd_1761317 := by
    simpa [prefixWord, tailWord_1761317, baseEnd_1761317] using wordTrace_append hprefix tailTrace_1761317
  have hstable : (prefixWord ++ tailWord_1761317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761317).length < 2 ^ (prefixWord ++ tailWord_1761317).sum := by decide
  have hdescent : baseEnd_1761317 < baseStart_1761317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761350 : List Nat := [6, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_1761350 : Nat := 118140960795 + 1761350 * 2 ^ 59
def prefixEnd_1761350 : Nat := 4983230072969 + 3 ^ 40 * 1761350 * 2
def baseEnd_1761350 : Nat := 904419150796788943724705

theorem tailTrace_1761350 : CollatzResearch.WordTrace tailWord_1761350 prefixEnd_1761350 904419150796788943724705 := by
  unfold tailWord_1761350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2007553505279288733626047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42827808112624826317355669 2007553505279288733626047)
  ·
    refine ⟨3011330257918933100439071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2007553505279288733626047 3011330257918933100439071)
    ·
      refine ⟨4516995386878399650658607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3011330257918933100439071 4516995386878399650658607)
      ·
        refine ⟨6775493080317599475987911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4516995386878399650658607 6775493080317599475987911)
        ·
          refine ⟨10163239620476399213981867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6775493080317599475987911 10163239620476399213981867)
          ·
            refine ⟨15244859430714598820972801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10163239620476399213981867 15244859430714598820972801)
            ·
              refine ⟨11433644573035949115729601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15244859430714598820972801 11433644573035949115729601)
              ·
                refine ⟨8575233429776961836797201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11433644573035949115729601 8575233429776961836797201)
                ·
                  refine ⟨6431425072332721377597901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8575233429776961836797201 6431425072332721377597901)
                  ·
                    refine ⟨2411784402124770516599213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6431425072332721377597901 2411784402124770516599213)
                    ·
                      refine ⟨904419150796788943724705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2411784402124770516599213 904419150796788943724705)
                      ·
                        rfl

theorem cell23_1761350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_1761350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761350 prefixEnd_1761350 := by exact prefixLift 1761350
  have htrace : WordTrace (prefixWord ++ tailWord_1761350) baseStart_1761350 baseEnd_1761350 := by
    simpa [prefixWord, tailWord_1761350, baseEnd_1761350] using wordTrace_append hprefix tailTrace_1761350
  have hstable : (prefixWord ++ tailWord_1761350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761350).length < 2 ^ (prefixWord ++ tailWord_1761350).sum := by decide
  have hdescent : baseEnd_1761350 < baseStart_1761350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761383 : List Nat := [1, 1, 5, 1, 1, 2, 3, 2, 3, 4]
def baseStart_1761383 : Nat := 118140960795 + 1761383 * 2 ^ 59
def prefixEnd_1761383 : Nat := 4983230072969 + 3 ^ 40 * 1761383 * 2
def baseEnd_1761383 : Nat := 301478698552795771537351

theorem tailTrace_1761383 : CollatzResearch.WordTrace tailWord_1761383 prefixEnd_1761383 301478698552795771537351 := by
  unfold tailWord_1761383
  simp only [CollatzResearch.WordTrace]
  refine ⟨64242915777817686111984803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42828610518545124074656535 64242915777817686111984803)
  ·
    refine ⟨96364373666726529167977205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64242915777817686111984803 96364373666726529167977205)
    ·
      refine ⟨9034160031255612109497863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96364373666726529167977205 9034160031255612109497863)
      ·
        refine ⟨13551240046883418164246795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9034160031255612109497863 13551240046883418164246795)
        ·
          refine ⟨20326860070325127246370193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13551240046883418164246795 20326860070325127246370193)
          ·
            refine ⟨15245145052743845434777645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20326860070325127246370193 15245145052743845434777645)
            ·
              refine ⟨5716929394778942038041617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15245145052743845434777645 5716929394778942038041617)
              ·
                refine ⟨4287697046084206528531213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5716929394778942038041617 4287697046084206528531213)
                ·
                  refine ⟨1607886392281577448199205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4287697046084206528531213 1607886392281577448199205)
                  ·
                    refine ⟨301478698552795771537351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1607886392281577448199205 301478698552795771537351)
                    ·
                      rfl

theorem cell23_1761383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_1761383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761383 prefixEnd_1761383 := by exact prefixLift 1761383
  have htrace : WordTrace (prefixWord ++ tailWord_1761383) baseStart_1761383 baseEnd_1761383 := by
    simpa [prefixWord, tailWord_1761383, baseEnd_1761383] using wordTrace_append hprefix tailTrace_1761383
  have hstable : (prefixWord ++ tailWord_1761383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761383).length < 2 ^ (prefixWord ++ tailWord_1761383).sum := by decide
  have hdescent : baseEnd_1761383 < baseStart_1761383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761413 : List Nat := [1, 3, 1, 1, 5, 1, 3, 2, 6]
def baseStart_1761413 : Nat := 118140960795 + 1761413 * 2 ^ 59
def prefixEnd_1761413 : Nat := 4983230072969 + 3 ^ 40 * 1761413 * 2
def baseEnd_1761413 : Nat := 100494611119780244137435

theorem tailTrace_1761413 : CollatzResearch.WordTrace tailWord_1761413 prefixEnd_1761413 100494611119780244137435 := by
  unfold tailWord_1761413
  simp only [CollatzResearch.WordTrace]
  refine ⟨64244009967709001235576893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42829339978472667490384595 64244009967709001235576893)
  ·
    refine ⟨24091503737890875463341335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64244009967709001235576893 24091503737890875463341335)
    ·
      refine ⟨36137255606836313195012003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24091503737890875463341335 36137255606836313195012003)
      ·
        refine ⟨54205883410254469792518005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36137255606836313195012003 54205883410254469792518005)
        ·
          refine ⟨5081801569711356543048563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54205883410254469792518005 5081801569711356543048563)
          ·
            refine ⟨7622702354567034814572845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5081801569711356543048563 7622702354567034814572845)
            ·
              refine ⟨2858513382962638055464817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7622702354567034814572845 2858513382962638055464817)
              ·
                refine ⟨2143885037221978541598613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2858513382962638055464817 2143885037221978541598613)
                ·
                  refine ⟨100494611119780244137435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2143885037221978541598613 100494611119780244137435)
                  ·
                    rfl

theorem cell23_1761413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 6].length) (baseStart_1761413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761413 prefixEnd_1761413 := by exact prefixLift 1761413
  have htrace : WordTrace (prefixWord ++ tailWord_1761413) baseStart_1761413 baseEnd_1761413 := by
    simpa [prefixWord, tailWord_1761413, baseEnd_1761413] using wordTrace_append hprefix tailTrace_1761413
  have hstable : (prefixWord ++ tailWord_1761413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761413).length < 2 ^ (prefixWord ++ tailWord_1761413).sum := by decide
  have hdescent : baseEnd_1761413 < baseStart_1761413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761440 : List Nat := [2, 1, 1, 4, 2, 2, 2, 2, 3, 1, 3]
def baseStart_1761440 : Nat := 118140960795 + 1761440 * 2 ^ 59
def prefixEnd_1761440 : Nat := 4983230072969 + 3 ^ 40 * 1761440 * 2
def baseEnd_1761440 : Nat := 904465364055693591599291

theorem tailTrace_1761440 : CollatzResearch.WordTrace tailWord_1761440 prefixEnd_1761440 904465364055693591599291 := by
  unfold tailWord_1761440
  simp only [CollatzResearch.WordTrace]
  refine ⟨32122497369305592423404887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42829996492407456564539849 32122497369305592423404887)
  ·
    refine ⟨48183746053958388635107331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32122497369305592423404887 48183746053958388635107331)
    ·
      refine ⟨72275619080937582952660997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48183746053958388635107331 72275619080937582952660997)
      ·
        refine ⟨13551678577675796803623937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72275619080937582952660997 13551678577675796803623937)
        ·
          refine ⟨10163758933256847602717953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13551678577675796803623937 10163758933256847602717953)
          ·
            refine ⟨7622819199942635702038465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10163758933256847602717953 7622819199942635702038465)
            ·
              refine ⟨5717114399956976776528849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7622819199942635702038465 5717114399956976776528849)
              ·
                refine ⟨4287835799967732582396637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5717114399956976776528849 4287835799967732582396637)
                ·
                  refine ⟨1607938424987899718398739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4287835799967732582396637 1607938424987899718398739)
                  ·
                    refine ⟨2411907637481849577598109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1607938424987899718398739 2411907637481849577598109)
                    ·
                      refine ⟨904465364055693591599291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2411907637481849577598109 904465364055693591599291)
                      ·
                        rfl

theorem cell23_1761440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_1761440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761440 prefixEnd_1761440 := by exact prefixLift 1761440
  have htrace : WordTrace (prefixWord ++ tailWord_1761440) baseStart_1761440 baseEnd_1761440 := by
    simpa [prefixWord, tailWord_1761440, baseEnd_1761440] using wordTrace_append hprefix tailTrace_1761440
  have hstable : (prefixWord ++ tailWord_1761440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761440).length < 2 ^ (prefixWord ++ tailWord_1761440).sum := by decide
  have hdescent : baseEnd_1761440 < baseStart_1761440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761483 : List Nat := [1, 1, 1, 1, 3, 2, 4, 2, 3, 2, 3]
def baseStart_1761483 : Nat := 118140960795 + 1761483 * 2 ^ 59
def prefixEnd_1761483 : Nat := 4983230072969 + 3 ^ 40 * 1761483 * 2
def baseEnd_1761483 : Nat := 904487443723836923361593

theorem tailTrace_1761483 : CollatzResearch.WordTrace tailWord_1761483 prefixEnd_1761483 904487443723836923361593 := by
  unfold tailWord_1761483
  simp only [CollatzResearch.WordTrace]
  refine ⟨64246563077455403190625103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42831042051636935460416735 64246563077455403190625103)
  ·
    refine ⟨96369844616183104785937655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64246563077455403190625103 96369844616183104785937655)
    ·
      refine ⟨144554766924274657178906483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96369844616183104785937655 144554766924274657178906483)
      ·
        refine ⟨216832150386411985768359725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144554766924274657178906483 216832150386411985768359725)
        ·
          refine ⟨81312056394904494663134897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216832150386411985768359725 81312056394904494663134897)
          ·
            refine ⟨60984042296178370997351173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81312056394904494663134897 60984042296178370997351173)
            ·
              refine ⟨11434507930533444562003345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60984042296178370997351173 11434507930533444562003345)
              ·
                refine ⟨8575880947900083421502509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11434507930533444562003345 8575880947900083421502509)
                ·
                  refine ⟨3215955355462531283063441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8575880947900083421502509 3215955355462531283063441)
                  ·
                    refine ⟨2411966516596898462297581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3215955355462531283063441 2411966516596898462297581)
                    ·
                      refine ⟨904487443723836923361593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2411966516596898462297581 904487443723836923361593)
                      ·
                        rfl

theorem cell23_1761483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2, 3].length) (baseStart_1761483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761483 prefixEnd_1761483 := by exact prefixLift 1761483
  have htrace : WordTrace (prefixWord ++ tailWord_1761483) baseStart_1761483 baseEnd_1761483 := by
    simpa [prefixWord, tailWord_1761483, baseEnd_1761483] using wordTrace_append hprefix tailTrace_1761483
  have hstable : (prefixWord ++ tailWord_1761483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761483).length < 2 ^ (prefixWord ++ tailWord_1761483).sum := by decide
  have hdescent : baseEnd_1761483 < baseStart_1761483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761494 : List Nat := [5, 2, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_1761494 : Nat := 118140960795 + 1761494 * 2 ^ 59
def prefixEnd_1761494 : Nat := 4983230072969 + 3 ^ 40 * 1761494 * 2
def baseEnd_1761494 : Nat := 301497697337012126774681

theorem tailTrace_1761494 : CollatzResearch.WordTrace tailWord_1761494 prefixEnd_1761494 301497697337012126774681 := by
  unfold tailWord_1761494
  simp only [CollatzResearch.WordTrace]
  refine ⟨4015435267525972004329721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42831309520277034712850357 4015435267525972004329721)
  ·
    refine ⟨3011576450644479003247291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4015435267525972004329721 3011576450644479003247291)
    ·
      refine ⟨4517364675966718504870937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3011576450644479003247291 4517364675966718504870937)
      ·
        refine ⟨3388023506975038878653203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4517364675966718504870937 3388023506975038878653203)
        ·
          refine ⟨5082035260462558317979805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3388023506975038878653203 5082035260462558317979805)
          ·
            refine ⟨1905763222673459369242427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5082035260462558317979805 1905763222673459369242427)
            ·
              refine ⟨2858644834010189053863641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1905763222673459369242427 2858644834010189053863641)
              ·
                refine ⟨2143983625507641790397731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2858644834010189053863641 2143983625507641790397731)
                ·
                  refine ⟨3215975438261462685596597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2143983625507641790397731 3215975438261462685596597)
                  ·
                    refine ⟨301497697337012126774681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3215975438261462685596597 301497697337012126774681)
                    ·
                      rfl

theorem cell23_1761494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_1761494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761494 prefixEnd_1761494 := by exact prefixLift 1761494
  have htrace : WordTrace (prefixWord ++ tailWord_1761494) baseStart_1761494 baseEnd_1761494 := by
    simpa [prefixWord, tailWord_1761494, baseEnd_1761494] using wordTrace_append hprefix tailTrace_1761494
  have hstable : (prefixWord ++ tailWord_1761494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761494).length < 2 ^ (prefixWord ++ tailWord_1761494).sum := by decide
  have hdescent : baseEnd_1761494 < baseStart_1761494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761513 : List Nat := [1, 2, 1, 1, 1, 2, 2, 6, 1, 3, 3]
def baseStart_1761513 : Nat := 118140960795 + 1761513 * 2 ^ 59
def prefixEnd_1761513 : Nat := 4983230072969 + 3 ^ 40 * 1761513 * 2
def baseEnd_1761513 : Nat := 904502848143471805986455

theorem tailTrace_1761513 : CollatzResearch.WordTrace tailWord_1761513 prefixEnd_1761513 904502848143471805986455 := by
  unfold tailWord_1761513
  simp only [CollatzResearch.WordTrace]
  refine ⟨64247657267346718314217193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42831771511564478876144795 64247657267346718314217193)
  ·
    refine ⟨48185742950510038735662895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64247657267346718314217193 48185742950510038735662895)
    ·
      refine ⟨72278614425765058103494343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48185742950510038735662895 72278614425765058103494343)
      ·
        refine ⟨108417921638647587155241515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72278614425765058103494343 108417921638647587155241515)
        ·
          refine ⟨162626882457971380732862273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108417921638647587155241515 162626882457971380732862273)
          ·
            refine ⟨121970161843478535549646705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162626882457971380732862273 121970161843478535549646705)
            ·
              refine ⟨91477621382608901662235029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121970161843478535549646705 91477621382608901662235029)
              ·
                refine ⟨4288013502309792265417267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91477621382608901662235029 4288013502309792265417267)
                ·
                  refine ⟨6432020253464688398125901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4288013502309792265417267 6432020253464688398125901)
                  ·
                    refine ⟨2412007595049258149297213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6432020253464688398125901 2412007595049258149297213)
                    ·
                      refine ⟨904502848143471805986455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2412007595049258149297213 904502848143471805986455)
                      ·
                        rfl

theorem cell23_1761513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 3, 3].length) (baseStart_1761513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761513 prefixEnd_1761513 := by exact prefixLift 1761513
  have htrace : WordTrace (prefixWord ++ tailWord_1761513) baseStart_1761513 baseEnd_1761513 := by
    simpa [prefixWord, tailWord_1761513, baseEnd_1761513] using wordTrace_append hprefix tailTrace_1761513
  have hstable : (prefixWord ++ tailWord_1761513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761513).length < 2 ^ (prefixWord ++ tailWord_1761513).sum := by decide
  have hdescent : baseEnd_1761513 < baseStart_1761513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761514 : List Nat := [3, 1, 3, 1, 1, 2, 2, 5, 1, 2, 2]
def baseStart_1761514 : Nat := 118140960795 + 1761514 * 2 ^ 59
def prefixEnd_1761514 : Nat := 4983230072969 + 3 ^ 40 * 1761514 * 2
def baseEnd_1761514 : Nat := 904503361624126302073951

theorem tailTrace_1761514 : CollatzResearch.WordTrace tailWord_1761514 prefixEnd_1761514 904503361624126302073951 := by
  unfold tailWord_1761514
  simp only [CollatzResearch.WordTrace]
  refine ⟨16061923435085773871250899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42831795826895396990002397 16061923435085773871250899)
  ·
    refine ⟨24092885152628660806876349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16061923435085773871250899 24092885152628660806876349)
    ·
      refine ⟨9034831932235747802578631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24092885152628660806876349 9034831932235747802578631)
      ·
        refine ⟨13552247898353621703867947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9034831932235747802578631 13552247898353621703867947)
        ·
          refine ⟨20328371847530432555801921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13552247898353621703867947 20328371847530432555801921)
          ·
            refine ⟨15246278885647824416851441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20328371847530432555801921 15246278885647824416851441)
            ·
              refine ⟨11434709164235868312638581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15246278885647824416851441 11434709164235868312638581)
              ·
                refine ⟨1072003984147112654309867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11434709164235868312638581 1072003984147112654309867)
                ·
                  refine ⟨1608005976220668981464801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1072003984147112654309867 1608005976220668981464801)
                  ·
                    refine ⟨1206004482165501736098601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1608005976220668981464801 1206004482165501736098601)
                    ·
                      refine ⟨904503361624126302073951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1206004482165501736098601 904503361624126302073951)
                      ·
                        rfl

theorem cell23_1761514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_1761514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761514 prefixEnd_1761514 := by exact prefixLift 1761514
  have htrace : WordTrace (prefixWord ++ tailWord_1761514) baseStart_1761514 baseEnd_1761514 := by
    simpa [prefixWord, tailWord_1761514, baseEnd_1761514] using wordTrace_append hprefix tailTrace_1761514
  have hstable : (prefixWord ++ tailWord_1761514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761514).length < 2 ^ (prefixWord ++ tailWord_1761514).sum := by decide
  have hdescent : baseEnd_1761514 < baseStart_1761514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761517 : List Nat := [1, 5, 1, 2, 3, 2, 1, 1, 1, 1, 5]
def baseStart_1761517 : Nat := 118140960795 + 1761517 * 2 ^ 59
def prefixEnd_1761517 : Nat := 4983230072969 + 3 ^ 40 * 1761517 * 2
def baseEnd_1761517 : Nat := 904504902066089790336437

theorem tailTrace_1761517 : CollatzResearch.WordTrace tailWord_1761517 prefixEnd_1761517 904504902066089790336437 := by
  unfold tailWord_1761517
  simp only [CollatzResearch.WordTrace]
  refine ⟨64247803159332226997362805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42831868772888151331575203 64247803159332226997362805)
  ·
    refine ⟨6023231546187396281002763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64247803159332226997362805 6023231546187396281002763)
    ·
      refine ⟨9034847319281094421504145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6023231546187396281002763 9034847319281094421504145)
      ·
        refine ⟨6776135489460820816128109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9034847319281094421504145 6776135489460820816128109)
        ·
          refine ⟨2541050808547807806048041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6776135489460820816128109 2541050808547807806048041)
          ·
            refine ⟨1905788106410855854536031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2541050808547807806048041 1905788106410855854536031)
            ·
              refine ⟨2858682159616283781804047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1905788106410855854536031 2858682159616283781804047)
              ·
                refine ⟨4288023239424425672706071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2858682159616283781804047 4288023239424425672706071)
                ·
                  refine ⟨6432034859136638509059107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4288023239424425672706071 6432034859136638509059107)
                  ·
                    refine ⟨9648052288704957763588661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6432034859136638509059107 9648052288704957763588661)
                    ·
                      refine ⟨904504902066089790336437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9648052288704957763588661 904504902066089790336437)
                      ·
                        rfl

theorem cell23_1761517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_1761517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761517 prefixEnd_1761517 := by exact prefixLift 1761517
  have htrace : WordTrace (prefixWord ++ tailWord_1761517) baseStart_1761517 baseEnd_1761517 := by
    simpa [prefixWord, tailWord_1761517, baseEnd_1761517] using wordTrace_append hprefix tailTrace_1761517
  have hstable : (prefixWord ++ tailWord_1761517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761517).length < 2 ^ (prefixWord ++ tailWord_1761517).sum := by decide
  have hdescent : baseEnd_1761517 < baseStart_1761517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761583 : List Nat := [1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 4]
def baseStart_1761583 : Nat := 118140960795 + 1761583 * 2 ^ 59
def prefixEnd_1761583 : Nat := 4983230072969 + 3 ^ 40 * 1761583 * 2
def baseEnd_1761583 : Nat := 904538791789286532111133

theorem tailTrace_1761583 : CollatzResearch.WordTrace tailWord_1761583 prefixEnd_1761583 904538791789286532111133 := by
  unfold tailWord_1761583
  simp only [CollatzResearch.WordTrace]
  refine ⟨64250210377093120269265403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42833473584728746846176935 64250210377093120269265403)
  ·
    refine ⟨96375315565639680403898105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64250210377093120269265403 96375315565639680403898105)
    ·
      refine ⟨72281486674229760302923579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96375315565639680403898105 72281486674229760302923579)
      ·
        refine ⟨108422230011344640454385369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72281486674229760302923579 108422230011344640454385369)
        ·
          refine ⟨81316672508508480340789027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108422230011344640454385369 81316672508508480340789027)
          ·
            refine ⟨121975008762762720511183541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81316672508508480340789027 121975008762762720511183541)
            ·
              refine ⟨11435157071509005047923457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121975008762762720511183541 11435157071509005047923457)
              ·
                refine ⟨8576367803631753785942593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11435157071509005047923457 8576367803631753785942593)
                ·
                  refine ⟨6432275852723815339456945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8576367803631753785942593 6432275852723815339456945)
                  ·
                    refine ⟨4824206889542861504592709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6432275852723815339456945 4824206889542861504592709)
                    ·
                      refine ⟨904538791789286532111133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4824206889542861504592709 904538791789286532111133)
                      ·
                        rfl

theorem cell23_1761583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 4].length) (baseStart_1761583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761583 prefixEnd_1761583 := by exact prefixLift 1761583
  have htrace : WordTrace (prefixWord ++ tailWord_1761583) baseStart_1761583 baseEnd_1761583 := by
    simpa [prefixWord, tailWord_1761583, baseEnd_1761583] using wordTrace_append hprefix tailTrace_1761583
  have hstable : (prefixWord ++ tailWord_1761583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761583).length < 2 ^ (prefixWord ++ tailWord_1761583).sum := by decide
  have hdescent : baseEnd_1761583 < baseStart_1761583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761587 : List Nat := [1, 1, 1, 2, 5, 1, 3, 1, 4, 2, 2]
def baseStart_1761587 : Nat := 118140960795 + 1761587 * 2 ^ 59
def prefixEnd_1761587 : Nat := 4983230072969 + 3 ^ 40 * 1761587 * 2
def baseEnd_1761587 : Nat := 904540845711904516461115

theorem tailTrace_1761587 : CollatzResearch.WordTrace tailWord_1761587 prefixEnd_1761587 904540845711904516461115 := by
  unfold tailWord_1761587
  simp only [CollatzResearch.WordTrace]
  refine ⟨64250356269078628952411015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42833570846052419301607343 64250356269078628952411015)
  ·
    refine ⟨96375534403617943428616523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64250356269078628952411015 96375534403617943428616523)
    ·
      refine ⟨144563301605426915142924785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96375534403617943428616523 144563301605426915142924785)
      ·
        refine ⟨108422476204070186357193589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144563301605426915142924785 108422476204070186357193589)
        ·
          refine ⟨10164607144131579970986899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108422476204070186357193589 10164607144131579970986899)
          ·
            refine ⟨15246910716197369956480349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10164607144131579970986899 15246910716197369956480349)
            ·
              refine ⟨5717591518574013733680131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15246910716197369956480349 5717591518574013733680131)
              ·
                refine ⟨8576387277861020600520197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5717591518574013733680131 8576387277861020600520197)
                ·
                  refine ⟨1608072614598941362597537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8576387277861020600520197 1608072614598941362597537)
                  ·
                    refine ⟨1206054460949206021948153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1608072614598941362597537 1206054460949206021948153)
                    ·
                      refine ⟨904540845711904516461115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1206054460949206021948153 904540845711904516461115)
                      ·
                        rfl

theorem cell23_1761587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4, 2, 2].length) (baseStart_1761587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761587 prefixEnd_1761587 := by exact prefixLift 1761587
  have htrace : WordTrace (prefixWord ++ tailWord_1761587) baseStart_1761587 baseEnd_1761587 := by
    simpa [prefixWord, tailWord_1761587, baseEnd_1761587] using wordTrace_append hprefix tailTrace_1761587
  have hstable : (prefixWord ++ tailWord_1761587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761587).length < 2 ^ (prefixWord ++ tailWord_1761587).sum := by decide
  have hdescent : baseEnd_1761587 < baseStart_1761587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761623 : List Nat := [1, 1, 3, 2, 3, 1, 1, 3, 1, 7]
def baseStart_1761623 : Nat := 118140960795 + 1761623 * 2 ^ 59
def prefixEnd_1761623 : Nat := 4983230072969 + 3 ^ 40 * 1761623 * 2
def baseEnd_1761623 : Nat := 301519777005155458536983

theorem tailTrace_1761623 : CollatzResearch.WordTrace tailWord_1761623 prefixEnd_1761623 301519777005155458536983 := by
  unfold tailWord_1761623
  simp only [CollatzResearch.WordTrace]
  refine ⟨64251669296948207100721523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42834446197965471400481015 64251669296948207100721523)
  ·
    refine ⟨96377503945422310651082285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64251669296948207100721523 96377503945422310651082285)
    ·
      refine ⟨36141563979533366494155857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96377503945422310651082285 36141563979533366494155857)
      ·
        refine ⟨27106172984650024870616893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36141563979533366494155857 27106172984650024870616893)
        ·
          refine ⟨10164814869243759326481335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27106172984650024870616893 10164814869243759326481335)
          ·
            refine ⟨15247222303865638989722003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10164814869243759326481335 15247222303865638989722003)
            ·
              refine ⟨22870833455798458484583005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15247222303865638989722003 22870833455798458484583005)
              ·
                refine ⟨8576562545924421931718627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22870833455798458484583005 8576562545924421931718627)
                ·
                  refine ⟨12864843818886632897577941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8576562545924421931718627 12864843818886632897577941)
                  ·
                    refine ⟨301519777005155458536983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12864843818886632897577941 301519777005155458536983)
                    ·
                      rfl

theorem cell23_1761623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 7].length) (baseStart_1761623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761623 prefixEnd_1761623 := by exact prefixLift 1761623
  have htrace : WordTrace (prefixWord ++ tailWord_1761623) baseStart_1761623 baseEnd_1761623 := by
    simpa [prefixWord, tailWord_1761623, baseEnd_1761623] using wordTrace_append hprefix tailTrace_1761623
  have hstable : (prefixWord ++ tailWord_1761623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761623).length < 2 ^ (prefixWord ++ tailWord_1761623).sum := by decide
  have hdescent : baseEnd_1761623 < baseStart_1761623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761640 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 4, 5]
def baseStart_1761640 : Nat := 118140960795 + 1761640 * 2 ^ 59
def prefixEnd_1761640 : Nat := 4983230072969 + 3 ^ 40 * 1761640 * 2
def baseEnd_1761640 : Nat := 301522686728864269699457

theorem tailTrace_1761640 : CollatzResearch.WordTrace tailWord_1761640 prefixEnd_1761640 301522686728864269699457 := by
  unfold tailWord_1761640
  simp only [CollatzResearch.WordTrace]
  refine ⟨32126144668943309502045187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42834859558591079336060249 32126144668943309502045187)
  ·
    refine ⟨48189217003414964253067781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32126144668943309502045187 48189217003414964253067781)
    ·
      refine ⟨9035478188140305797450209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48189217003414964253067781 9035478188140305797450209)
      ·
        refine ⟨6776608641105229348087657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9035478188140305797450209 6776608641105229348087657)
        ·
          refine ⟨5082456480828922011065743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6776608641105229348087657 5082456480828922011065743)
          ·
            refine ⟨7623684721243383016598615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5082456480828922011065743 7623684721243383016598615)
            ·
              refine ⟨11435527081865074524897923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7623684721243383016598615 11435527081865074524897923)
              ·
                refine ⟨17153290622797611787346885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11435527081865074524897923 17153290622797611787346885)
                ·
                  refine ⟨3216241991774552210127541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17153290622797611787346885 3216241991774552210127541)
                  ·
                    refine ⟨301522686728864269699457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3216241991774552210127541 301522686728864269699457)
                    ·
                      rfl

theorem cell23_1761640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_1761640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761640 prefixEnd_1761640 := by exact prefixLift 1761640
  have htrace : WordTrace (prefixWord ++ tailWord_1761640) baseStart_1761640 baseEnd_1761640 := by
    simpa [prefixWord, tailWord_1761640, baseEnd_1761640] using wordTrace_append hprefix tailTrace_1761640
  have hstable : (prefixWord ++ tailWord_1761640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761640).length < 2 ^ (prefixWord ++ tailWord_1761640).sum := by decide
  have hdescent : baseEnd_1761640 < baseStart_1761640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761644 : List Nat := [2, 2, 1, 1, 6, 1, 3, 2, 5]
def baseStart_1761644 : Nat := 118140960795 + 1761644 * 2 ^ 59
def prefixEnd_1761644 : Nat := 4983230072969 + 3 ^ 40 * 1761644 * 2
def baseEnd_1761644 : Nat := 100507790456578977049817

theorem tailTrace_1761644 : CollatzResearch.WordTrace tailWord_1761644 prefixEnd_1761644 100507790456578977049817 := by
  unfold tailWord_1761644
  simp only [CollatzResearch.WordTrace]
  refine ⟨32126217614936063843617993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42834956819914751791490657 32126217614936063843617993)
  ·
    refine ⟨24094663211202047882713495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32126217614936063843617993 24094663211202047882713495)
    ·
      refine ⟨36141994816803071824070243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24094663211202047882713495 36141994816803071824070243)
      ·
        refine ⟨54212992225204607736105365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36141994816803071824070243 54212992225204607736105365)
        ·
          refine ⟨2541234010556465987629939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54212992225204607736105365 2541234010556465987629939)
          ·
            refine ⟨3811851015834698981444909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2541234010556465987629939 3811851015834698981444909)
            ·
              refine ⟨1429444130938012118041841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3811851015834698981444909 1429444130938012118041841)
              ·
                refine ⟨1072083098203509088531381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1429444130938012118041841 1072083098203509088531381)
                ·
                  refine ⟨100507790456578977049817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1072083098203509088531381 100507790456578977049817)
                  ·
                    rfl

theorem cell23_1761644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2, 5].length) (baseStart_1761644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761644 prefixEnd_1761644 := by exact prefixLift 1761644
  have htrace : WordTrace (prefixWord ++ tailWord_1761644) baseStart_1761644 baseEnd_1761644 := by
    simpa [prefixWord, tailWord_1761644, baseEnd_1761644] using wordTrace_append hprefix tailTrace_1761644
  have hstable : (prefixWord ++ tailWord_1761644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761644).length < 2 ^ (prefixWord ++ tailWord_1761644).sum := by decide
  have hdescent : baseEnd_1761644 < baseStart_1761644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761650 : List Nat := [3, 2, 1, 2, 1, 4, 1, 1, 1, 2, 5]
def baseStart_1761650 : Nat := 118140960795 + 1761650 * 2 ^ 59
def prefixEnd_1761650 : Nat := 4983230072969 + 3 ^ 40 * 1761650 * 2
def baseEnd_1761650 : Nat := 904573194993137769973325

theorem tailTrace_1761650 : CollatzResearch.WordTrace tailWord_1761650 prefixEnd_1761650 904573194993137769973325 := by
  unfold tailWord_1761650
  simp only [CollatzResearch.WordTrace]
  refine ⟨16063163516962597677988601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42835102711900260474636269 16063163516962597677988601)
  ·
    refine ⟨12047372637721948258491451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16063163516962597677988601 12047372637721948258491451)
    ·
      refine ⟨18071058956582922387737177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12047372637721948258491451 18071058956582922387737177)
      ·
        refine ⟨13553294217437191790802883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18071058956582922387737177 13553294217437191790802883)
        ·
          refine ⟨20329941326155787686204325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13553294217437191790802883 20329941326155787686204325)
          ·
            refine ⟨3811863998654210191163311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20329941326155787686204325 3811863998654210191163311)
            ·
              refine ⟨5717795997981315286744967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3811863998654210191163311 5717795997981315286744967)
              ·
                refine ⟨8576693996971972930117451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5717795997981315286744967 8576693996971972930117451)
                ·
                  refine ⟨12865040995457959395176177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8576693996971972930117451 12865040995457959395176177)
                  ·
                    refine ⟨9648780746593469546382133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12865040995457959395176177 9648780746593469546382133)
                    ·
                      refine ⟨904573194993137769973325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9648780746593469546382133 904573194993137769973325)
                      ·
                        rfl

theorem cell23_1761650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_1761650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761650 prefixEnd_1761650 := by exact prefixLift 1761650
  have htrace : WordTrace (prefixWord ++ tailWord_1761650) baseStart_1761650 baseEnd_1761650 := by
    simpa [prefixWord, tailWord_1761650, baseEnd_1761650] using wordTrace_append hprefix tailTrace_1761650
  have hstable : (prefixWord ++ tailWord_1761650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761650).length < 2 ^ (prefixWord ++ tailWord_1761650).sum := by decide
  have hdescent : baseEnd_1761650 < baseStart_1761650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761674 : List Nat := [3, 1, 2, 5, 1, 1, 2, 1, 2, 5]
def baseStart_1761674 : Nat := 118140960795 + 1761674 * 2 ^ 59
def prefixEnd_1761674 : Nat := 4983230072969 + 3 ^ 40 * 1761674 * 2
def baseEnd_1761674 : Nat := 301528506176281892024405

theorem tailTrace_1761674 : CollatzResearch.WordTrace tailWord_1761674 prefixEnd_1761674 301528506176281892024405 := by
  unfold tailWord_1761674
  simp only [CollatzResearch.WordTrace]
  refine ⟨16063382354940860702707019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42835686279842295207218717 16063382354940860702707019)
  ·
    refine ⟨24095073532411291054060529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16063382354940860702707019 24095073532411291054060529)
    ·
      refine ⟨18071305149308468290545397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24095073532411291054060529 18071305149308468290545397)
      ·
        refine ⟨1694184857747668902238631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18071305149308468290545397 1694184857747668902238631)
        ·
          refine ⟨2541277286621503353357947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1694184857747668902238631 2541277286621503353357947)
          ·
            refine ⟨3811915929932255030036921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2541277286621503353357947 3811915929932255030036921)
            ·
              refine ⟨2858936947449191272527691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3811915929932255030036921 2858936947449191272527691)
              ·
                refine ⟨4288405421173786908791537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2858936947449191272527691 4288405421173786908791537)
                ·
                  refine ⟨3216304065880340181593653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4288405421173786908791537 3216304065880340181593653)
                  ·
                    refine ⟨301528506176281892024405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3216304065880340181593653 301528506176281892024405)
                    ·
                      rfl

theorem cell23_1761674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_1761674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761674 prefixEnd_1761674 := by exact prefixLift 1761674
  have htrace : WordTrace (prefixWord ++ tailWord_1761674) baseStart_1761674 baseEnd_1761674 := by
    simpa [prefixWord, tailWord_1761674, baseEnd_1761674] using wordTrace_append hprefix tailTrace_1761674
  have hstable : (prefixWord ++ tailWord_1761674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761674).length < 2 ^ (prefixWord ++ tailWord_1761674).sum := by decide
  have hdescent : baseEnd_1761674 < baseStart_1761674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761694 : List Nat := [4, 3, 1, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_1761694 : Nat := 118140960795 + 1761694 * 2 ^ 59
def prefixEnd_1761694 : Nat := 4983230072969 + 3 ^ 40 * 1761694 * 2
def baseEnd_1761694 : Nat := 904595788141935597823123

theorem tailTrace_1761694 : CollatzResearch.WordTrace tailWord_1761694 prefixEnd_1761694 904595788141935597823123 := by
  unfold tailWord_1761694
  simp only [CollatzResearch.WordTrace]
  refine ⟨8031782359961373278319517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42836172586460657484370757 8031782359961373278319517)
  ·
    refine ⟨3011918384985514979369819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8031782359961373278319517 3011918384985514979369819)
    ·
      refine ⟨4517877577478272469054729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3011918384985514979369819 4517877577478272469054729)
      ·
        refine ⟨3388408183108704351791047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4517877577478272469054729 3388408183108704351791047)
        ·
          refine ⟨5082612274663056527686571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3388408183108704351791047 5082612274663056527686571)
          ·
            refine ⟨7623918411994584791529857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5082612274663056527686571 7623918411994584791529857)
            ·
              refine ⟨5717938808995938593647393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7623918411994584791529857 5717938808995938593647393)
              ·
                refine ⟨4288454106746953945235545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5717938808995938593647393 4288454106746953945235545)
                ·
                  refine ⟨3216340580060215458926659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4288454106746953945235545 3216340580060215458926659)
                  ·
                    refine ⟨4824510870090323188389989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3216340580060215458926659 4824510870090323188389989)
                    ·
                      refine ⟨904595788141935597823123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4824510870090323188389989 904595788141935597823123)
                      ·
                        rfl

theorem cell23_1761694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_1761694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761694 prefixEnd_1761694 := by exact prefixLift 1761694
  have htrace : WordTrace (prefixWord ++ tailWord_1761694) baseStart_1761694 baseEnd_1761694 := by
    simpa [prefixWord, tailWord_1761694, baseEnd_1761694] using wordTrace_append hprefix tailTrace_1761694
  have hstable : (prefixWord ++ tailWord_1761694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761694).length < 2 ^ (prefixWord ++ tailWord_1761694).sum := by decide
  have hdescent : baseEnd_1761694 < baseStart_1761694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761700 : List Nat := [2, 3, 1, 2, 1, 1, 3, 4, 6]
def baseStart_1761700 : Nat := 118140960795 + 1761700 * 2 ^ 59
def prefixEnd_1761700 : Nat := 4983230072969 + 3 ^ 40 * 1761700 * 2
def baseEnd_1761700 : Nat := 100510985447318063816455

theorem tailTrace_1761700 : CollatzResearch.WordTrace tailWord_1761700 prefixEnd_1761700 100510985447318063816455 := by
  unfold tailWord_1761700
  simp only [CollatzResearch.WordTrace]
  refine ⟨32127238858834624625637277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42836318478446166167516369 32127238858834624625637277)
  ·
    refine ⟨12047714572062984234613979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32127238858834624625637277 12047714572062984234613979)
    ·
      refine ⟨18071571858094476351920969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12047714572062984234613979 18071571858094476351920969)
      ·
        refine ⟨13553678893570857263940727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18071571858094476351920969 13553678893570857263940727)
        ·
          refine ⟨20330518340356285895911091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13553678893570857263940727 20330518340356285895911091)
          ·
            refine ⟨30495777510534428843866637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20330518340356285895911091 30495777510534428843866637)
            ·
              refine ⟨11435916566450410816449989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30495777510534428843866637 11435916566450410816449989)
              ·
                refine ⟨2144234356209452028084373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11435916566450410816449989 2144234356209452028084373)
                ·
                  refine ⟨100510985447318063816455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2144234356209452028084373 100510985447318063816455)
                  ·
                    rfl

theorem cell23_1761700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 6].length) (baseStart_1761700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761700 prefixEnd_1761700 := by exact prefixLift 1761700
  have htrace : WordTrace (prefixWord ++ tailWord_1761700) baseStart_1761700 baseEnd_1761700 := by
    simpa [prefixWord, tailWord_1761700, baseEnd_1761700] using wordTrace_append hprefix tailTrace_1761700
  have hstable : (prefixWord ++ tailWord_1761700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761700).length < 2 ^ (prefixWord ++ tailWord_1761700).sum := by decide
  have hdescent : baseEnd_1761700 < baseStart_1761700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761781 : List Nat := [1, 3, 5, 1, 2, 1, 2, 2, 1, 5]
def baseStart_1761781 : Nat := 118140960795 + 1761781 * 2 ^ 59
def prefixEnd_1761781 : Nat := 4983230072969 + 3 ^ 40 * 1761781 * 2
def baseEnd_1761781 : Nat := 301546820319625585811741

theorem tailTrace_1761781 : CollatzResearch.WordTrace tailWord_1761781 prefixEnd_1761781 301546820319625585811741 := by
  unfold tailWord_1761781
  simp only [CollatzResearch.WordTrace]
  refine ⟨64257432030375800084973197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42838288020250533389982131 64257432030375800084973197)
  ·
    refine ⟨24096537011390925031864949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64257432030375800084973197 24096537011390925031864949)
    ·
      refine ⟨2259050344817899221737339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24096537011390925031864949 2259050344817899221737339)
      ·
        refine ⟨3388575517226848832606009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2259050344817899221737339 3388575517226848832606009)
        ·
          refine ⟨2541431637920136624454507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3388575517226848832606009 2541431637920136624454507)
          ·
            refine ⟨3812147456880204936681761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2541431637920136624454507 3812147456880204936681761)
            ·
              refine ⟨2859110592660153702511321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3812147456880204936681761 2859110592660153702511321)
              ·
                refine ⟨2144332944495115276883491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2859110592660153702511321 2144332944495115276883491)
                ·
                  refine ⟨3216499416742672915325237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2144332944495115276883491 3216499416742672915325237)
                  ·
                    refine ⟨301546820319625585811741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3216499416742672915325237 301546820319625585811741)
                    ·
                      rfl

theorem cell23_1761781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_1761781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761781 prefixEnd_1761781 := by exact prefixLift 1761781
  have htrace : WordTrace (prefixWord ++ tailWord_1761781) baseStart_1761781 baseEnd_1761781 := by
    simpa [prefixWord, tailWord_1761781, baseEnd_1761781] using wordTrace_append hprefix tailTrace_1761781
  have hstable : (prefixWord ++ tailWord_1761781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761781).length < 2 ^ (prefixWord ++ tailWord_1761781).sum := by decide
  have hdescent : baseEnd_1761781 < baseStart_1761781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761784 : List Nat := [2, 1, 2, 1, 1, 4, 1, 4, 3, 2, 2]
def baseStart_1761784 : Nat := 118140960795 + 1761784 * 2 ^ 59
def prefixEnd_1761784 : Nat := 4983230072969 + 3 ^ 40 * 1761784 * 2
def baseEnd_1761784 : Nat := 904642001400840245697709

theorem tailTrace_1761784 : CollatzResearch.WordTrace tailWord_1761784 prefixEnd_1761784 904642001400840245697709 := by
  unfold tailWord_1761784
  simp only [CollatzResearch.WordTrace]
  refine ⟨32128770724682465798666203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42838360966243287731554937 32128770724682465798666203)
  ·
    refine ⟨48193156087023698697999305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32128770724682465798666203 48193156087023698697999305)
    ·
      refine ⟨36144867065267774023499479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48193156087023698697999305 36144867065267774023499479)
      ·
        refine ⟨54217300597901661035249219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36144867065267774023499479 54217300597901661035249219)
        ·
          refine ⟨81325950896852491552873829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54217300597901661035249219 81325950896852491552873829)
          ·
            refine ⟨15248615793159842166163843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81325950896852491552873829 15248615793159842166163843)
            ·
              refine ⟨22872923689739763249245765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15248615793159842166163843 22872923689739763249245765)
              ·
                refine ⟨4288673191826205609233581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22872923689739763249245765 4288673191826205609233581)
                ·
                  refine ⟨1608252446934827103462593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4288673191826205609233581 1608252446934827103462593)
                  ·
                    refine ⟨1206189335201120327596945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1608252446934827103462593 1206189335201120327596945)
                    ·
                      refine ⟨904642001400840245697709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1206189335201120327596945 904642001400840245697709)
                      ·
                        rfl

theorem cell23_1761784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 3, 2, 2].length) (baseStart_1761784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761784 prefixEnd_1761784 := by exact prefixLift 1761784
  have htrace : WordTrace (prefixWord ++ tailWord_1761784) baseStart_1761784 baseEnd_1761784 := by
    simpa [prefixWord, tailWord_1761784, baseEnd_1761784] using wordTrace_append hprefix tailTrace_1761784
  have hstable : (prefixWord ++ tailWord_1761784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761784).length < 2 ^ (prefixWord ++ tailWord_1761784).sum := by decide
  have hdescent : baseEnd_1761784 < baseStart_1761784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761798 : List Nat := [6, 2, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_1761798 : Nat := 118140960795 + 1761798 * 2 ^ 59
def prefixEnd_1761798 : Nat := 4983230072969 + 3 ^ 40 * 1761798 * 2
def baseEnd_1761798 : Nat := 301549730043334396974215

theorem tailTrace_1761798 : CollatzResearch.WordTrace tailWord_1761798 prefixEnd_1761798 301549730043334396974215 := by
  unfold tailWord_1761798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2008064127228569124635689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42838701380876141325561365 2008064127228569124635689)
  ·
    refine ⟨1506048095421426843476767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2008064127228569124635689 1506048095421426843476767)
    ·
      refine ⟨2259072143132140265215151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1506048095421426843476767 2259072143132140265215151)
      ·
        refine ⟨3388608214698210397822727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2259072143132140265215151 3388608214698210397822727)
        ·
          refine ⟨5082912322047315596734091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3388608214698210397822727 5082912322047315596734091)
          ·
            refine ⟨7624368483070973395101137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5082912322047315596734091 7624368483070973395101137)
            ·
              refine ⟨5718276362303230046325853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7624368483070973395101137 5718276362303230046325853)
              ·
                refine ⟨2144353635863711267372195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5718276362303230046325853 2144353635863711267372195)
                ·
                  refine ⟨3216530453795566901058293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2144353635863711267372195 3216530453795566901058293)
                  ·
                    refine ⟨301549730043334396974215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3216530453795566901058293 301549730043334396974215)
                    ·
                      rfl

theorem cell23_1761798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_1761798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761798 prefixEnd_1761798 := by exact prefixLift 1761798
  have htrace : WordTrace (prefixWord ++ tailWord_1761798) baseStart_1761798 baseEnd_1761798 := by
    simpa [prefixWord, tailWord_1761798, baseEnd_1761798] using wordTrace_append hprefix tailTrace_1761798
  have hstable : (prefixWord ++ tailWord_1761798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761798).length < 2 ^ (prefixWord ++ tailWord_1761798).sum := by decide
  have hdescent : baseEnd_1761798 < baseStart_1761798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761801 : List Nat := [1, 2, 1, 1, 3, 1, 2, 7, 1, 2, 2]
def baseStart_1761801 : Nat := 118140960795 + 1761801 * 2 ^ 59
def prefixEnd_1761801 : Nat := 4983230072969 + 3 ^ 40 * 1761801 * 2
def baseEnd_1761801 : Nat := 904650730571966679185131

theorem tailTrace_1761801 : CollatzResearch.WordTrace tailWord_1761801 prefixEnd_1761801 904650730571966679185131 := by
  unfold tailWord_1761801
  simp only [CollatzResearch.WordTrace]
  refine ⟨64258161490303343500701257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42838774326868895667134171 64258161490303343500701257)
  ·
    refine ⟨48193621117727507625525943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64258161490303343500701257 48193621117727507625525943)
    ·
      refine ⟨72290431676591261438288915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48193621117727507625525943 72290431676591261438288915)
      ·
        refine ⟨108435647514886892157433373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72290431676591261438288915 108435647514886892157433373)
        ·
          refine ⟨40663367818082584559037515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108435647514886892157433373 40663367818082584559037515)
          ·
            refine ⟨60995051727123876838556273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40663367818082584559037515 60995051727123876838556273)
            ·
              refine ⟨45746288795342907628917205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60995051727123876838556273 45746288795342907628917205)
              ·
                refine ⟨1072178643640849397552747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 45746288795342907628917205 1072178643640849397552747)
                ·
                  refine ⟨1608267965461274096329121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1072178643640849397552747 1608267965461274096329121)
                  ·
                    refine ⟨1206200974095955572246841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1608267965461274096329121 1206200974095955572246841)
                    ·
                      refine ⟨904650730571966679185131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1206200974095955572246841 904650730571966679185131)
                      ·
                        rfl

theorem cell23_1761801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7, 1, 2, 2].length) (baseStart_1761801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761801 prefixEnd_1761801 := by exact prefixLift 1761801
  have htrace : WordTrace (prefixWord ++ tailWord_1761801) baseStart_1761801 baseEnd_1761801 := by
    simpa [prefixWord, tailWord_1761801, baseEnd_1761801] using wordTrace_append hprefix tailTrace_1761801
  have hstable : (prefixWord ++ tailWord_1761801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761801).length < 2 ^ (prefixWord ++ tailWord_1761801).sum := by decide
  have hdescent : baseEnd_1761801 < baseStart_1761801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761804 : List Nat := [2, 2, 1, 2, 4, 1, 2, 3, 1, 2, 3]
def baseStart_1761804 : Nat := 118140960795 + 1761804 * 2 ^ 59
def prefixEnd_1761804 : Nat := 4983230072969 + 3 ^ 40 * 1761804 * 2
def baseEnd_1761804 : Nat := 904652271013930167447617

theorem tailTrace_1761804 : CollatzResearch.WordTrace tailWord_1761804 prefixEnd_1761804 904652271013930167447617 := by
  unfold tailWord_1761804
  simp only [CollatzResearch.WordTrace]
  refine ⟨32129135454646237506530233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42838847272861650008706977 32129135454646237506530233)
  ·
    refine ⟨24096851590984678129897675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32129135454646237506530233 24096851590984678129897675)
    ·
      refine ⟨36145277386477017194846513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24096851590984678129897675 36145277386477017194846513)
      ·
        refine ⟨27108958039857762896134885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36145277386477017194846513 27108958039857762896134885)
        ·
          refine ⟨5082929632473330543025291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27108958039857762896134885 5082929632473330543025291)
          ·
            refine ⟨7624394448709995814537937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5082929632473330543025291 7624394448709995814537937)
            ·
              refine ⟨5718295836532496860903453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7624394448709995814537937 5718295836532496860903453)
              ·
                refine ⟨2144360938699686322838795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5718295836532496860903453 2144360938699686322838795)
                ·
                  refine ⟨3216541408049529484258193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2144360938699686322838795 3216541408049529484258193)
                  ·
                    refine ⟨2412406056037147113193645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3216541408049529484258193 2412406056037147113193645)
                    ·
                      refine ⟨904652271013930167447617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2412406056037147113193645 904652271013930167447617)
                      ·
                        rfl

theorem cell23_1761804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_1761804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761804 prefixEnd_1761804 := by exact prefixLift 1761804
  have htrace : WordTrace (prefixWord ++ tailWord_1761804) baseStart_1761804 baseEnd_1761804 := by
    simpa [prefixWord, tailWord_1761804, baseEnd_1761804] using wordTrace_append hprefix tailTrace_1761804
  have hstable : (prefixWord ++ tailWord_1761804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761804).length < 2 ^ (prefixWord ++ tailWord_1761804).sum := by decide
  have hdescent : baseEnd_1761804 < baseStart_1761804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761838 : List Nat := [4, 1, 3, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_1761838 : Nat := 118140960795 + 1761838 * 2 ^ 59
def prefixEnd_1761838 : Nat := 4983230072969 + 3 ^ 40 * 1761838 * 2
def baseEnd_1761838 : Nat := 904669729356183034422461

theorem tailTrace_1761838 : CollatzResearch.WordTrace tailWord_1761838 prefixEnd_1761838 904669729356183034422461 := by
  unfold tailWord_1761838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8032438873896162352474771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42839673994112865879865445 8032438873896162352474771)
  ·
    refine ⟨12048658310844243528712157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8032438873896162352474771 12048658310844243528712157)
    ·
      refine ⟨4518246866566591323267059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12048658310844243528712157 4518246866566591323267059)
      ·
        refine ⟨6777370299849886984900589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4518246866566591323267059 6777370299849886984900589)
        ·
          refine ⟨2541513862443707619337721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6777370299849886984900589 2541513862443707619337721)
          ·
            refine ⟨1906135396832780714503291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2541513862443707619337721 1906135396832780714503291)
            ·
              refine ⟨2859203095249171071754937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1906135396832780714503291 2859203095249171071754937)
              ·
                refine ⟨2144402321436878303816203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2859203095249171071754937 2144402321436878303816203)
                ·
                  refine ⟨3216603482155317455724305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2144402321436878303816203 3216603482155317455724305)
                  ·
                    refine ⟨2412452611616488091793229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3216603482155317455724305 2412452611616488091793229)
                    ·
                      refine ⟨904669729356183034422461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2412452611616488091793229 904669729356183034422461)
                      ·
                        rfl

theorem cell23_1761838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_1761838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761838 prefixEnd_1761838 := by exact prefixLift 1761838
  have htrace : WordTrace (prefixWord ++ tailWord_1761838) baseStart_1761838 baseEnd_1761838 := by
    simpa [prefixWord, tailWord_1761838, baseEnd_1761838] using wordTrace_append hprefix tailTrace_1761838
  have hstable : (prefixWord ++ tailWord_1761838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761838).length < 2 ^ (prefixWord ++ tailWord_1761838).sum := by decide
  have hdescent : baseEnd_1761838 < baseStart_1761838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761874 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 3, 4, 2]
def baseStart_1761874 : Nat := 118140960795 + 1761874 * 2 ^ 59
def prefixEnd_1761874 : Nat := 4983230072969 + 3 ^ 40 * 1761874 * 2
def baseEnd_1761874 : Nat := 904688214659744893572295

theorem tailTrace_1761874 : CollatzResearch.WordTrace tailWord_1761874 prefixEnd_1761874 904688214659744893572295 := by
  unfold tailWord_1761874
  simp only [CollatzResearch.WordTrace]
  refine ⟨16065206004759719242027169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42840549346025917978739117 16065206004759719242027169)
  ·
    refine ⟨12048904503569789431520377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16065206004759719242027169 12048904503569789431520377)
    ·
      refine ⟨9036678377677342073640283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12048904503569789431520377 9036678377677342073640283)
      ·
        refine ⟨13555017566516013110460425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9036678377677342073640283 13555017566516013110460425)
        ·
          refine ⟨10166263174887009832845319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13555017566516013110460425 10166263174887009832845319)
          ·
            refine ⟨15249394762330514749267979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10166263174887009832845319 15249394762330514749267979)
            ·
              refine ⟨22874092143495772123901969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15249394762330514749267979 22874092143495772123901969)
              ·
                refine ⟨17155569107621829092926477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22874092143495772123901969 17155569107621829092926477)
                ·
                  refine ⟨6433338415358185909847429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17155569107621829092926477 6433338415358185909847429)
                  ·
                    refine ⟨1206250952879659858096393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6433338415358185909847429 1206250952879659858096393)
                    ·
                      refine ⟨904688214659744893572295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1206250952879659858096393 904688214659744893572295)
                      ·
                        rfl

theorem cell23_1761874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_1761874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761874 prefixEnd_1761874 := by exact prefixLift 1761874
  have htrace : WordTrace (prefixWord ++ tailWord_1761874) baseStart_1761874 baseEnd_1761874 := by
    simpa [prefixWord, tailWord_1761874, baseEnd_1761874] using wordTrace_append hprefix tailTrace_1761874
  have hstable : (prefixWord ++ tailWord_1761874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761874).length < 2 ^ (prefixWord ++ tailWord_1761874).sum := by decide
  have hdescent : baseEnd_1761874 < baseStart_1761874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761877 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 2, 4, 3]
def baseStart_1761877 : Nat := 118140960795 + 1761877 * 2 ^ 59
def prefixEnd_1761877 : Nat := 4983230072969 + 3 ^ 40 * 1761877 * 2
def baseEnd_1761877 : Nat := 904689755101708381834781

theorem tailTrace_1761877 : CollatzResearch.WordTrace tailWord_1761877 prefixEnd_1761877 904689755101708381834781 := by
  unfold tailWord_1761877
  simp only [CollatzResearch.WordTrace]
  refine ⟨64260933438028008480467885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42840622292018672320311923 64260933438028008480467885)
  ·
    refine ⟨24097850039260503180175457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64260933438028008480467885 24097850039260503180175457)
    ·
      refine ⟨18073387529445377385131593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24097850039260503180175457 18073387529445377385131593)
      ·
        refine ⟨13555040647084033038848695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18073387529445377385131593 13555040647084033038848695)
        ·
          refine ⟨20332560970626049558273043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13555040647084033038848695 20332560970626049558273043)
          ·
            refine ⟨30498841455939074337409565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20332560970626049558273043 30498841455939074337409565)
            ·
              refine ⟨11437065545977152876528587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30498841455939074337409565 11437065545977152876528587)
              ·
                refine ⟨17155598318965729314792881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11437065545977152876528587 17155598318965729314792881)
                ·
                  refine ⟨12866698739224296986094661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17155598318965729314792881 12866698739224296986094661)
                  ·
                    refine ⟨2412506013604555684892749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12866698739224296986094661 2412506013604555684892749)
                    ·
                      refine ⟨904689755101708381834781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2412506013604555684892749 904689755101708381834781)
                      ·
                        rfl

theorem cell23_1761877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_1761877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761877 prefixEnd_1761877 := by exact prefixLift 1761877
  have htrace : WordTrace (prefixWord ++ tailWord_1761877) baseStart_1761877 baseEnd_1761877 := by
    simpa [prefixWord, tailWord_1761877, baseEnd_1761877] using wordTrace_append hprefix tailTrace_1761877
  have hstable : (prefixWord ++ tailWord_1761877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761877).length < 2 ^ (prefixWord ++ tailWord_1761877).sum := by decide
  have hdescent : baseEnd_1761877 < baseStart_1761877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761884 : List Nat := [2, 2, 4, 1, 3, 1, 1, 1, 2, 6]
def baseStart_1761884 : Nat := 118140960795 + 1761884 * 2 ^ 59
def prefixEnd_1761884 : Nat := 4983230072969 + 3 ^ 40 * 1761884 * 2
def baseEnd_1761884 : Nat := 301564449822096618149083

theorem tailTrace_1761884 : CollatzResearch.WordTrace tailWord_1761884 prefixEnd_1761884 301564449822096618149083 := by
  unfold tailWord_1761884
  simp only [CollatzResearch.WordTrace]
  refine ⟨32130594374501324337986353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42840792499335099117315137 32130594374501324337986353)
  ·
    refine ⟨24097945780875993253489765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32130594374501324337986353 24097945780875993253489765)
    ·
      refine ⟨4518364833914248735029331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24097945780875993253489765 4518364833914248735029331)
      ·
        refine ⟨6777547250871373102543997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4518364833914248735029331 6777547250871373102543997)
        ·
          refine ⟨2541580219076764913453999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6777547250871373102543997 2541580219076764913453999)
          ·
            refine ⟨3812370328615147370180999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2541580219076764913453999 3812370328615147370180999)
            ·
              refine ⟨5718555492922721055271499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3812370328615147370180999 5718555492922721055271499)
              ·
                refine ⟨8577833239384081582907249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5718555492922721055271499 8577833239384081582907249)
                ·
                  refine ⟨6433374929538061187180437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8577833239384081582907249 6433374929538061187180437)
                  ·
                    refine ⟨301564449822096618149083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6433374929538061187180437 301564449822096618149083)
                    ·
                      rfl

theorem cell23_1761884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_1761884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761884 prefixEnd_1761884 := by exact prefixLift 1761884
  have htrace : WordTrace (prefixWord ++ tailWord_1761884) baseStart_1761884 baseEnd_1761884 := by
    simpa [prefixWord, tailWord_1761884, baseEnd_1761884] using wordTrace_append hprefix tailTrace_1761884
  have hstable : (prefixWord ++ tailWord_1761884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761884).length < 2 ^ (prefixWord ++ tailWord_1761884).sum := by decide
  have hdescent : baseEnd_1761884 < baseStart_1761884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761891 : List Nat := [1, 1, 1, 5, 1, 2, 1, 5, 2, 2, 2]
def baseStart_1761891 : Nat := 118140960795 + 1761891 * 2 ^ 59
def prefixEnd_1761891 : Nat := 4983230072969 + 3 ^ 40 * 1761891 * 2
def baseEnd_1761891 : Nat := 904696943830871327059717

theorem tailTrace_1761891 : CollatzResearch.WordTrace tailWord_1761891 prefixEnd_1761891 904696943830871327059717 := by
  unfold tailWord_1761891
  simp only [CollatzResearch.WordTrace]
  refine ⟨64261444059977288871477527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42840962706651525914318351 64261444059977288871477527)
  ·
    refine ⟨96392166089965933307216291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64261444059977288871477527 96392166089965933307216291)
    ·
      refine ⟨144588249134948899960824437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96392166089965933307216291 144588249134948899960824437)
      ·
        refine ⟨13555148356401459371327291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144588249134948899960824437 13555148356401459371327291)
        ·
          refine ⟨20332722534602189056990937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13555148356401459371327291 20332722534602189056990937)
          ·
            refine ⟨15249541900951641792743203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20332722534602189056990937 15249541900951641792743203)
            ·
              refine ⟨22874312851427462689114805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15249541900951641792743203 22874312851427462689114805)
              ·
                refine ⟨2144466829821324627104513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22874312851427462689114805 2144466829821324627104513)
                ·
                  refine ⟨1608350122365993470328385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2144466829821324627104513 1608350122365993470328385)
                  ·
                    refine ⟨1206262591774495102746289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1608350122365993470328385 1206262591774495102746289)
                    ·
                      refine ⟨904696943830871327059717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1206262591774495102746289 904696943830871327059717)
                      ·
                        rfl

theorem cell23_1761891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_1761891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761891 prefixEnd_1761891 := by exact prefixLift 1761891
  have htrace : WordTrace (prefixWord ++ tailWord_1761891) baseStart_1761891 baseEnd_1761891 := by
    simpa [prefixWord, tailWord_1761891, baseEnd_1761891] using wordTrace_append hprefix tailTrace_1761891
  have hstable : (prefixWord ++ tailWord_1761891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761891).length < 2 ^ (prefixWord ++ tailWord_1761891).sum := by decide
  have hdescent : baseEnd_1761891 < baseStart_1761891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761924 : List Nat := [2, 3, 2, 1, 3, 1, 1, 2, 2, 3, 3]
def baseStart_1761924 : Nat := 118140960795 + 1761924 * 2 ^ 59
def prefixEnd_1761924 : Nat := 4983230072969 + 3 ^ 40 * 1761924 * 2
def baseEnd_1761924 : Nat := 904713888692469697947065

theorem tailTrace_1761924 : CollatzResearch.WordTrace tailWord_1761924 prefixEnd_1761924 904713888692469697947065 := by
  unfold tailWord_1761924
  simp only [CollatzResearch.WordTrace]
  refine ⟨32131323834428867753714413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42841765112571823671619217 32131323834428867753714413)
  ·
    refine ⟨12049246437910825407642905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32131323834428867753714413 12049246437910825407642905)
    ·
      refine ⟨9036934828433119055732179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12049246437910825407642905 9036934828433119055732179)
      ·
        refine ⟨13555402242649678583598269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9036934828433119055732179 13555402242649678583598269)
        ·
          refine ⟨5083275840993629468849351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13555402242649678583598269 5083275840993629468849351)
          ·
            refine ⟨7624913761490444203274027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5083275840993629468849351 7624913761490444203274027)
            ·
              refine ⟨11437370642235666304911041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7624913761490444203274027 11437370642235666304911041)
              ·
                refine ⟨8578027981676749728683281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11437370642235666304911041 8578027981676749728683281)
                ·
                  refine ⟨6433520986257562296512461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8578027981676749728683281 6433520986257562296512461)
                  ·
                    refine ⟨2412570369846585861192173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6433520986257562296512461 2412570369846585861192173)
                    ·
                      refine ⟨904713888692469697947065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2412570369846585861192173 904713888692469697947065)
                      ·
                        rfl

theorem cell23_1761924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_1761924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761924 prefixEnd_1761924 := by exact prefixLift 1761924
  have htrace : WordTrace (prefixWord ++ tailWord_1761924) baseStart_1761924 baseEnd_1761924 := by
    simpa [prefixWord, tailWord_1761924, baseEnd_1761924] using wordTrace_append hprefix tailTrace_1761924
  have hstable : (prefixWord ++ tailWord_1761924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761924).length < 2 ^ (prefixWord ++ tailWord_1761924).sum := by decide
  have hdescent : baseEnd_1761924 < baseStart_1761924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761927 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 4, 5]
def baseStart_1761927 : Nat := 118140960795 + 1761927 * 2 ^ 59
def prefixEnd_1761927 : Nat := 4983230072969 + 3 ^ 40 * 1761927 * 2
def baseEnd_1761927 : Nat := 301571809711477728736517

theorem tailTrace_1761927 : CollatzResearch.WordTrace tailWord_1761927 prefixEnd_1761927 301571809711477728736517 := by
  unfold tailWord_1761927
  simp only [CollatzResearch.WordTrace]
  refine ⟨64262757087846867019788035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42841838058564578013192023 64262757087846867019788035)
  ·
    refine ⟨96394135631770300529682053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64262757087846867019788035 96394135631770300529682053)
    ·
      refine ⟨18073900430956931349315385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96394135631770300529682053 18073900430956931349315385)
      ·
        refine ⟨13555425323217698511986539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18073900430956931349315385 13555425323217698511986539)
        ·
          refine ⟨20333137984826547767979809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13555425323217698511986539 20333137984826547767979809)
          ·
            refine ⟨15249853488619910825984857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20333137984826547767979809 15249853488619910825984857)
            ·
              refine ⟨11437390116464933119488643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15249853488619910825984857 11437390116464933119488643)
              ·
                refine ⟨17156085174697399679232965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11437390116464933119488643 17156085174697399679232965)
                ·
                  refine ⟨3216765970255762439856181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17156085174697399679232965 3216765970255762439856181)
                  ·
                    refine ⟨301571809711477728736517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3216765970255762439856181 301571809711477728736517)
                    ·
                      rfl

theorem cell23_1761927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_1761927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761927 prefixEnd_1761927 := by exact prefixLift 1761927
  have htrace : WordTrace (prefixWord ++ tailWord_1761927) baseStart_1761927 baseEnd_1761927 := by
    simpa [prefixWord, tailWord_1761927, baseEnd_1761927] using wordTrace_append hprefix tailTrace_1761927
  have hstable : (prefixWord ++ tailWord_1761927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761927).length < 2 ^ (prefixWord ++ tailWord_1761927).sum := by decide
  have hdescent : baseEnd_1761927 < baseStart_1761927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761984 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 3]
def baseStart_1761984 : Nat := 118140960795 + 1761984 * 2 ^ 59
def prefixEnd_1761984 : Nat := 4983230072969 + 3 ^ 40 * 1761984 * 2
def baseEnd_1761984 : Nat := 904744697531739463196789

theorem tailTrace_1761984 : CollatzResearch.WordTrace tailWord_1761984 prefixEnd_1761984 904744697531739463196789 := by
  unfold tailWord_1761984
  simp only [CollatzResearch.WordTrace]
  refine ⟨32132418024320182877306503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42843224032426910503075337 32132418024320182877306503)
  ·
    refine ⟨48198627036480274315959755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32132418024320182877306503 48198627036480274315959755)
    ·
      refine ⟨72297940554720411473939633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48198627036480274315959755 72297940554720411473939633)
      ·
        refine ⟨54223455416040308605454725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72297940554720411473939633 54223455416040308605454725)
        ·
          refine ⟨10166897890507557863522761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54223455416040308605454725 10166897890507557863522761)
          ·
            refine ⟨7625173417880668397642071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10166897890507557863522761 7625173417880668397642071)
            ·
              refine ⟨11437760126821002596463107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7625173417880668397642071 11437760126821002596463107)
              ·
                refine ⟨17156640190231503894694661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11437760126821002596463107 17156640190231503894694661)
                ·
                  refine ⟨3216870035668406980255249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17156640190231503894694661 3216870035668406980255249)
                  ·
                    refine ⟨2412652526751305235191437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3216870035668406980255249 2412652526751305235191437)
                    ·
                      refine ⟨904744697531739463196789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2412652526751305235191437 904744697531739463196789)
                      ·
                        rfl

theorem cell23_1761984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 3].length) (baseStart_1761984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1761984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1761984 prefixEnd_1761984 := by exact prefixLift 1761984
  have htrace : WordTrace (prefixWord ++ tailWord_1761984) baseStart_1761984 baseEnd_1761984 := by
    simpa [prefixWord, tailWord_1761984, baseEnd_1761984] using wordTrace_append hprefix tailTrace_1761984
  have hstable : (prefixWord ++ tailWord_1761984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761984).length < 2 ^ (prefixWord ++ tailWord_1761984).sum := by decide
  have hdescent : baseEnd_1761984 < baseStart_1761984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762047 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 5, 6]
def baseStart_1762047 : Nat := 118140960795 + 1762047 * 2 ^ 59
def prefixEnd_1762047 : Nat := 4983230072969 + 3 ^ 40 * 1762047 * 2
def baseEnd_1762047 : Nat := 301592348937657572236333

theorem tailTrace_1762047 : CollatzResearch.WordTrace tailWord_1762047 prefixEnd_1762047 301592348937657572236333 := by
  unfold tailWord_1762047
  simp only [CollatzResearch.WordTrace]
  refine ⟨64267133847412127514156395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42844755898274751676104263 64267133847412127514156395)
  ·
    refine ⟨96400700771118191271234593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64267133847412127514156395 96400700771118191271234593)
    ·
      refine ⟨72300525578338643453425945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96400700771118191271234593 72300525578338643453425945)
      ·
        refine ⟨54225394183753982590069459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72300525578338643453425945 54225394183753982590069459)
        ·
          refine ⟨81338091275630973885104189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54225394183753982590069459 81338091275630973885104189)
          ·
            refine ⟨30501784228361615206914071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81338091275630973885104189 30501784228361615206914071)
            ·
              refine ⟨45752676342542422810371107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30501784228361615206914071 45752676342542422810371107)
              ·
                refine ⟨68629014513813634215556661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45752676342542422810371107 68629014513813634215556661)
                ·
                  refine ⟨6433970110670028207708437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68629014513813634215556661 6433970110670028207708437)
                  ·
                    refine ⟨301592348937657572236333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6433970110670028207708437 301592348937657572236333)
                    ·
                      rfl

theorem cell23_1762047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 6].length) (baseStart_1762047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762047 prefixEnd_1762047 := by exact prefixLift 1762047
  have htrace : WordTrace (prefixWord ++ tailWord_1762047) baseStart_1762047 baseEnd_1762047 := by
    simpa [prefixWord, tailWord_1762047, baseEnd_1762047] using wordTrace_append hprefix tailTrace_1762047
  have hstable : (prefixWord ++ tailWord_1762047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762047).length < 2 ^ (prefixWord ++ tailWord_1762047).sum := by decide
  have hdescent : baseEnd_1762047 < baseStart_1762047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762088 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 5, 2, 2]
def baseStart_1762088 : Nat := 118140960795 + 1762088 * 2 ^ 59
def prefixEnd_1762088 : Nat := 4983230072969 + 3 ^ 40 * 1762088 * 2
def baseEnd_1762088 : Nat := 904798099519807056296311

theorem tailTrace_1762088 : CollatzResearch.WordTrace tailWord_1762088 prefixEnd_1762088 904798099519807056296311 := by
  unfold tailWord_1762088
  simp only [CollatzResearch.WordTrace]
  refine ⟨32134314620131795758199459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42845752826842394344265945 32134314620131795758199459)
  ·
    refine ⟨48201471930197693637299189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32134314620131795758199459 48201471930197693637299189)
    ·
      refine ⟨4518887993456033778496799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48201471930197693637299189 4518887993456033778496799)
      ·
        refine ⟨6778331990184050667745199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4518887993456033778496799 6778331990184050667745199)
        ·
          refine ⟨10167497985276076001617799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6778331990184050667745199 10167497985276076001617799)
          ·
            refine ⟨15251246977914114002426699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10167497985276076001617799 15251246977914114002426699)
            ·
              refine ⟨22876870466871171003640049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15251246977914114002426699 22876870466871171003640049)
              ·
                refine ⟨17157652850153378252730037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22876870466871171003640049 17157652850153378252730037)
                ·
                  refine ⟨1608529954701879211193441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17157652850153378252730037 1608529954701879211193441)
                  ·
                    refine ⟨1206397466026409408395081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1608529954701879211193441 1206397466026409408395081)
                    ·
                      refine ⟨904798099519807056296311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1206397466026409408395081 904798099519807056296311)
                      ·
                        rfl

theorem cell23_1762088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_1762088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762088 prefixEnd_1762088 := by exact prefixLift 1762088
  have htrace : WordTrace (prefixWord ++ tailWord_1762088) baseStart_1762088 baseEnd_1762088 := by
    simpa [prefixWord, tailWord_1762088, baseEnd_1762088] using wordTrace_append hprefix tailTrace_1762088
  have hstable : (prefixWord ++ tailWord_1762088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762088).length < 2 ^ (prefixWord ++ tailWord_1762088).sum := by decide
  have hdescent : baseEnd_1762088 < baseStart_1762088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762121 : List Nat := [1, 2, 1, 1, 2, 5, 3, 1, 1, 3, 3]
def baseStart_1762121 : Nat := 118140960795 + 1762121 * 2 ^ 59
def prefixEnd_1762121 : Nat := 4983230072969 + 3 ^ 40 * 1762121 * 2
def baseEnd_1762121 : Nat := 904815044381405427183659

theorem tailTrace_1762121 : CollatzResearch.WordTrace tailWord_1762121 prefixEnd_1762121 904815044381405427183659 := by
  unfold tailWord_1762121
  simp only [CollatzResearch.WordTrace]
  refine ⟨64269832849144038152350217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42846555232762692101566811 64269832849144038152350217)
  ·
    refine ⟨48202374636858028614262663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64269832849144038152350217 48202374636858028614262663)
    ·
      refine ⟨72303561955287042921393995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48202374636858028614262663 72303561955287042921393995)
      ·
        refine ⟨108455342932930564382090993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72303561955287042921393995 108455342932930564382090993)
        ·
          refine ⟨81341507199697923286568245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108455342932930564382090993 81341507199697923286568245)
          ·
            refine ⟨7625766299971680308115773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81341507199697923286568245 7625766299971680308115773)
            ·
              refine ⟨2859662362489380115543415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7625766299971680308115773 2859662362489380115543415)
              ·
                refine ⟨4289493543734070173315123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2859662362489380115543415 4289493543734070173315123)
                ·
                  refine ⟨6434240315601105259972685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4289493543734070173315123 6434240315601105259972685)
                  ·
                    refine ⟨2412840118350414472489757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6434240315601105259972685 2412840118350414472489757)
                    ·
                      refine ⟨904815044381405427183659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2412840118350414472489757 904815044381405427183659)
                      ·
                        rfl

theorem cell23_1762121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 3, 3].length) (baseStart_1762121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762121 prefixEnd_1762121 := by exact prefixLift 1762121
  have htrace : WordTrace (prefixWord ++ tailWord_1762121) baseStart_1762121 baseEnd_1762121 := by
    simpa [prefixWord, tailWord_1762121, baseEnd_1762121] using wordTrace_append hprefix tailTrace_1762121
  have hstable : (prefixWord ++ tailWord_1762121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762121).length < 2 ^ (prefixWord ++ tailWord_1762121).sum := by decide
  have hdescent : baseEnd_1762121 < baseStart_1762121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762131 : List Nat := [1, 1, 1, 2, 1, 1, 3, 5, 3, 3, 2]
def baseStart_1762131 : Nat := 118140960795 + 1762131 * 2 ^ 59
def prefixEnd_1762131 : Nat := 4983230072969 + 3 ^ 40 * 1762131 * 2
def baseEnd_1762131 : Nat := 904820179187950388058613

theorem tailTrace_1762131 : CollatzResearch.WordTrace tailWord_1762131 prefixEnd_1762131 904820179187950388058613 := by
  unfold tailWord_1762131
  simp only [CollatzResearch.WordTrace]
  refine ⟨64270197579107809860214247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42846798386071873240142831 64270197579107809860214247)
  ·
    refine ⟨96405296368661714790321371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64270197579107809860214247 96405296368661714790321371)
    ·
      refine ⟨144607944552992572185482057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96405296368661714790321371 144607944552992572185482057)
      ·
        refine ⟨108455958414744429139111543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144607944552992572185482057 108455958414744429139111543)
        ·
          refine ⟨162683937622116643708667315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108455958414744429139111543 162683937622116643708667315)
          ·
            refine ⟨244025906433174965563000973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162683937622116643708667315 244025906433174965563000973)
            ·
              refine ⟨91509714912440612086125365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244025906433174965563000973 91509714912440612086125365)
              ·
                refine ⟨8579035773041307383074253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91509714912440612086125365 8579035773041307383074253)
                ·
                  refine ⟨3217138414890490268652845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8579035773041307383074253 3217138414890490268652845)
                  ·
                    refine ⟨1206426905583933850744817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3217138414890490268652845 1206426905583933850744817)
                    ·
                      refine ⟨904820179187950388058613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1206426905583933850744817 904820179187950388058613)
                      ·
                        rfl

theorem cell23_1762131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 3, 2].length) (baseStart_1762131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762131 prefixEnd_1762131 := by exact prefixLift 1762131
  have htrace : WordTrace (prefixWord ++ tailWord_1762131) baseStart_1762131 baseEnd_1762131 := by
    simpa [prefixWord, tailWord_1762131, baseEnd_1762131] using wordTrace_append hprefix tailTrace_1762131
  have hstable : (prefixWord ++ tailWord_1762131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762131).length < 2 ^ (prefixWord ++ tailWord_1762131).sum := by decide
  have hdescent : baseEnd_1762131 < baseStart_1762131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762201 : List Nat := [1, 2, 1, 2, 1, 3, 1, 7, 5]
def baseStart_1762201 : Nat := 118140960795 + 1762201 * 2 ^ 59
def prefixEnd_1762201 : Nat := 4983230072969 + 3 ^ 40 * 1762201 * 2
def baseEnd_1762201 : Nat := 100539569203751679353699

theorem tailTrace_1762201 : CollatzResearch.WordTrace tailWord_1762201 prefixEnd_1762201 100539569203751679353699 := by
  unfold tailWord_1762201
  simp only [CollatzResearch.WordTrace]
  refine ⟨64272750688854211815262457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42848500459236141210174971 64272750688854211815262457)
  ·
    refine ⟨48204563016640658861446843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64272750688854211815262457 48204563016640658861446843)
    ·
      refine ⟨72306844524960988292170265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48204563016640658861446843 72306844524960988292170265)
      ·
        refine ⟨54230133393720741219127699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72306844524960988292170265 54230133393720741219127699)
        ·
          refine ⟨81345200090581111828691549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54230133393720741219127699 81345200090581111828691549)
          ·
            refine ⟨30504450033967916935759331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81345200090581111828691549 30504450033967916935759331)
            ·
              refine ⟨45756675050951875403638997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30504450033967916935759331 45756675050951875403638997)
              ·
                refine ⟨1072422071506684579772789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 45756675050951875403638997 1072422071506684579772789)
                ·
                  refine ⟨100539569203751679353699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1072422071506684579772789 100539569203751679353699)
                  ·
                    rfl

theorem cell23_1762201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7, 5].length) (baseStart_1762201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762201 prefixEnd_1762201 := by exact prefixLift 1762201
  have htrace : WordTrace (prefixWord ++ tailWord_1762201) baseStart_1762201 baseEnd_1762201 := by
    simpa [prefixWord, tailWord_1762201, baseEnd_1762201] using wordTrace_append hprefix tailTrace_1762201
  have hstable : (prefixWord ++ tailWord_1762201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762201).length < 2 ^ (prefixWord ++ tailWord_1762201).sum := by decide
  have hdescent : baseEnd_1762201 < baseStart_1762201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762238 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2]
def baseStart_1762238 : Nat := 118140960795 + 1762238 * 2 ^ 59
def prefixEnd_1762238 : Nat := 4983230072969 + 3 ^ 40 * 1762238 * 2
def baseEnd_1762238 : Nat := 904875121617981469420621

theorem tailTrace_1762238 : CollatzResearch.WordTrace tailWord_1762238 prefixEnd_1762238 904875121617981469420621 := by
  unfold tailWord_1762238
  simp only [CollatzResearch.WordTrace]
  refine ⟨8034262523715020891794921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42849400126480111422906245 8034262523715020891794921)
  ·
    refine ⟨6025696892786265668846191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8034262523715020891794921 6025696892786265668846191)
    ·
      refine ⟨9038545339179398503269287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6025696892786265668846191 9038545339179398503269287)
      ·
        refine ⟨13557818008769097754903931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9038545339179398503269287 13557818008769097754903931)
        ·
          refine ⟨20336727013153646632355897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13557818008769097754903931 20336727013153646632355897)
          ·
            refine ⟨15252545259865234974266923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20336727013153646632355897 15252545259865234974266923)
            ·
              refine ⟨22878817889797852461400385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15252545259865234974266923 22878817889797852461400385)
              ·
                refine ⟨17159113417348389346050289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22878817889797852461400385 17159113417348389346050289)
                ·
                  refine ⟨12869335063011292009537717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17159113417348389346050289 12869335063011292009537717)
                  ·
                    refine ⟨1206500162157308625894161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12869335063011292009537717 1206500162157308625894161)
                    ·
                      refine ⟨904875121617981469420621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1206500162157308625894161 904875121617981469420621)
                      ·
                        rfl

theorem cell23_1762238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_1762238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762238 prefixEnd_1762238 := by exact prefixLift 1762238
  have htrace : WordTrace (prefixWord ++ tailWord_1762238) baseStart_1762238 baseEnd_1762238 := by
    simpa [prefixWord, tailWord_1762238, baseEnd_1762238] using wordTrace_append hprefix tailTrace_1762238
  have hstable : (prefixWord ++ tailWord_1762238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762238).length < 2 ^ (prefixWord ++ tailWord_1762238).sum := by decide
  have hdescent : baseEnd_1762238 < baseStart_1762238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762251 : List Nat := [1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 4]
def baseStart_1762251 : Nat := 118140960795 + 1762251 * 2 ^ 59
def prefixEnd_1762251 : Nat := 4983230072969 + 3 ^ 40 * 1762251 * 2
def baseEnd_1762251 : Nat := 904881796866489918558061

theorem tailTrace_1762251 : CollatzResearch.WordTrace tailWord_1762251 prefixEnd_1762251 904881796866489918558061 := by
  unfold tailWord_1762251
  simp only [CollatzResearch.WordTrace]
  refine ⟨64274574338673070354582607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42849716225782046903055071 64274574338673070354582607)
  ·
    refine ⟨96411861508009605531873911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64274574338673070354582607 96411861508009605531873911)
    ·
      refine ⟨144617792262014408297810867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96411861508009605531873911 144617792262014408297810867)
      ·
        refine ⟨216926688393021612446716301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144617792262014408297810867 216926688393021612446716301)
        ·
          refine ⟨81347508147383104667518613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216926688393021612446716301 81347508147383104667518613)
          ·
            refine ⟨3813164444408583031289935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81347508147383104667518613 3813164444408583031289935)
            ·
              refine ⟨5719746666612874546934903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3813164444408583031289935 5719746666612874546934903)
              ·
                refine ⟨8579619999919311820402355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5719746666612874546934903 8579619999919311820402355)
                ·
                  refine ⟨12869429999878967730603533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8579619999919311820402355 12869429999878967730603533)
                  ·
                    refine ⟨4826036249954612898976325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12869429999878967730603533 4826036249954612898976325)
                    ·
                      refine ⟨904881796866489918558061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4826036249954612898976325 904881796866489918558061)
                      ·
                        rfl

theorem cell23_1762251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 4].length) (baseStart_1762251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762251 prefixEnd_1762251 := by exact prefixLift 1762251
  have htrace : WordTrace (prefixWord ++ tailWord_1762251) baseStart_1762251 baseEnd_1762251 := by
    simpa [prefixWord, tailWord_1762251, baseEnd_1762251] using wordTrace_append hprefix tailTrace_1762251
  have hstable : (prefixWord ++ tailWord_1762251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762251).length < 2 ^ (prefixWord ++ tailWord_1762251).sum := by decide
  have hdescent : baseEnd_1762251 < baseStart_1762251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762301 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 1, 7, 3]
def baseStart_1762301 : Nat := 118140960795 + 1762301 * 2 ^ 59
def prefixEnd_1762301 : Nat := 4983230072969 + 3 ^ 40 * 1762301 * 2
def baseEnd_1762301 : Nat := 904907470899214722932831

theorem tailTrace_1762301 : CollatzResearch.WordTrace tailWord_1762301 prefixEnd_1762301 904907470899214722932831 := by
  unfold tailWord_1762301
  simp only [CollatzResearch.WordTrace]
  refine ⟨64276397988491928893902757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42850931992327952595935171 64276397988491928893902757)
  ·
    refine ⟨12051824622842236667606767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64276397988491928893902757 12051824622842236667606767)
    ·
      refine ⟨18077736934263355001410151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12051824622842236667606767 18077736934263355001410151)
      ·
        refine ⟨27116605401395032502115227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18077736934263355001410151 27116605401395032502115227)
        ·
          refine ⟨40674908102092548753172841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27116605401395032502115227 40674908102092548753172841)
          ·
            refine ⟨30506181076569411564879631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40674908102092548753172841 30506181076569411564879631)
            ·
              refine ⟨45759271614854117347319447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30506181076569411564879631 45759271614854117347319447)
              ·
                refine ⟨68638907422281176020979171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45759271614854117347319447 68638907422281176020979171)
                ·
                  refine ⟨102958361133421764031468757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68638907422281176020979171 102958361133421764031468757)
                  ·
                    refine ⟨2413086589064572594487549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 102958361133421764031468757 2413086589064572594487549)
                    ·
                      refine ⟨904907470899214722932831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2413086589064572594487549 904907470899214722932831)
                      ·
                        rfl

theorem cell23_1762301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_1762301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762301 prefixEnd_1762301 := by exact prefixLift 1762301
  have htrace : WordTrace (prefixWord ++ tailWord_1762301) baseStart_1762301 baseEnd_1762301 := by
    simpa [prefixWord, tailWord_1762301, baseEnd_1762301] using wordTrace_append hprefix tailTrace_1762301
  have hstable : (prefixWord ++ tailWord_1762301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762301).length < 2 ^ (prefixWord ++ tailWord_1762301).sum := by decide
  have hdescent : baseEnd_1762301 < baseStart_1762301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762312 : List Nat := [2, 1, 3, 2, 1, 5, 1, 3, 1, 4]
def baseStart_1762312 : Nat := 118140960795 + 1762312 * 2 ^ 59
def prefixEnd_1762312 : Nat := 4983230072969 + 3 ^ 40 * 1762312 * 2
def baseEnd_1762312 : Nat := 301637706395471393298427

theorem tailTrace_1762312 : CollatzResearch.WordTrace tailWord_1762312 prefixEnd_1762312 301637706395471393298427 := by
  unfold tailWord_1762312
  simp only [CollatzResearch.WordTrace]
  refine ⟨32138399595726038886276595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42851199460968051848368793 32138399595726038886276595)
  ·
    refine ⟨48207599393589058329414893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32138399595726038886276595 48207599393589058329414893)
    ·
      refine ⟨18077849772595896873530585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48207599393589058329414893 18077849772595896873530585)
      ·
        refine ⟨13558387329446922655147939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18077849772595896873530585 13558387329446922655147939)
        ·
          refine ⟨20337580994170383982721909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13558387329446922655147939 20337580994170383982721909)
          ·
            refine ⟨1906648218203473498380179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20337580994170383982721909 1906648218203473498380179)
            ·
              refine ⟨2859972327305210247570269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1906648218203473498380179 2859972327305210247570269)
              ·
                refine ⟨1072489622739453842838851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2859972327305210247570269 1072489622739453842838851)
                ·
                  refine ⟨1608734434109180764258277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1072489622739453842838851 1608734434109180764258277)
                  ·
                    refine ⟨301637706395471393298427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1608734434109180764258277 301637706395471393298427)
                    ·
                      rfl

theorem cell23_1762312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_1762312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762312 prefixEnd_1762312 := by exact prefixLift 1762312
  have htrace : WordTrace (prefixWord ++ tailWord_1762312) baseStart_1762312 baseEnd_1762312 := by
    simpa [prefixWord, tailWord_1762312, baseEnd_1762312] using wordTrace_append hprefix tailTrace_1762312
  have hstable : (prefixWord ++ tailWord_1762312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762312).length < 2 ^ (prefixWord ++ tailWord_1762312).sum := by decide
  have hdescent : baseEnd_1762312 < baseStart_1762312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762335 : List Nat := [1, 1, 2, 4, 1, 3, 3, 1, 3, 1, 3]
def baseStart_1762335 : Nat := 118140960795 + 1762335 * 2 ^ 59
def prefixEnd_1762335 : Nat := 4983230072969 + 3 ^ 40 * 1762335 * 2
def baseEnd_1762335 : Nat := 904924929241467589907675

theorem tailTrace_1762335 : CollatzResearch.WordTrace tailWord_1762335 prefixEnd_1762335 904924929241467589907675 := by
  unfold tailWord_1762335
  simp only [CollatzResearch.WordTrace]
  refine ⟨64277638070368752700640459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42851758713579168467093639 64277638070368752700640459)
  ·
    refine ⟨96416457105553129050960689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64277638070368752700640459 96416457105553129050960689)
    ·
      refine ⟨72312342829164846788220517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96416457105553129050960689 72312342829164846788220517)
      ·
        refine ⟨13558564280468408772791347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72312342829164846788220517 13558564280468408772791347)
        ·
          refine ⟨20337846420702613159187021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13558564280468408772791347 20337846420702613159187021)
          ·
            refine ⟨7626692407763479934695133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20337846420702613159187021 7626692407763479934695133)
            ·
              refine ⟨2860009652911304975510675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7626692407763479934695133 2860009652911304975510675)
              ·
                refine ⟨4290014479366957463266013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2860009652911304975510675 4290014479366957463266013)
                ·
                  refine ⟨1608755429762609048724755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4290014479366957463266013 1608755429762609048724755)
                  ·
                    refine ⟨2413133144643913573087133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1608755429762609048724755 2413133144643913573087133)
                    ·
                      refine ⟨904924929241467589907675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2413133144643913573087133 904924929241467589907675)
                      ·
                        rfl

theorem cell23_1762335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_1762335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762335 prefixEnd_1762335 := by exact prefixLift 1762335
  have htrace : WordTrace (prefixWord ++ tailWord_1762335) baseStart_1762335 baseEnd_1762335 := by
    simpa [prefixWord, tailWord_1762335, baseEnd_1762335] using wordTrace_append hprefix tailTrace_1762335
  have hstable : (prefixWord ++ tailWord_1762335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762335).length < 2 ^ (prefixWord ++ tailWord_1762335).sum := by decide
  have hdescent : baseEnd_1762335 < baseStart_1762335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762378 : List Nat := [3, 1, 2, 1, 1, 2, 5, 1, 1, 1, 5]
def baseStart_1762378 : Nat := 118140960795 + 1762378 * 2 ^ 59
def prefixEnd_1762378 : Nat := 4983230072969 + 3 ^ 40 * 1762378 * 2
def baseEnd_1762378 : Nat := 904947008909610921669977

theorem tailTrace_1762378 : CollatzResearch.WordTrace tailWord_1762378 prefixEnd_1762378 904947008909610921669977 := by
  unfold tailWord_1762378
  simp only [CollatzResearch.WordTrace]
  refine ⟨16069801602303242761113947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42852804272808647362970525 16069801602303242761113947)
  ·
    refine ⟨24104702403454864141670921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16069801602303242761113947 24104702403454864141670921)
    ·
      refine ⟨18078526802591148106253191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24104702403454864141670921 18078526802591148106253191)
      ·
        refine ⟨27117790203886722159379787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18078526802591148106253191 27117790203886722159379787)
        ·
          refine ⟨40676685305830083239069681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27117790203886722159379787 40676685305830083239069681)
          ·
            refine ⟨30507513979372562429302261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40676685305830083239069681 30507513979372562429302261)
            ·
              refine ⟨2860079435566177727747087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30507513979372562429302261 2860079435566177727747087)
              ·
                refine ⟨4290119153349266591620631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2860079435566177727747087 4290119153349266591620631)
                ·
                  refine ⟨6435178730023899887430947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4290119153349266591620631 6435178730023899887430947)
                  ·
                    refine ⟨9652768095035849831146421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6435178730023899887430947 9652768095035849831146421)
                    ·
                      refine ⟨904947008909610921669977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9652768095035849831146421 904947008909610921669977)
                      ·
                        rfl

theorem cell23_1762378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_1762378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762378 prefixEnd_1762378 := by exact prefixLift 1762378
  have htrace : WordTrace (prefixWord ++ tailWord_1762378) baseStart_1762378 baseEnd_1762378 := by
    simpa [prefixWord, tailWord_1762378, baseEnd_1762378] using wordTrace_append hprefix tailTrace_1762378
  have hstable : (prefixWord ++ tailWord_1762378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762378).length < 2 ^ (prefixWord ++ tailWord_1762378).sum := by decide
  have hdescent : baseEnd_1762378 < baseStart_1762378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762386 : List Nat := [3, 2, 2, 1, 3, 3, 2, 2, 1, 1, 3]
def baseStart_1762386 : Nat := 118140960795 + 1762386 * 2 ^ 59
def prefixEnd_1762386 : Nat := 4983230072969 + 3 ^ 40 * 1762386 * 2
def baseEnd_1762386 : Nat := 904951116754846890369941

theorem tailTrace_1762386 : CollatzResearch.WordTrace tailWord_1762386 prefixEnd_1762386 904951116754846890369941 := by
  unfold tailWord_1762386
  simp only [CollatzResearch.WordTrace]
  refine ⟨16069874548295997102686753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42852998795455992273831341 16069874548295997102686753)
  ·
    refine ⟨12052405911221997827015065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16069874548295997102686753 12052405911221997827015065)
    ·
      refine ⟨9039304433416498370261299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12052405911221997827015065 9039304433416498370261299)
      ·
        refine ⟨13558956650124747555391949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9039304433416498370261299 13558956650124747555391949)
        ·
          refine ⟨5084608743796780333271981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13558956650124747555391949 5084608743796780333271981)
          ·
            refine ⟨1906728278923792624976993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5084608743796780333271981 1906728278923792624976993)
            ·
              refine ⟨1430046209192844468732745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1906728278923792624976993 1430046209192844468732745)
              ·
                refine ⟨1072534656894633351549559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1430046209192844468732745 1072534656894633351549559)
                ·
                  refine ⟨1608801985341950027324339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1072534656894633351549559 1608801985341950027324339)
                  ·
                    refine ⟨2413202978012925040986509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1608801985341950027324339 2413202978012925040986509)
                    ·
                      refine ⟨904951116754846890369941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2413202978012925040986509 904951116754846890369941)
                      ·
                        rfl

theorem cell23_1762386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_1762386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762386 prefixEnd_1762386 := by exact prefixLift 1762386
  have htrace : WordTrace (prefixWord ++ tailWord_1762386) baseStart_1762386 baseEnd_1762386 := by
    simpa [prefixWord, tailWord_1762386, baseEnd_1762386] using wordTrace_append hprefix tailTrace_1762386
  have hstable : (prefixWord ++ tailWord_1762386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762386).length < 2 ^ (prefixWord ++ tailWord_1762386).sum := by decide
  have hdescent : baseEnd_1762386 < baseStart_1762386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762401 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 2, 2, 6]
def baseStart_1762401 : Nat := 118140960795 + 1762401 * 2 ^ 59
def prefixEnd_1762401 : Nat := 4983230072969 + 3 ^ 40 * 1762401 * 2
def baseEnd_1762401 : Nat := 904958818964664331682371

theorem tailTrace_1762401 : CollatzResearch.WordTrace tailWord_1762401 prefixEnd_1762401 904958818964664331682371 := by
  unfold tailWord_1762401
  simp only [CollatzResearch.WordTrace]
  refine ⟨64280045288129645972543057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42853363525419763981695371 64280045288129645972543057)
  ·
    refine ⟨48210033966097234479407293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64280045288129645972543057 48210033966097234479407293)
    ·
      refine ⟨18078762737286462929777735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48210033966097234479407293 18078762737286462929777735)
      ·
        refine ⟨27118144105929694394666603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18078762737286462929777735 27118144105929694394666603)
        ·
          refine ⟨40677216158894541591999905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27118144105929694394666603 40677216158894541591999905)
          ·
            refine ⟨30507912119170906193999929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40677216158894541591999905 30507912119170906193999929)
            ·
              refine ⟨22880934089378179645499947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30507912119170906193999929 22880934089378179645499947)
              ·
                refine ⟨34321401134067269468249921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22880934089378179645499947 34321401134067269468249921)
                ·
                  refine ⟨25741050850550452101187441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34321401134067269468249921 25741050850550452101187441)
                  ·
                    refine ⟨19305788137912839075890581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25741050850550452101187441 19305788137912839075890581)
                    ·
                      refine ⟨904958818964664331682371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19305788137912839075890581 904958818964664331682371)
                      ·
                        rfl

theorem cell23_1762401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_1762401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762401 prefixEnd_1762401 := by exact prefixLift 1762401
  have htrace : WordTrace (prefixWord ++ tailWord_1762401) baseStart_1762401 baseEnd_1762401 := by
    simpa [prefixWord, tailWord_1762401, baseEnd_1762401] using wordTrace_append hprefix tailTrace_1762401
  have hstable : (prefixWord ++ tailWord_1762401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762401).length < 2 ^ (prefixWord ++ tailWord_1762401).sum := by decide
  have hdescent : baseEnd_1762401 < baseStart_1762401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762402 : List Nat := [3, 3, 2, 2, 1, 1, 2, 3, 2, 4]
def baseStart_1762402 : Nat := 118140960795 + 1762402 * 2 ^ 59
def prefixEnd_1762402 : Nat := 4983230072969 + 3 ^ 40 * 1762402 * 2
def baseEnd_1762402 : Nat := 301653110815106275923289

theorem tailTrace_1762402 : CollatzResearch.WordTrace tailWord_1762402 prefixEnd_1762402 301653110815106275923289 := by
  unfold tailWord_1762402
  simp only [CollatzResearch.WordTrace]
  refine ⟨16070020440281505785832365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42853387840750682095552973 16070020440281505785832365)
  ·
    refine ⟨6026257665105564669687137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16070020440281505785832365 6026257665105564669687137)
    ·
      refine ⟨4519693248829173502265353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6026257665105564669687137 4519693248829173502265353)
      ·
        refine ⟨3389769936621880126699015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4519693248829173502265353 3389769936621880126699015)
        ·
          refine ⟨5084654904932820190048523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3389769936621880126699015 5084654904932820190048523)
          ·
            refine ⟨7626982357399230285072785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5084654904932820190048523 7626982357399230285072785)
            ·
              refine ⟨5720236768049422713804589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7626982357399230285072785 5720236768049422713804589)
              ·
                refine ⟨2145088788018533517676721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5720236768049422713804589 2145088788018533517676721)
                ·
                  refine ⟨1608816591013900138257541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2145088788018533517676721 1608816591013900138257541)
                  ·
                    refine ⟨301653110815106275923289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1608816591013900138257541 301653110815106275923289)
                    ·
                      rfl

theorem cell23_1762402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_1762402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762402 prefixEnd_1762402 := by exact prefixLift 1762402
  have htrace : WordTrace (prefixWord ++ tailWord_1762402) baseStart_1762402 baseEnd_1762402 := by
    simpa [prefixWord, tailWord_1762402, baseEnd_1762402] using wordTrace_append hprefix tailTrace_1762402
  have hstable : (prefixWord ++ tailWord_1762402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762402).length < 2 ^ (prefixWord ++ tailWord_1762402).sum := by decide
  have hdescent : baseEnd_1762402 < baseStart_1762402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762482 : List Nat := [3, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2]
def baseStart_1762482 : Nat := 118140960795 + 1762482 * 2 ^ 59
def prefixEnd_1762482 : Nat := 4983230072969 + 3 ^ 40 * 1762482 * 2
def baseEnd_1762482 : Nat := 905000410897678514769499

theorem tailTrace_1762482 : CollatzResearch.WordTrace tailWord_1762482 prefixEnd_1762482 905000410897678514769499 := by
  unfold tailWord_1762482
  simp only [CollatzResearch.WordTrace]
  refine ⟨16070749900209049201560425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42855333067224131204161133 16070749900209049201560425)
  ·
    refine ⟨12053062425156786901170319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16070749900209049201560425 12053062425156786901170319)
    ·
      refine ⟨18079593637735180351755479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12053062425156786901170319 18079593637735180351755479)
      ·
        refine ⟨27119390456602770527633219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18079593637735180351755479 27119390456602770527633219)
        ·
          refine ⟨40679085684904155791449829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27119390456602770527633219 40679085684904155791449829)
          ·
            refine ⟨7627328565919529210896843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40679085684904155791449829 7627328565919529210896843)
            ·
              refine ⟨11440992848879293816345265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7627328565919529210896843 11440992848879293816345265)
              ·
                refine ⟨8580744636659470362258949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11440992848879293816345265 8580744636659470362258949)
                ·
                  refine ⟨1608889619373650692923553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8580744636659470362258949 1608889619373650692923553)
                  ·
                    refine ⟨1206667214530238019692665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1608889619373650692923553 1206667214530238019692665)
                    ·
                      refine ⟨905000410897678514769499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1206667214530238019692665 905000410897678514769499)
                      ·
                        rfl

theorem cell23_1762482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2].length) (baseStart_1762482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762482 prefixEnd_1762482 := by exact prefixLift 1762482
  have htrace : WordTrace (prefixWord ++ tailWord_1762482) baseStart_1762482 baseEnd_1762482 := by
    simpa [prefixWord, tailWord_1762482, baseEnd_1762482] using wordTrace_append hprefix tailTrace_1762482
  have hstable : (prefixWord ++ tailWord_1762482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762482).length < 2 ^ (prefixWord ++ tailWord_1762482).sum := by decide
  have hdescent : baseEnd_1762482 < baseStart_1762482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762556 : List Nat := [2, 2, 2, 1, 6, 1, 2, 2, 5]
def baseStart_1762556 : Nat := 118140960795 + 1762556 * 2 ^ 59
def prefixEnd_1762556 : Nat := 4983230072969 + 3 ^ 40 * 1762556 * 2
def baseEnd_1762556 : Nat := 100559823162901247249351

theorem tailTrace_1762556 : CollatzResearch.WordTrace tailWord_1762556 prefixEnd_1762556 100559823162901247249351 := by
  unfold tailWord_1762556
  simp only [CollatzResearch.WordTrace]
  refine ⟨32142849301284053722217761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42857132401712071629623681 32142849301284053722217761)
  ·
    refine ⟨24107136975963040291663321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32142849301284053722217761 24107136975963040291663321)
    ·
      refine ⟨18080352731972280218747491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24107136975963040291663321 18080352731972280218747491)
      ·
        refine ⟨27120529097958420328121237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18080352731972280218747491 27120529097958420328121237)
        ·
          refine ⟨1271274801466800952880683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27120529097958420328121237 1271274801466800952880683)
          ·
            refine ⟨1906912202200201429321025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1271274801466800952880683 1906912202200201429321025)
            ·
              refine ⟨1430184151650151071990769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1906912202200201429321025 1430184151650151071990769)
              ·
                refine ⟨1072638113737613303993077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1430184151650151071990769 1072638113737613303993077)
                ·
                  refine ⟨100559823162901247249351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1072638113737613303993077 100559823162901247249351)
                  ·
                    rfl

theorem cell23_1762556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2, 5].length) (baseStart_1762556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762556 prefixEnd_1762556 := by exact prefixLift 1762556
  have htrace : WordTrace (prefixWord ++ tailWord_1762556) baseStart_1762556 baseEnd_1762556 := by
    simpa [prefixWord, tailWord_1762556, baseEnd_1762556] using wordTrace_append hprefix tailTrace_1762556
  have hstable : (prefixWord ++ tailWord_1762556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762556).length < 2 ^ (prefixWord ++ tailWord_1762556).sum := by decide
  have hdescent : baseEnd_1762556 < baseStart_1762556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762565 : List Nat := [1, 3, 1, 1, 2, 1, 4, 3, 3, 4]
def baseStart_1762565 : Nat := 118140960795 + 1762565 * 2 ^ 59
def prefixEnd_1762565 : Nat := 4983230072969 + 3 ^ 40 * 1762565 * 2
def baseEnd_1762565 : Nat := 301681009930667230010539

theorem tailTrace_1762565 : CollatzResearch.WordTrace tailWord_1762565 prefixEnd_1762565 301681009930667230010539 := by
  unfold tailWord_1762565
  simp only [CollatzResearch.WordTrace]
  refine ⟨64286026859535501981513149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42857351239690334654342099 64286026859535501981513149)
  ·
    refine ⟨24107260072325813243067431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64286026859535501981513149 24107260072325813243067431)
    ·
      refine ⟨36160890108488719864601147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24107260072325813243067431 36160890108488719864601147)
      ·
        refine ⟨54241335162733079796901721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36160890108488719864601147 54241335162733079796901721)
        ·
          refine ⟨40681001372049809847676291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54241335162733079796901721 40681001372049809847676291)
          ·
            refine ⟨61021502058074714771514437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40681001372049809847676291 61021502058074714771514437)
            ·
              refine ⟨11441531635889009019658957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61021502058074714771514437 11441531635889009019658957)
              ·
                refine ⟨4290574363458378382372109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11441531635889009019658957 4290574363458378382372109)
                ·
                  refine ⟨1608965386296891893389541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4290574363458378382372109 1608965386296891893389541)
                  ·
                    refine ⟨301681009930667230010539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1608965386296891893389541 301681009930667230010539)
                    ·
                      rfl

theorem cell23_1762565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3, 4].length) (baseStart_1762565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762565 prefixEnd_1762565 := by exact prefixLift 1762565
  have htrace : WordTrace (prefixWord ++ tailWord_1762565) baseStart_1762565 baseEnd_1762565 := by
    simpa [prefixWord, tailWord_1762565, baseEnd_1762565] using wordTrace_append hprefix tailTrace_1762565
  have hstable : (prefixWord ++ tailWord_1762565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762565).length < 2 ^ (prefixWord ++ tailWord_1762565).sum := by decide
  have hdescent : baseEnd_1762565 < baseStart_1762565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762572 : List Nat := [2, 2, 1, 2, 2, 4, 1, 1, 2, 4, 2]
def baseStart_1762572 : Nat := 118140960795 + 1762572 * 2 ^ 59
def prefixEnd_1762572 : Nat := 4983230072969 + 3 ^ 40 * 1762572 * 2
def baseEnd_1762572 : Nat := 905046624156583162644085

theorem tailTrace_1762572 : CollatzResearch.WordTrace tailWord_1762572 prefixEnd_1762572 905046624156583162644085 := by
  unfold tailWord_1762572
  simp only [CollatzResearch.WordTrace]
  refine ⟨32143141085255071088508985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42857521447006761451345313 32143141085255071088508985)
  ·
    refine ⟨24107355813941303316381739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32143141085255071088508985 24107355813941303316381739)
    ·
      refine ⟨36161033720911954974572609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24107355813941303316381739 36161033720911954974572609)
      ·
        refine ⟨27120775290683966230929457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36161033720911954974572609 27120775290683966230929457)
        ·
          refine ⟨20340581468012974673197093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27120775290683966230929457 20340581468012974673197093)
          ·
            refine ⟨3813859025252432751224455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20340581468012974673197093 3813859025252432751224455)
            ·
              refine ⟨5720788537878649126836683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3813859025252432751224455 5720788537878649126836683)
              ·
                refine ⟨8581182806817973690255025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5720788537878649126836683 8581182806817973690255025)
                ·
                  refine ⟨6435887105113480267691269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8581182806817973690255025 6435887105113480267691269)
                  ·
                    refine ⟨1206728832208777550192113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6435887105113480267691269 1206728832208777550192113)
                    ·
                      refine ⟨905046624156583162644085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1206728832208777550192113 905046624156583162644085)
                      ·
                        rfl

theorem cell23_1762572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 2, 4, 2].length) (baseStart_1762572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762572 prefixEnd_1762572 := by exact prefixLift 1762572
  have htrace : WordTrace (prefixWord ++ tailWord_1762572) baseStart_1762572 baseEnd_1762572 := by
    simpa [prefixWord, tailWord_1762572, baseEnd_1762572] using wordTrace_append hprefix tailTrace_1762572
  have hstable : (prefixWord ++ tailWord_1762572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762572).length < 2 ^ (prefixWord ++ tailWord_1762572).sum := by decide
  have hdescent : baseEnd_1762572 < baseStart_1762572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762589 : List Nat := [1, 4, 2, 3, 1, 3, 1, 1, 2, 1, 4]
def baseStart_1762589 : Nat := 118140960795 + 1762589 * 2 ^ 59
def prefixEnd_1762589 : Nat := 4983230072969 + 3 ^ 40 * 1762589 * 2
def baseEnd_1762589 : Nat := 905055353327709596131507

theorem tailTrace_1762589 : CollatzResearch.WordTrace tailWord_1762589 prefixEnd_1762589 905055353327709596131507 := by
  unfold tailWord_1762589
  simp only [CollatzResearch.WordTrace]
  refine ⟨64286902211448554080386821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42857934807632369386924547 64286902211448554080386821)
  ·
    refine ⟨12053794164646603890072529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64286902211448554080386821 12053794164646603890072529)
    ·
      refine ⟨9040345623484952917554397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12053794164646603890072529 9040345623484952917554397)
      ·
        refine ⟨3390129608806857344082899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9040345623484952917554397 3390129608806857344082899)
        ·
          refine ⟨5085194413210286016124349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3390129608806857344082899 5085194413210286016124349)
          ·
            refine ⟨1906947904953857256046631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5085194413210286016124349 1906947904953857256046631)
            ·
              refine ⟨2860421857430785884069947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1906947904953857256046631 2860421857430785884069947)
              ·
                refine ⟨4290632786146178826104921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2860421857430785884069947 4290632786146178826104921)
                ·
                  refine ⟨3217974589609634119578691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4290632786146178826104921 3217974589609634119578691)
                  ·
                    refine ⟨4826961884414451179368037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3217974589609634119578691 4826961884414451179368037)
                    ·
                      refine ⟨905055353327709596131507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4826961884414451179368037 905055353327709596131507)
                      ·
                        rfl

theorem cell23_1762589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_1762589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762589 prefixEnd_1762589 := by exact prefixLift 1762589
  have htrace : WordTrace (prefixWord ++ tailWord_1762589) baseStart_1762589 baseEnd_1762589 := by
    simpa [prefixWord, tailWord_1762589, baseEnd_1762589] using wordTrace_append hprefix tailTrace_1762589
  have hstable : (prefixWord ++ tailWord_1762589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762589).length < 2 ^ (prefixWord ++ tailWord_1762589).sum := by decide
  have hdescent : baseEnd_1762589 < baseStart_1762589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762592 : List Nat := [2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 3]
def baseStart_1762592 : Nat := 118140960795 + 1762592 * 2 ^ 59
def prefixEnd_1762592 : Nat := 4983230072969 + 3 ^ 40 * 1762592 * 2
def baseEnd_1762592 : Nat := 905056893769673084393993

theorem tailTrace_1762592 : CollatzResearch.WordTrace tailWord_1762592 prefixEnd_1762592 905056893769673084393993 := by
  unfold tailWord_1762592
  simp only [CollatzResearch.WordTrace]
  refine ⟨32143505815218842796373015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42858007753625123728497353 32143505815218842796373015)
  ·
    refine ⟨48215258722828264194559523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32143505815218842796373015 48215258722828264194559523)
    ·
      refine ⟨72322888084242396291839285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48215258722828264194559523 72322888084242396291839285)
      ·
        refine ⟨6780270757897724652359933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72322888084242396291839285 6780270757897724652359933)
        ·
          refine ⟨2542601534211646744634975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6780270757897724652359933 2542601534211646744634975)
          ·
            refine ⟨3813902301317470116952463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2542601534211646744634975 3813902301317470116952463)
            ·
              refine ⟨5720853451976205175428695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3813902301317470116952463 5720853451976205175428695)
              ·
                refine ⟨8581280177964307763143043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5720853451976205175428695 8581280177964307763143043)
                ·
                  refine ⟨12871920266946461644714565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8581280177964307763143043 12871920266946461644714565)
                  ·
                    refine ⟨2413485050052461558383981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12871920266946461644714565 2413485050052461558383981)
                    ·
                      refine ⟨905056893769673084393993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2413485050052461558383981 905056893769673084393993)
                      ·
                        rfl

theorem cell23_1762592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_1762592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762592 prefixEnd_1762592 := by exact prefixLift 1762592
  have htrace : WordTrace (prefixWord ++ tailWord_1762592) baseStart_1762592 baseEnd_1762592 := by
    simpa [prefixWord, tailWord_1762592, baseEnd_1762592] using wordTrace_append hprefix tailTrace_1762592
  have hstable : (prefixWord ++ tailWord_1762592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762592).length < 2 ^ (prefixWord ++ tailWord_1762592).sum := by decide
  have hdescent : baseEnd_1762592 < baseStart_1762592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762656 : List Nat := [2, 1, 1, 3, 4, 1, 3, 3, 1, 1, 3]
def baseStart_1762656 : Nat := 118140960795 + 1762656 * 2 ^ 59
def prefixEnd_1762656 : Nat := 4983230072969 + 3 ^ 40 * 1762656 * 2
def baseEnd_1762656 : Nat := 905089756531560833993699

theorem tailTrace_1762656 : CollatzResearch.WordTrace tailWord_1762656 prefixEnd_1762656 905089756531560833993699 := by
  unfold tailWord_1762656
  simp only [CollatzResearch.WordTrace]
  refine ⟨32144672951102912261537911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42859563934803883015383881 32144672951102912261537911)
  ·
    refine ⟨48217009426654368392306867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32144672951102912261537911 48217009426654368392306867)
    ·
      refine ⟨72325514139981552588460301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48217009426654368392306867 72325514139981552588460301)
      ·
        refine ⟨27122067802493082220672613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72325514139981552588460301 27122067802493082220672613)
        ·
          refine ⟨5085387712967452916376115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27122067802493082220672613 5085387712967452916376115)
          ·
            refine ⟨7628081569451179374564173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5085387712967452916376115 7628081569451179374564173)
            ·
              refine ⟨2860530588544192265461565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7628081569451179374564173 2860530588544192265461565)
              ·
                refine ⟨1072698970704072099548087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2860530588544192265461565 1072698970704072099548087)
                ·
                  refine ⟨1609048456056108149322131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1072698970704072099548087 1609048456056108149322131)
                  ·
                    refine ⟨2413572684084162223983197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1609048456056108149322131 2413572684084162223983197)
                    ·
                      refine ⟨905089756531560833993699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2413572684084162223983197 905089756531560833993699)
                      ·
                        rfl

theorem cell23_1762656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3, 1, 1, 3].length) (baseStart_1762656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762656 prefixEnd_1762656 := by exact prefixLift 1762656
  have htrace : WordTrace (prefixWord ++ tailWord_1762656) baseStart_1762656 baseEnd_1762656 := by
    simpa [prefixWord, tailWord_1762656, baseEnd_1762656] using wordTrace_append hprefix tailTrace_1762656
  have hstable : (prefixWord ++ tailWord_1762656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762656).length < 2 ^ (prefixWord ++ tailWord_1762656).sum := by decide
  have hdescent : baseEnd_1762656 < baseStart_1762656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762666 : List Nat := [3, 1, 3, 3, 2, 1, 1, 2, 2, 3, 2]
def baseStart_1762666 : Nat := 118140960795 + 1762666 * 2 ^ 59
def prefixEnd_1762666 : Nat := 4983230072969 + 3 ^ 40 * 1762666 * 2
def baseEnd_1762666 : Nat := 905094891338105794868653

theorem tailTrace_1762666 : CollatzResearch.WordTrace tailWord_1762666 prefixEnd_1762666 905094891338105794868653 := by
  unfold tailWord_1762666
  simp only [CollatzResearch.WordTrace]
  refine ⟨16072427658042399057734963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42859807088113064153959901 16072427658042399057734963)
  ·
    refine ⟨24108641487063598586602445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16072427658042399057734963 24108641487063598586602445)
    ·
      refine ⟨9040740557648849469975917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24108641487063598586602445 9040740557648849469975917)
      ·
        refine ⟨3390277709118318551240969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9040740557648849469975917 3390277709118318551240969)
        ·
          refine ⟨2542708281838738913430727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3390277709118318551240969 2542708281838738913430727)
          ·
            refine ⟨3814062422758108370146091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2542708281838738913430727 3814062422758108370146091)
            ·
              refine ⟨5721093634137162555219137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3814062422758108370146091 5721093634137162555219137)
              ·
                refine ⟨4290820225602871916414353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5721093634137162555219137 4290820225602871916414353)
                ·
                  refine ⟨3218115169202153937310765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4290820225602871916414353 3218115169202153937310765)
                  ·
                    refine ⟨1206793188450807726491537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3218115169202153937310765 1206793188450807726491537)
                    ·
                      refine ⟨905094891338105794868653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1206793188450807726491537 905094891338105794868653)
                      ·
                        rfl

theorem cell23_1762666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_1762666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1762666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1762666 prefixEnd_1762666 := by exact prefixLift 1762666
  have htrace : WordTrace (prefixWord ++ tailWord_1762666) baseStart_1762666 baseEnd_1762666 := by
    simpa [prefixWord, tailWord_1762666, baseEnd_1762666] using wordTrace_append hprefix tailTrace_1762666
  have hstable : (prefixWord ++ tailWord_1762666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762666).length < 2 ^ (prefixWord ++ tailWord_1762666).sum := by decide
  have hdescent : baseEnd_1762666 < baseStart_1762666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
