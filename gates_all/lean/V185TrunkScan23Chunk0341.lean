import V185TrunkScan23Chunk0340

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2015936 : List Nat := [2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 4]
def baseStart_2015936 : Nat := 118140960795 + 2015936 * 2 ^ 59
def prefixEnd_2015936 : Nat := 4983230072969 + 3 ^ 40 * 2015936 * 2
def baseEnd_2015936 : Nat := 1035144136702329874828885

theorem tailTrace_2015936 : CollatzResearch.WordTrace tailWord_2015936 prefixEnd_2015936 1035144136702329874828885 := by
  unfold tailWord_2015936
  simp only [CollatzResearch.WordTrace]
  refine ⟨36763613212307820651613831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49018150949743760868818441 36763613212307820651613831)
  ·
    refine ⟨55145419818461730977420747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36763613212307820651613831 55145419818461730977420747)
    ·
      refine ⟨82718129727692596466131121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55145419818461730977420747 82718129727692596466131121)
      ·
        refine ⟨62038597295769447349598341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82718129727692596466131121 62038597295769447349598341)
        ·
          refine ⟨11632236992956771378049689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62038597295769447349598341 11632236992956771378049689)
          ·
            refine ⟨8724177744717578533537267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11632236992956771378049689 8724177744717578533537267)
            ·
              refine ⟨13086266617076367800305901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8724177744717578533537267 13086266617076367800305901)
              ·
                refine ⟨4907349981403637925114713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13086266617076367800305901 4907349981403637925114713)
                ·
                  refine ⟨3680512486052728443836035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4907349981403637925114713 3680512486052728443836035)
                  ·
                    refine ⟨5520768729079092665754053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3680512486052728443836035 5520768729079092665754053)
                    ·
                      refine ⟨1035144136702329874828885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5520768729079092665754053 1035144136702329874828885)
                      ·
                        rfl

theorem cell23_2015936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_2015936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015936 prefixEnd_2015936 := by exact prefixLift 2015936
  have htrace : WordTrace (prefixWord ++ tailWord_2015936) baseStart_2015936 baseEnd_2015936 := by
    simpa [prefixWord, tailWord_2015936, baseEnd_2015936] using wordTrace_append hprefix tailTrace_2015936
  have hstable : (prefixWord ++ tailWord_2015936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015936).length < 2 ^ (prefixWord ++ tailWord_2015936).sum := by decide
  have hdescent : baseEnd_2015936 < baseStart_2015936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015999 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 5]
def baseStart_2015999 : Nat := 118140960795 + 2015999 * 2 ^ 59
def prefixEnd_2015999 : Nat := 4983230072969 + 3 ^ 40 * 2015999 * 2
def baseEnd_2015999 : Nat := 1035176485983563128341095

theorem tailTrace_2015999 : CollatzResearch.WordTrace tailWord_2015999 prefixEnd_2015999 1035176485983563128341095 := by
  unfold tailWord_2015999
  simp only [CollatzResearch.WordTrace]
  refine ⟨73529524223387403062771051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49019682815591602041847367 73529524223387403062771051)
  ·
    refine ⟨110294286335081104594156577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73529524223387403062771051 110294286335081104594156577)
    ·
      refine ⟨82720714751310828445617433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110294286335081104594156577 82720714751310828445617433)
      ·
        refine ⟨62040536063483121334213075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82720714751310828445617433 62040536063483121334213075)
        ·
          refine ⟨93060804095224682001319613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62040536063483121334213075 93060804095224682001319613)
          ·
            refine ⟨34897801535709255750494855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93060804095224682001319613 34897801535709255750494855)
            ·
              refine ⟨52346702303563883625742283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34897801535709255750494855 52346702303563883625742283)
              ·
                refine ⟨78520053455345825438613425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52346702303563883625742283 78520053455345825438613425)
                ·
                  refine ⟨58890040091509369078960069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78520053455345825438613425 58890040091509369078960069)
                  ·
                    refine ⟨11041882517158006702305013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58890040091509369078960069 11041882517158006702305013)
                    ·
                      refine ⟨1035176485983563128341095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11041882517158006702305013 1035176485983563128341095)
                      ·
                        rfl

theorem cell23_2015999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_2015999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2015999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2015999 prefixEnd_2015999 := by exact prefixLift 2015999
  have htrace : WordTrace (prefixWord ++ tailWord_2015999) baseStart_2015999 baseEnd_2015999 := by
    simpa [prefixWord, tailWord_2015999, baseEnd_2015999] using wordTrace_append hprefix tailTrace_2015999
  have hstable : (prefixWord ++ tailWord_2015999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015999).length < 2 ^ (prefixWord ++ tailWord_2015999).sum := by decide
  have hdescent : baseEnd_2015999 < baseStart_2015999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016053 : List Nat := [1, 3, 3, 1, 3, 1, 1, 2, 4, 4]
def baseStart_2016053 : Nat := 118140960795 + 2016053 * 2 ^ 59
def prefixEnd_2016053 : Nat := 4983230072969 + 3 ^ 40 * 2016053 * 2
def baseEnd_2016053 : Nat := 345068071312968639021949

theorem tailTrace_2016053 : CollatzResearch.WordTrace tailWord_2016053 prefixEnd_2016053 345068071312968639021949 := by
  unfold tailWord_2016053
  simp only [CollatzResearch.WordTrace]
  refine ⟨73531493765191770285236813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49020995843461180190157875 73531493765191770285236813)
  ·
    refine ⟨27574310161946913856963805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73531493765191770285236813 27574310161946913856963805)
    ·
      refine ⟨10340366310730092696361427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27574310161946913856963805 10340366310730092696361427)
      ·
        refine ⟨15510549466095139044542141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10340366310730092696361427 15510549466095139044542141)
        ·
          refine ⟨5816456049785677141703303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15510549466095139044542141 5816456049785677141703303)
          ·
            refine ⟨8724684074678515712554955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5816456049785677141703303 8724684074678515712554955)
            ·
              refine ⟨13087026112017773568832433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8724684074678515712554955 13087026112017773568832433)
              ·
                refine ⟨9815269584013330176624325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13087026112017773568832433 9815269584013330176624325)
                ·
                  refine ⟨1840363047002499408117061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9815269584013330176624325 1840363047002499408117061)
                  ·
                    refine ⟨345068071312968639021949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1840363047002499408117061 345068071312968639021949)
                    ·
                      rfl

theorem cell23_2016053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_2016053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016053 prefixEnd_2016053 := by exact prefixLift 2016053
  have htrace : WordTrace (prefixWord ++ tailWord_2016053) baseStart_2016053 baseEnd_2016053 := by
    simpa [prefixWord, tailWord_2016053, baseEnd_2016053] using wordTrace_append hprefix tailTrace_2016053
  have hstable : (prefixWord ++ tailWord_2016053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016053).length < 2 ^ (prefixWord ++ tailWord_2016053).sum := by decide
  have hdescent : baseEnd_2016053 < baseStart_2016053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016056 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 3, 2, 4]
def baseStart_2016056 : Nat := 118140960795 + 2016056 * 2 ^ 59
def prefixEnd_2016056 : Nat := 4983230072969 + 3 ^ 40 * 2016056 * 2
def baseEnd_2016056 : Nat := 1035205754380869405328333

theorem tailTrace_2016056 : CollatzResearch.WordTrace tailWord_2016056 prefixEnd_2016056 1035205754380869405328333 := by
  unfold tailWord_2016056
  simp only [CollatzResearch.WordTrace]
  refine ⟨36765801592090450898798011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49021068789453934531730681 36765801592090450898798011)
  ·
    refine ⟨55148702388135676348197017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36765801592090450898798011 55148702388135676348197017)
    ·
      refine ⟨41361526791101757261147763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55148702388135676348197017 41361526791101757261147763)
      ·
        refine ⟨62042290186652635891721645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41361526791101757261147763 62042290186652635891721645)
        ·
          refine ⟨23265858819994738459395617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62042290186652635891721645 23265858819994738459395617)
          ·
            refine ⟨17449394114996053844546713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23265858819994738459395617 17449394114996053844546713)
            ·
              refine ⟨13087045586247040383410035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17449394114996053844546713 13087045586247040383410035)
              ·
                refine ⟨19630568379370560575115053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13087045586247040383410035 19630568379370560575115053)
                ·
                  refine ⟨7361463142263960215668145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19630568379370560575115053 7361463142263960215668145)
                  ·
                    refine ⟨5521097356697970161751109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7361463142263960215668145 5521097356697970161751109)
                    ·
                      refine ⟨1035205754380869405328333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5521097356697970161751109 1035205754380869405328333)
                      ·
                        rfl

theorem cell23_2016056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_2016056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016056 prefixEnd_2016056 := by exact prefixLift 2016056
  have htrace : WordTrace (prefixWord ++ tailWord_2016056) baseStart_2016056 baseEnd_2016056 := by
    simpa [prefixWord, tailWord_2016056, baseEnd_2016056] using wordTrace_append hprefix tailTrace_2016056
  have hstable : (prefixWord ++ tailWord_2016056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016056).length < 2 ^ (prefixWord ++ tailWord_2016056).sum := by decide
  have hdescent : baseEnd_2016056 < baseStart_2016056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016063 : List Nat := [1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 5]
def baseStart_2016063 : Nat := 118140960795 + 2016063 * 2 ^ 59
def prefixEnd_2016063 : Nat := 4983230072969 + 3 ^ 40 * 2016063 * 2
def baseEnd_2016063 : Nat := 1035209348745450877940801

theorem tailTrace_2016063 : CollatzResearch.WordTrace tailWord_2016063 prefixEnd_2016063 1035209348745450877940801 := by
  unfold tailWord_2016063
  simp only [CollatzResearch.WordTrace]
  refine ⟨73531858495155541993100843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49021238996770361328733895 73531858495155541993100843)
  ·
    refine ⟨110297787742733312989651265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73531858495155541993100843 110297787742733312989651265)
    ·
      refine ⟨82723340807049984742238449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110297787742733312989651265 82723340807049984742238449)
      ·
        refine ⟨62042505605287488556678837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82723340807049984742238449 62042505605287488556678837)
        ·
          refine ⟨5816484900495702052188641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62042505605287488556678837 5816484900495702052188641)
          ·
            refine ⟨4362363675371776539141481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5816484900495702052188641 4362363675371776539141481)
            ·
              refine ⟨3271772756528832404356111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4362363675371776539141481 3271772756528832404356111)
              ·
                refine ⟨4907659134793248606534167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3271772756528832404356111 4907659134793248606534167)
                ·
                  refine ⟨7361488702189872909801251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4907659134793248606534167 7361488702189872909801251)
                  ·
                    refine ⟨11042233053284809364701877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7361488702189872909801251 11042233053284809364701877)
                    ·
                      refine ⟨1035209348745450877940801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11042233053284809364701877 1035209348745450877940801)
                      ·
                        rfl

theorem cell23_2016063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 5].length) (baseStart_2016063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016063 prefixEnd_2016063 := by exact prefixLift 2016063
  have htrace : WordTrace (prefixWord ++ tailWord_2016063) baseStart_2016063 baseEnd_2016063 := by
    simpa [prefixWord, tailWord_2016063, baseEnd_2016063] using wordTrace_append hprefix tailTrace_2016063
  have hstable : (prefixWord ++ tailWord_2016063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016063).length < 2 ^ (prefixWord ++ tailWord_2016063).sum := by decide
  have hdescent : baseEnd_2016063 < baseStart_2016063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016087 : List Nat := [1, 1, 3, 2, 4, 3, 2, 1, 2, 4]
def baseStart_2016087 : Nat := 118140960795 + 2016087 * 2 ^ 59
def prefixEnd_2016087 : Nat := 4983230072969 + 3 ^ 40 * 2016087 * 2
def baseEnd_2016087 : Nat := 345073890760386261346897

theorem tailTrace_2016087 : CollatzResearch.WordTrace tailWord_2016087 prefixEnd_2016087 345073890760386261346897 := by
  unfold tailWord_2016087
  simp only [CollatzResearch.WordTrace]
  refine ⟨73532733847068594091974515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49021822564712396061316343 73532733847068594091974515)
  ·
    refine ⟨110299100770602891137961773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73532733847068594091974515 110299100770602891137961773)
    ·
      refine ⟨41362162788976084176735665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110299100770602891137961773 41362162788976084176735665)
      ·
        refine ⟨31021622091732063132551749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41362162788976084176735665 31021622091732063132551749)
        ·
          refine ⟨5816554142199761837353453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31021622091732063132551749 5816554142199761837353453)
          ·
            refine ⟨2181207803324910689007545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5816554142199761837353453 2181207803324910689007545)
            ·
              refine ⟨1635905852493683016755659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2181207803324910689007545 1635905852493683016755659)
              ·
                refine ⟨2453858778740524525133489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1635905852493683016755659 2453858778740524525133489)
                ·
                  refine ⟨1840394084055393393850117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2453858778740524525133489 1840394084055393393850117)
                  ·
                    refine ⟨345073890760386261346897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1840394084055393393850117 345073890760386261346897)
                    ·
                      rfl

theorem cell23_2016087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 2, 4].length) (baseStart_2016087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016087 prefixEnd_2016087 := by exact prefixLift 2016087
  have htrace : WordTrace (prefixWord ++ tailWord_2016087) baseStart_2016087 baseEnd_2016087 := by
    simpa [prefixWord, tailWord_2016087, baseEnd_2016087] using wordTrace_append hprefix tailTrace_2016087
  have hstable : (prefixWord ++ tailWord_2016087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016087).length < 2 ^ (prefixWord ++ tailWord_2016087).sum := by decide
  have hdescent : baseEnd_2016087 < baseStart_2016087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016183 : List Nat := [1, 1, 3, 1, 3, 1, 3, 2, 2, 3, 3]
def baseStart_2016183 : Nat := 118140960795 + 2016183 * 2 ^ 59
def prefixEnd_2016183 : Nat := 4983230072969 + 3 ^ 40 * 2016183 * 2
def baseEnd_2016183 : Nat := 1035270966423990408440249

theorem tailTrace_2016183 : CollatzResearch.WordTrace tailWord_2016183 prefixEnd_2016183 1035270966423990408440249 := by
  unfold tailWord_2016183
  simp only [CollatzResearch.WordTrace]
  refine ⟨73536235254720802487469203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49024156836480534991646135 73536235254720802487469203)
  ·
    refine ⟨110304352882081203731203805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73536235254720802487469203 110304352882081203731203805)
    ·
      refine ⟨41364132330780451399201427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110304352882081203731203805 41364132330780451399201427)
      ·
        refine ⟨62046198496170677098802141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41364132330780451399201427 62046198496170677098802141)
        ·
          refine ⟨23267324436064003912050803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62046198496170677098802141 23267324436064003912050803)
          ·
            refine ⟨34900986654096005868076205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23267324436064003912050803 34900986654096005868076205)
            ·
              refine ⟨13087869995286002200528577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34900986654096005868076205 13087869995286002200528577)
              ·
                refine ⟨9815902496464501650396433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13087869995286002200528577 9815902496464501650396433)
                ·
                  refine ⟨7361926872348376237797325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9815902496464501650396433 7361926872348376237797325)
                  ·
                    refine ⟨2760722577130641089173997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7361926872348376237797325 2760722577130641089173997)
                    ·
                      refine ⟨1035270966423990408440249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2760722577130641089173997 1035270966423990408440249)
                      ·
                        rfl

theorem cell23_2016183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3, 3].length) (baseStart_2016183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016183 prefixEnd_2016183 := by exact prefixLift 2016183
  have htrace : WordTrace (prefixWord ++ tailWord_2016183) baseStart_2016183 baseEnd_2016183 := by
    simpa [prefixWord, tailWord_2016183, baseEnd_2016183] using wordTrace_append hprefix tailTrace_2016183
  have hstable : (prefixWord ++ tailWord_2016183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016183).length < 2 ^ (prefixWord ++ tailWord_2016183).sum := by decide
  have hdescent : baseEnd_2016183 < baseStart_2016183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016184 : List Nat := [2, 1, 2, 1, 2, 6, 1, 2, 2, 2, 2]
def baseStart_2016184 : Nat := 118140960795 + 2016184 * 2 ^ 59
def prefixEnd_2016184 : Nat := 4983230072969 + 3 ^ 40 * 2016184 * 2
def baseEnd_2016184 : Nat := 1035271479904644904527745

theorem tailTrace_2016184 : CollatzResearch.WordTrace tailWord_2016184 prefixEnd_2016184 1035271479904644904527745 := by
  unfold tailWord_2016184
  simp only [CollatzResearch.WordTrace]
  refine ⟨36768135863858589829127803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49024181151811453105503737 36768135863858589829127803)
  ·
    refine ⟨55152203795787884743691705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36768135863858589829127803 55152203795787884743691705)
    ·
      refine ⟨41364152846840913557768779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55152203795787884743691705 41364152846840913557768779)
      ·
        refine ⟨62046229270261370336653169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41364152846840913557768779 62046229270261370336653169)
        ·
          refine ⟨46534671952696027752489877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62046229270261370336653169 46534671952696027752489877)
          ·
            refine ⟨2181312747782626300897963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46534671952696027752489877 2181312747782626300897963)
            ·
              refine ⟨3271969121673939451346945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2181312747782626300897963 3271969121673939451346945)
              ·
                refine ⟨2453976841255454588510209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3271969121673939451346945 2453976841255454588510209)
                ·
                  refine ⟨1840482630941590941382657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2453976841255454588510209 1840482630941590941382657)
                  ·
                    refine ⟨1380361973206193206036993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1840482630941590941382657 1380361973206193206036993)
                    ·
                      refine ⟨1035271479904644904527745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1380361973206193206036993 1035271479904644904527745)
                      ·
                        rfl

theorem cell23_2016184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 2, 2, 2].length) (baseStart_2016184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016184 prefixEnd_2016184 := by exact prefixLift 2016184
  have htrace : WordTrace (prefixWord ++ tailWord_2016184) baseStart_2016184 baseEnd_2016184 := by
    simpa [prefixWord, tailWord_2016184, baseEnd_2016184] using wordTrace_append hprefix tailTrace_2016184
  have hstable : (prefixWord ++ tailWord_2016184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016184).length < 2 ^ (prefixWord ++ tailWord_2016184).sum := by decide
  have hdescent : baseEnd_2016184 < baseStart_2016184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016190 : List Nat := [4, 2, 1, 1, 1, 2, 1, 6, 5]
def baseStart_2016190 : Nat := 118140960795 + 2016190 * 2 ^ 59
def prefixEnd_2016190 : Nat := 4983230072969 + 3 ^ 40 * 2016190 * 2
def baseEnd_2016190 : Nat := 115030506754285764561413

theorem tailTrace_2016190 : CollatzResearch.WordTrace tailWord_2016190 prefixEnd_2016190 115030506754285764561413 := by
  unfold tailWord_2016190
  simp only [CollatzResearch.WordTrace]
  refine ⟨9192061320711930335371753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49024327043796961788649349 9192061320711930335371753)
  ·
    refine ⟨6894045990533947751528815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9192061320711930335371753 6894045990533947751528815)
    ·
      refine ⟨10341068985800921627293223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6894045990533947751528815 10341068985800921627293223)
      ·
        refine ⟨15511603478701382440939835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10341068985800921627293223 15511603478701382440939835)
        ·
          refine ⟨23267405218052073661409753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15511603478701382440939835 23267405218052073661409753)
          ·
            refine ⟨17450553913539055246057315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23267405218052073661409753 17450553913539055246057315)
            ·
              refine ⟨26175830870308582869085973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17450553913539055246057315 26175830870308582869085973)
              ·
                refine ⟨1226992072045714821988405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26175830870308582869085973 1226992072045714821988405)
                ·
                  refine ⟨115030506754285764561413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1226992072045714821988405 115030506754285764561413)
                  ·
                    rfl

theorem cell23_2016190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_2016190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016190 prefixEnd_2016190 := by exact prefixLift 2016190
  have htrace : WordTrace (prefixWord ++ tailWord_2016190) baseStart_2016190 baseEnd_2016190 := by
    simpa [prefixWord, tailWord_2016190, baseEnd_2016190] using wordTrace_append hprefix tailTrace_2016190
  have hstable : (prefixWord ++ tailWord_2016190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016190).length < 2 ^ (prefixWord ++ tailWord_2016190).sum := by decide
  have hdescent : baseEnd_2016190 < baseStart_2016190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016273 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 3]
def baseStart_2016273 : Nat := 118140960795 + 2016273 * 2 ^ 59
def prefixEnd_2016273 : Nat := 4983230072969 + 3 ^ 40 * 2016273 * 2
def baseEnd_2016273 : Nat := 1035317179682895056314835

theorem tailTrace_2016273 : CollatzResearch.WordTrace tailWord_2016273 prefixEnd_2016273 1035317179682895056314835 := by
  unfold tailWord_2016273
  simp only [CollatzResearch.WordTrace]
  refine ⟨73539517824394747858245473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49026345216263165238830315 73539517824394747858245473)
  ·
    refine ⟨55154638368296060893684105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73539517824394747858245473 55154638368296060893684105)
    ·
      refine ⟨41365978776222045670263079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55154638368296060893684105 41365978776222045670263079)
      ·
        refine ⟨62048968164333068505394619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41365978776222045670263079 62048968164333068505394619)
        ·
          refine ⟨93073452246499602758091929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62048968164333068505394619 93073452246499602758091929)
          ·
            refine ⟨69805089184874702068568947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93073452246499602758091929 69805089184874702068568947)
            ·
              refine ⟨104707633777312053102853421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69805089184874702068568947 104707633777312053102853421)
              ·
                refine ⟨39265362666492019913570033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104707633777312053102853421 39265362666492019913570033)
                ·
                  refine ⟨29449021999869014935177525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39265362666492019913570033 29449021999869014935177525)
                  ·
                    refine ⟨2760845812487720150172893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29449021999869014935177525 2760845812487720150172893)
                    ·
                      refine ⟨1035317179682895056314835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2760845812487720150172893 1035317179682895056314835)
                      ·
                        rfl

theorem cell23_2016273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 3].length) (baseStart_2016273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016273 prefixEnd_2016273 := by exact prefixLift 2016273
  have htrace : WordTrace (prefixWord ++ tailWord_2016273) baseStart_2016273 baseEnd_2016273 := by
    simpa [prefixWord, tailWord_2016273, baseEnd_2016273] using wordTrace_append hprefix tailTrace_2016273
  have hstable : (prefixWord ++ tailWord_2016273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016273).length < 2 ^ (prefixWord ++ tailWord_2016273).sum := by decide
  have hdescent : baseEnd_2016273 < baseStart_2016273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016277 : List Nat := [1, 3, 2, 1, 4, 2, 2, 1, 2, 2, 3]
def baseStart_2016277 : Nat := 118140960795 + 2016277 * 2 ^ 59
def prefixEnd_2016277 : Nat := 4983230072969 + 3 ^ 40 * 2016277 * 2
def baseEnd_2016277 : Nat := 1035319233605513040664817

theorem tailTrace_2016277 : CollatzResearch.WordTrace tailWord_2016277 prefixEnd_2016277 1035319233605513040664817 := by
  unfold tailWord_2016277
  simp only [CollatzResearch.WordTrace]
  refine ⟨73539663716380256541391085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49026442477586837694260723 73539663716380256541391085)
  ·
    refine ⟨27577373893642596203021657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73539663716380256541391085 27577373893642596203021657)
    ·
      refine ⟨20683030420231947152266243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27577373893642596203021657 20683030420231947152266243)
      ·
        refine ⟨31024545630347920728399365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20683030420231947152266243 31024545630347920728399365)
        ·
          refine ⟨5817102305690235136574881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31024545630347920728399365 5817102305690235136574881)
          ·
            refine ⟨4362826729267676352431161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5817102305690235136574881 4362826729267676352431161)
            ·
              refine ⟨3272120046950757264323371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4362826729267676352431161 3272120046950757264323371)
              ·
                refine ⟨4908180070426135896485057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3272120046950757264323371 4908180070426135896485057)
                ·
                  refine ⟨3681135052819601922363793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4908180070426135896485057 3681135052819601922363793)
                  ·
                    refine ⟨2760851289614701441772845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3681135052819601922363793 2760851289614701441772845)
                    ·
                      refine ⟨1035319233605513040664817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2760851289614701441772845 1035319233605513040664817)
                      ·
                        rfl

theorem cell23_2016277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_2016277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016277 prefixEnd_2016277 := by exact prefixLift 2016277
  have htrace : WordTrace (prefixWord ++ tailWord_2016277) baseStart_2016277 baseEnd_2016277 := by
    simpa [prefixWord, tailWord_2016277, baseEnd_2016277] using wordTrace_append hprefix tailTrace_2016277
  have hstable : (prefixWord ++ tailWord_2016277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016277).length < 2 ^ (prefixWord ++ tailWord_2016277).sum := by decide
  have hdescent : baseEnd_2016277 < baseStart_2016277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016330 : List Nat := [3, 1, 2, 1, 1, 2, 4, 1, 3, 1, 4]
def baseStart_2016330 : Nat := 118140960795 + 2016330 * 2 ^ 59
def prefixEnd_2016330 : Nat := 4983230072969 + 3 ^ 40 * 2016330 * 2
def baseEnd_2016330 : Nat := 1035346448080201333302073

theorem tailTrace_2016330 : CollatzResearch.WordTrace tailWord_2016330 prefixEnd_2016330 1035346448080201333302073 := by
  unfold tailWord_2016330
  simp only [CollatzResearch.WordTrace]
  refine ⟨18385399196297061648267611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49027731190125497728713629 18385399196297061648267611)
  ·
    refine ⟨27578098794445592472401417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18385399196297061648267611 27578098794445592472401417)
    ·
      refine ⟨20683574095834194354301063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27578098794445592472401417 20683574095834194354301063)
      ·
        refine ⟨31025361143751291531451595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20683574095834194354301063 31025361143751291531451595)
        ·
          refine ⟨46538041715626937297177393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31025361143751291531451595 46538041715626937297177393)
          ·
            refine ⟨34903531286720202972883045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46538041715626937297177393 34903531286720202972883045)
            ·
              refine ⟨6544412116260038057415571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34903531286720202972883045 6544412116260038057415571)
              ·
                refine ⟨9816618174390057086123357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6544412116260038057415571 9816618174390057086123357)
                ·
                  refine ⟨3681231815396271407296259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9816618174390057086123357 3681231815396271407296259)
                  ·
                    refine ⟨5521847723094407110944389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3681231815396271407296259 5521847723094407110944389)
                    ·
                      refine ⟨1035346448080201333302073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5521847723094407110944389 1035346448080201333302073)
                      ·
                        rfl

theorem cell23_2016330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_2016330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016330 prefixEnd_2016330 := by exact prefixLift 2016330
  have htrace : WordTrace (prefixWord ++ tailWord_2016330) baseStart_2016330 baseEnd_2016330 := by
    simpa [prefixWord, tailWord_2016330, baseEnd_2016330] using wordTrace_append hprefix tailTrace_2016330
  have hstable : (prefixWord ++ tailWord_2016330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016330).length < 2 ^ (prefixWord ++ tailWord_2016330).sum := by decide
  have hdescent : baseEnd_2016330 < baseStart_2016330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016340 : List Nat := [2, 4, 1, 1, 1, 1, 4, 2, 1, 6]
def baseStart_2016340 : Nat := 118140960795 + 2016340 * 2 ^ 59
def prefixEnd_2016340 : Nat := 4983230072969 + 3 ^ 40 * 2016340 * 2
def baseEnd_2016340 : Nat := 345117194295582098059009

theorem tailTrace_2016340 : CollatzResearch.WordTrace tailWord_2016340 prefixEnd_2016340 345117194295582098059009 := by
  unfold tailWord_2016340
  simp only [CollatzResearch.WordTrace]
  refine ⟨36770980757576009150467237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49027974343434678867289649 36770980757576009150467237)
  ·
    refine ⟨6894558892045501715712607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36770980757576009150467237 6894558892045501715712607)
    ·
      refine ⟨10341838338068252573568911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6894558892045501715712607 10341838338068252573568911)
      ·
        refine ⟨15512757507102378860353367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10341838338068252573568911 15512757507102378860353367)
        ·
          refine ⟨23269136260653568290530051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15512757507102378860353367 23269136260653568290530051)
          ·
            refine ⟨34903704390980352435795077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23269136260653568290530051 34903704390980352435795077)
            ·
              refine ⟨6544444573308816081711577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34903704390980352435795077 6544444573308816081711577)
              ·
                refine ⟨4908333429981612061283683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6544444573308816081711577 4908333429981612061283683)
                ·
                  refine ⟨7362500144972418091925525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4908333429981612061283683 7362500144972418091925525)
                  ·
                    refine ⟨345117194295582098059009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7362500144972418091925525 345117194295582098059009)
                    ·
                      rfl

theorem cell23_2016340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_2016340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016340 prefixEnd_2016340 := by exact prefixLift 2016340
  have htrace : WordTrace (prefixWord ++ tailWord_2016340) baseStart_2016340 baseEnd_2016340 := by
    simpa [prefixWord, tailWord_2016340, baseEnd_2016340] using wordTrace_append hprefix tailTrace_2016340
  have hstable : (prefixWord ++ tailWord_2016340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016340).length < 2 ^ (prefixWord ++ tailWord_2016340).sum := by decide
  have hdescent : baseEnd_2016340 < baseStart_2016340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016343 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 6]
def baseStart_2016343 : Nat := 118140960795 + 2016343 * 2 ^ 59
def prefixEnd_2016343 : Nat := 4983230072969 + 3 ^ 40 * 2016343 * 2
def baseEnd_2016343 : Nat := 1035353123328709782439513

theorem tailTrace_2016343 : CollatzResearch.WordTrace tailWord_2016343 prefixEnd_2016343 1035353123328709782439513 := by
  unfold tailWord_2016343
  simp only [CollatzResearch.WordTrace]
  refine ⟨73542070934141149813293683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49028047289427433208862455 73542070934141149813293683)
  ·
    refine ⟨110313106401211724719940525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73542070934141149813293683 110313106401211724719940525)
    ·
      refine ⟨41367414900454396769977697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110313106401211724719940525 41367414900454396769977697)
      ·
        refine ⟨31025561175340797577483273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41367414900454396769977697 31025561175340797577483273)
        ·
          refine ⟨23269170881505598183112455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31025561175340797577483273 23269170881505598183112455)
          ·
            refine ⟨34903756322258397274668683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23269170881505598183112455 34903756322258397274668683)
            ·
              refine ⟨52355634483387595912003025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34903756322258397274668683 52355634483387595912003025)
              ·
                refine ⟨39266725862540696934002269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52355634483387595912003025 39266725862540696934002269)
                ·
                  refine ⟨14725022198452761350250851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39266725862540696934002269 14725022198452761350250851)
                  ·
                    refine ⟨22087533297679142025376277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14725022198452761350250851 22087533297679142025376277)
                    ·
                      refine ⟨1035353123328709782439513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22087533297679142025376277 1035353123328709782439513)
                      ·
                        rfl

theorem cell23_2016343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_2016343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016343 prefixEnd_2016343 := by exact prefixLift 2016343
  have htrace : WordTrace (prefixWord ++ tailWord_2016343) baseStart_2016343 baseEnd_2016343 := by
    simpa [prefixWord, tailWord_2016343, baseEnd_2016343] using wordTrace_append hprefix tailTrace_2016343
  have hstable : (prefixWord ++ tailWord_2016343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016343).length < 2 ^ (prefixWord ++ tailWord_2016343).sum := by decide
  have hdescent : baseEnd_2016343 < baseStart_2016343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016364 : List Nat := [2, 2, 1, 1, 3, 2, 4, 1, 3, 2, 2]
def baseStart_2016364 : Nat := 118140960795 + 2016364 * 2 ^ 59
def prefixEnd_2016364 : Nat := 4983230072969 + 3 ^ 40 * 2016364 * 2
def baseEnd_2016364 : Nat := 1035363906422454200276917

theorem tailTrace_2016364 : CollatzResearch.WordTrace tailWord_2016364 prefixEnd_2016364 1035363906422454200276917 := by
  unfold tailWord_2016364
  simp only [CollatzResearch.WordTrace]
  refine ⟨36771418433532535199904073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49028557911376713599872097 36771418433532535199904073)
  ·
    refine ⟨27578563825149401399928055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36771418433532535199904073 27578563825149401399928055)
    ·
      refine ⟨41367845737724102099892083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27578563825149401399928055 41367845737724102099892083)
      ·
        refine ⟨62051768606586153149838125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41367845737724102099892083 62051768606586153149838125)
        ·
          refine ⟨23269413227469807431189297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62051768606586153149838125 23269413227469807431189297)
          ·
            refine ⟨17452059920602355573391973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23269413227469807431189297 17452059920602355573391973)
            ·
              refine ⟨3272261235112941670010995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17452059920602355573391973 3272261235112941670010995)
              ·
                refine ⟨4908391852669412505016493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3272261235112941670010995 4908391852669412505016493)
                ·
                  refine ⟨1840646944751029689381185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4908391852669412505016493 1840646944751029689381185)
                  ·
                    refine ⟨1380485208563272267035889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1840646944751029689381185 1380485208563272267035889)
                    ·
                      refine ⟨1035363906422454200276917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1380485208563272267035889 1035363906422454200276917)
                      ·
                        rfl

theorem cell23_2016364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 2, 2].length) (baseStart_2016364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016364 prefixEnd_2016364 := by exact prefixLift 2016364
  have htrace : WordTrace (prefixWord ++ tailWord_2016364) baseStart_2016364 baseEnd_2016364 := by
    simpa [prefixWord, tailWord_2016364, baseEnd_2016364] using wordTrace_append hprefix tailTrace_2016364
  have hstable : (prefixWord ++ tailWord_2016364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016364).length < 2 ^ (prefixWord ++ tailWord_2016364).sum := by decide
  have hdescent : baseEnd_2016364 < baseStart_2016364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016398 : List Nat := [4, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2]
def baseStart_2016398 : Nat := 118140960795 + 2016398 * 2 ^ 59
def prefixEnd_2016398 : Nat := 4983230072969 + 3 ^ 40 * 2016398 * 2
def baseEnd_2016398 : Nat := 1035381364764707067251761

theorem tailTrace_2016398 : CollatzResearch.WordTrace tailWord_2016398 prefixEnd_2016398 1035381364764707067251761 := by
  unfold tailWord_2016398
  simp only [CollatzResearch.WordTrace]
  refine ⟨9193009618617736775818231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49029384632627929471030565 9193009618617736775818231)
  ·
    refine ⟨13789514427926605163727347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9193009618617736775818231 13789514427926605163727347)
    ·
      refine ⟨20684271641889907745591021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13789514427926605163727347 20684271641889907745591021)
      ·
        refine ⟨7756601865708715404596633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20684271641889907745591021 7756601865708715404596633)
        ·
          refine ⟨5817451399281536553447475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7756601865708715404596633 5817451399281536553447475)
          ·
            refine ⟨8726177098922304830171213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5817451399281536553447475 8726177098922304830171213)
            ·
              refine ⟨3272316412095864311314205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8726177098922304830171213 3272316412095864311314205)
              ·
                refine ⟨1227118654535949116742827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3272316412095864311314205 1227118654535949116742827)
                ·
                  refine ⟨1840677981803923675114241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1227118654535949116742827 1840677981803923675114241)
                  ·
                    refine ⟨1380508486352942756335681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1840677981803923675114241 1380508486352942756335681)
                    ·
                      refine ⟨1035381364764707067251761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1380508486352942756335681 1035381364764707067251761)
                      ·
                        rfl

theorem cell23_2016398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_2016398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016398 prefixEnd_2016398 := by exact prefixLift 2016398
  have htrace : WordTrace (prefixWord ++ tailWord_2016398) baseStart_2016398 baseEnd_2016398 := by
    simpa [prefixWord, tailWord_2016398, baseEnd_2016398] using wordTrace_append hprefix tailTrace_2016398
  have hstable : (prefixWord ++ tailWord_2016398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016398).length < 2 ^ (prefixWord ++ tailWord_2016398).sum := by decide
  have hdescent : baseEnd_2016398 < baseStart_2016398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016415 : List Nat := [1, 1, 2, 6, 2, 1, 3, 2, 1, 2, 2]
def baseStart_2016415 : Nat := 118140960795 + 2016415 * 2 ^ 59
def prefixEnd_2016415 : Nat := 4983230072969 + 3 ^ 40 * 2016415 * 2
def baseEnd_2016415 : Nat := 1035390093935833500739183

theorem tailTrace_2016415 : CollatzResearch.WordTrace tailWord_2016415 prefixEnd_2016415 1035390093935833500739183 := by
  unfold tailWord_2016415
  simp only [CollatzResearch.WordTrace]
  refine ⟨73544696989880306109914699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49029797993253537406609799 73544696989880306109914699)
  ·
    refine ⟨110317045484820459164872049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73544696989880306109914699 110317045484820459164872049)
    ·
      refine ⟨82737784113615344373654037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110317045484820459164872049 82737784113615344373654037)
      ·
        refine ⟨3878333630325719267515033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 82737784113615344373654037 3878333630325719267515033)
        ·
          refine ⟨2908750222744289450636275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3878333630325719267515033 2908750222744289450636275)
          ·
            refine ⟨4363125334116434175954413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2908750222744289450636275 4363125334116434175954413)
            ·
              refine ⟨1636172000293662815982905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4363125334116434175954413 1636172000293662815982905)
              ·
                refine ⟨1227129000220247111987179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1636172000293662815982905 1227129000220247111987179)
                ·
                  refine ⟨1840693500330370667980769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1227129000220247111987179 1840693500330370667980769)
                  ·
                    refine ⟨1380520125247778000985577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1840693500330370667980769 1380520125247778000985577)
                    ·
                      refine ⟨1035390093935833500739183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1380520125247778000985577 1035390093935833500739183)
                      ·
                        rfl

theorem cell23_2016415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_2016415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016415 prefixEnd_2016415 := by exact prefixLift 2016415
  have htrace : WordTrace (prefixWord ++ tailWord_2016415) baseStart_2016415 baseEnd_2016415 := by
    simpa [prefixWord, tailWord_2016415, baseEnd_2016415] using wordTrace_append hprefix tailTrace_2016415
  have hstable : (prefixWord ++ tailWord_2016415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016415).length < 2 ^ (prefixWord ++ tailWord_2016415).sum := by decide
  have hdescent : baseEnd_2016415 < baseStart_2016415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016440 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 4, 4, 3]
def baseStart_2016440 : Nat := 118140960795 + 2016440 * 2 ^ 59
def prefixEnd_2016440 : Nat := 4983230072969 + 3 ^ 40 * 2016440 * 2
def baseEnd_2016440 : Nat := 1035402930952195902926567

theorem tailTrace_2016440 : CollatzResearch.WordTrace tailWord_2016440 prefixEnd_2016440 1035402930952195902926567 := by
  unfold tailWord_2016440
  simp only [CollatzResearch.WordTrace]
  refine ⟨36772804407394867689787387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49030405876526490253049849 36772804407394867689787387)
  ·
    refine ⟨55159206611092301534681081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36772804407394867689787387 55159206611092301534681081)
    ·
      refine ⟨41369404958319226151010811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55159206611092301534681081 41369404958319226151010811)
      ·
        refine ⟨62054107437478839226516217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41369404958319226151010811 62054107437478839226516217)
        ·
          refine ⟨46540580578109129419887163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62054107437478839226516217 46540580578109129419887163)
          ·
            refine ⟨69810870867163694129830745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46540580578109129419887163 69810870867163694129830745)
            ·
              refine ⟨52358153150372770597373059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69810870867163694129830745 52358153150372770597373059)
              ·
                refine ⟨78537229725559155896059589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52358153150372770597373059 78537229725559155896059589)
                ·
                  refine ⟨14725730573542341730511173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78537229725559155896059589 14725730573542341730511173)
                  ·
                    refine ⟨2761074482539189074470845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14725730573542341730511173 2761074482539189074470845)
                    ·
                      refine ⟨1035402930952195902926567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2761074482539189074470845 1035402930952195902926567)
                      ·
                        rfl

theorem cell23_2016440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 4, 4, 3].length) (baseStart_2016440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016440 prefixEnd_2016440 := by exact prefixLift 2016440
  have htrace : WordTrace (prefixWord ++ tailWord_2016440) baseStart_2016440 baseEnd_2016440 := by
    simpa [prefixWord, tailWord_2016440, baseEnd_2016440] using wordTrace_append hprefix tailTrace_2016440
  have hstable : (prefixWord ++ tailWord_2016440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016440).length < 2 ^ (prefixWord ++ tailWord_2016440).sum := by decide
  have hdescent : baseEnd_2016440 < baseStart_2016440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016441 : List Nat := [1, 2, 1, 4, 1, 5, 1, 2, 1, 3, 2]
def baseStart_2016441 : Nat := 118140960795 + 2016441 * 2 ^ 59
def prefixEnd_2016441 : Nat := 4983230072969 + 3 ^ 40 * 2016441 * 2
def baseEnd_2016441 : Nat := 1035403444432850399014063

theorem tailTrace_2016441 : CollatzResearch.WordTrace tailWord_2016441 prefixEnd_2016441 1035403444432850399014063 := by
  unfold tailWord_2016441
  simp only [CollatzResearch.WordTrace]
  refine ⟨73545645287786112550361177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49030430191857408366907451 73545645287786112550361177)
  ·
    refine ⟨55159233965839584412770883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73545645287786112550361177 55159233965839584412770883)
    ·
      refine ⟨82738850948759376619156325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55159233965839584412770883 82738850948759376619156325)
      ·
        refine ⟨15513534552892383116091811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82738850948759376619156325 15513534552892383116091811)
        ·
          refine ⟨23270301829338574674137717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15513534552892383116091811 23270301829338574674137717)
          ·
            refine ⟨2181590796500491375700411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23270301829338574674137717 2181590796500491375700411)
            ·
              refine ⟨3272386194750737063550617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2181590796500491375700411 3272386194750737063550617)
              ·
                refine ⟨2454289646063052797662963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3272386194750737063550617 2454289646063052797662963)
                ·
                  refine ⟨3681434469094579196494445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2454289646063052797662963 3681434469094579196494445)
                  ·
                    refine ⟨1380537925910467198685417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3681434469094579196494445 1380537925910467198685417)
                    ·
                      refine ⟨1035403444432850399014063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1380537925910467198685417 1035403444432850399014063)
                      ·
                        rfl

theorem cell23_2016441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_2016441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016441 prefixEnd_2016441 := by exact prefixLift 2016441
  have htrace : WordTrace (prefixWord ++ tailWord_2016441) baseStart_2016441 baseEnd_2016441 := by
    simpa [prefixWord, tailWord_2016441, baseEnd_2016441] using wordTrace_append hprefix tailTrace_2016441
  have hstable : (prefixWord ++ tailWord_2016441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016441).length < 2 ^ (prefixWord ++ tailWord_2016441).sum := by decide
  have hdescent : baseEnd_2016441 < baseStart_2016441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016497 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 4, 5, 2]
def baseStart_2016497 : Nat := 118140960795 + 2016497 * 2 ^ 59
def prefixEnd_2016497 : Nat := 4983230072969 + 3 ^ 40 * 2016497 * 2
def baseEnd_2016497 : Nat := 1035432199349502179913805

theorem tailTrace_2016497 : CollatzResearch.WordTrace tailWord_2016497 prefixEnd_2016497 1035432199349502179913805 := by
  unfold tailWord_2016497
  simp only [CollatzResearch.WordTrace]
  refine ⟨73547687775583234114399745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49031791850388822742933163 73547687775583234114399745)
  ·
    refine ⟨55160765831687425585799809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73547687775583234114399745 55160765831687425585799809)
    ·
      refine ⟨41370574373765569189349857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55160765831687425585799809 41370574373765569189349857)
      ·
        refine ⟨31027930780324176892012393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41370574373765569189349857 31027930780324176892012393)
        ·
          refine ⟨23270948085243132669009295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31027930780324176892012393 23270948085243132669009295)
          ·
            refine ⟨34906422127864699003513943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23270948085243132669009295 34906422127864699003513943)
            ·
              refine ⟨52359633191797048505270915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34906422127864699003513943 52359633191797048505270915)
              ·
                refine ⟨78539449787695572757906373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52359633191797048505270915 78539449787695572757906373)
                ·
                  refine ⟨14726146835192919892107445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78539449787695572757906373 14726146835192919892107445)
                  ·
                    refine ⟨1380576265799336239885073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14726146835192919892107445 1380576265799336239885073)
                    ·
                      refine ⟨1035432199349502179913805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1380576265799336239885073 1035432199349502179913805)
                      ·
                        rfl

theorem cell23_2016497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 5, 2].length) (baseStart_2016497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016497 prefixEnd_2016497 := by exact prefixLift 2016497
  have htrace : WordTrace (prefixWord ++ tailWord_2016497) baseStart_2016497 baseEnd_2016497 := by
    simpa [prefixWord, tailWord_2016497, baseEnd_2016497] using wordTrace_append hprefix tailTrace_2016497
  have hstable : (prefixWord ++ tailWord_2016497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016497).length < 2 ^ (prefixWord ++ tailWord_2016497).sum := by decide
  have hdescent : baseEnd_2016497 < baseStart_2016497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016547 : List Nat := [1, 1, 1, 4, 2, 3, 1, 2, 1, 4, 3]
def baseStart_2016547 : Nat := 118140960795 + 2016547 * 2 ^ 59
def prefixEnd_2016547 : Nat := 4983230072969 + 3 ^ 40 * 2016547 * 2
def baseEnd_2016547 : Nat := 1035457873382226984288575

theorem tailTrace_2016547 : CollatzResearch.WordTrace tailWord_2016547 prefixEnd_2016547 1035457873382226984288575 := by
  unfold tailWord_2016547
  simp only [CollatzResearch.WordTrace]
  refine ⟨73549511425402092653719895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49033007616934728435813263 73549511425402092653719895)
  ·
    refine ⟨110324267138103138980579843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73549511425402092653719895 110324267138103138980579843)
    ·
      refine ⟨165486400707154708470869765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110324267138103138980579843 165486400707154708470869765)
      ·
        refine ⟨31028700132591507838288081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165486400707154708470869765 31028700132591507838288081)
        ·
          refine ⟨23271525099443630878716061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31028700132591507838288081 23271525099443630878716061)
          ·
            refine ⟨8726821912291361579518523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23271525099443630878716061 8726821912291361579518523)
            ·
              refine ⟨13090232868437042369277785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8726821912291361579518523 13090232868437042369277785)
              ·
                refine ⟨9817674651327781776958339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13090232868437042369277785 9817674651327781776958339)
                ·
                  refine ⟨14726511976991672665437509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9817674651327781776958339 14726511976991672665437509)
                  ·
                    refine ⟨2761220995685938624769533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14726511976991672665437509 2761220995685938624769533)
                    ·
                      refine ⟨1035457873382226984288575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2761220995685938624769533 1035457873382226984288575)
                      ·
                        rfl

theorem cell23_2016547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_2016547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016547 prefixEnd_2016547 := by exact prefixLift 2016547
  have htrace : WordTrace (prefixWord ++ tailWord_2016547) baseStart_2016547 baseEnd_2016547 := by
    simpa [prefixWord, tailWord_2016547, baseEnd_2016547] using wordTrace_append hprefix tailTrace_2016547
  have hstable : (prefixWord ++ tailWord_2016547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016547).length < 2 ^ (prefixWord ++ tailWord_2016547).sum := by decide
  have hdescent : baseEnd_2016547 < baseStart_2016547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016564 : List Nat := [2, 5, 1, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_2016564 : Nat := 118140960795 + 2016564 * 2 ^ 59
def prefixEnd_2016564 : Nat := 4983230072969 + 3 ^ 40 * 2016564 * 2
def baseEnd_2016564 : Nat := 1035466602553353417775997

theorem tailTrace_2016564 : CollatzResearch.WordTrace tailWord_2016564 prefixEnd_2016564 1035466602553353417775997 := by
  unfold tailWord_2016564
  simp only [CollatzResearch.WordTrace]
  refine ⟨36775065733170252278544373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49033420977560336371392497 36775065733170252278544373)
  ·
    refine ⟨3447662412484711151113535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36775065733170252278544373 3447662412484711151113535)
    ·
      refine ⟨5171493618727066726670303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3447662412484711151113535 5171493618727066726670303)
      ·
        refine ⟨7757240428090600090005455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5171493618727066726670303 7757240428090600090005455)
        ·
          refine ⟨11635860642135900135008183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7757240428090600090005455 11635860642135900135008183)
          ·
            refine ⟨17453790963203850202512275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11635860642135900135008183 17453790963203850202512275)
            ·
              refine ⟨26180686444805775303768413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17453790963203850202512275 26180686444805775303768413)
              ·
                refine ⟨9817757416802165738913155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26180686444805775303768413 9817757416802165738913155)
                ·
                  refine ⟨14726636125203248608369733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9817757416802165738913155 14726636125203248608369733)
                  ·
                    refine ⟨2761244273475609114069325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14726636125203248608369733 2761244273475609114069325)
                    ·
                      refine ⟨1035466602553353417775997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2761244273475609114069325 1035466602553353417775997)
                      ·
                        rfl

theorem cell23_2016564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_2016564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016564 prefixEnd_2016564 := by exact prefixLift 2016564
  have htrace : WordTrace (prefixWord ++ tailWord_2016564) baseStart_2016564 baseEnd_2016564 := by
    simpa [prefixWord, tailWord_2016564, baseEnd_2016564] using wordTrace_append hprefix tailTrace_2016564
  have hstable : (prefixWord ++ tailWord_2016564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016564).length < 2 ^ (prefixWord ++ tailWord_2016564).sum := by decide
  have hdescent : baseEnd_2016564 < baseStart_2016564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016588 : List Nat := [2, 2, 1, 3, 2, 3, 3, 2, 1, 4]
def baseStart_2016588 : Nat := 118140960795 + 2016588 * 2 ^ 59
def prefixEnd_2016588 : Nat := 4983230072969 + 3 ^ 40 * 2016588 * 2
def baseEnd_2016588 : Nat := 345159642029687107958629

theorem tailTrace_2016588 : CollatzResearch.WordTrace tailWord_2016588 prefixEnd_2016588 345159642029687107958629 := by
  unfold tailWord_2016588
  simp only [CollatzResearch.WordTrace]
  refine ⟨36775503409126778327981209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49034004545502371103974945 36775503409126778327981209)
  ·
    refine ⟨27581627556845083745985907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36775503409126778327981209 27581627556845083745985907)
    ·
      refine ⟨41372441335267625618978861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27581627556845083745985907 41372441335267625618978861)
      ·
        refine ⟨15514665500725359607117073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41372441335267625618978861 15514665500725359607117073)
        ·
          refine ⟨11635999125544019705337805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15514665500725359607117073 11635999125544019705337805)
          ·
            refine ⟨4363499672079007389501677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11635999125544019705337805 4363499672079007389501677)
            ·
              refine ⟨1636312377029627771063129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4363499672079007389501677 1636312377029627771063129)
              ·
                refine ⟨1227234282772220828297347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1636312377029627771063129 1227234282772220828297347)
                ·
                  refine ⟨1840851424158331242446021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1227234282772220828297347 1840851424158331242446021)
                  ·
                    refine ⟨345159642029687107958629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1840851424158331242446021 345159642029687107958629)
                    ·
                      rfl

theorem cell23_2016588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2, 1, 4].length) (baseStart_2016588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016588 prefixEnd_2016588 := by exact prefixLift 2016588
  have htrace : WordTrace (prefixWord ++ tailWord_2016588) baseStart_2016588 baseEnd_2016588 := by
    simpa [prefixWord, tailWord_2016588, baseEnd_2016588] using wordTrace_append hprefix tailTrace_2016588
  have hstable : (prefixWord ++ tailWord_2016588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016588).length < 2 ^ (prefixWord ++ tailWord_2016588).sum := by decide
  have hdescent : baseEnd_2016588 < baseStart_2016588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016621 : List Nat := [1, 5, 1, 1, 1, 3, 1, 3, 2, 3, 2]
def baseStart_2016621 : Nat := 118140960795 + 2016621 * 2 ^ 59
def prefixEnd_2016621 : Nat := 4983230072969 + 3 ^ 40 * 2016621 * 2
def baseEnd_2016621 : Nat := 1035495870950659694763235

theorem tailTrace_2016621 : CollatzResearch.WordTrace tailWord_2016621 prefixEnd_2016621 1035495870950659694763235 := by
  unfold tailWord_2016621
  simp only [CollatzResearch.WordTrace]
  refine ⟨73552210427134003291913717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49034806951422668861275811 73552210427134003291913717)
  ·
    refine ⟨6895519727543812808616911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73552210427134003291913717 6895519727543812808616911)
    ·
      refine ⟨10343279591315719212925367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6895519727543812808616911 10343279591315719212925367)
      ·
        refine ⟨15514919386973578819388051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10343279591315719212925367 15514919386973578819388051)
        ·
          refine ⟨23272379080460368229082077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15514919386973578819388051 23272379080460368229082077)
          ·
            refine ⟨8727142155172638085905779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23272379080460368229082077 8727142155172638085905779)
            ·
              refine ⟨13090713232758957128858669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8727142155172638085905779 13090713232758957128858669)
              ·
                refine ⟨4909017462284608923322001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13090713232758957128858669 4909017462284608923322001)
                ·
                  refine ⟨3681763096713456692491501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4909017462284608923322001 3681763096713456692491501)
                  ·
                    refine ⟨1380661161267546259684313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3681763096713456692491501 1380661161267546259684313)
                    ·
                      refine ⟨1035495870950659694763235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1380661161267546259684313 1035495870950659694763235)
                      ·
                        rfl

theorem cell23_2016621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_2016621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016621 prefixEnd_2016621 := by exact prefixLift 2016621
  have htrace : WordTrace (prefixWord ++ tailWord_2016621) baseStart_2016621 baseEnd_2016621 := by
    simpa [prefixWord, tailWord_2016621, baseEnd_2016621] using wordTrace_append hprefix tailTrace_2016621
  have hstable : (prefixWord ++ tailWord_2016621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016621).length < 2 ^ (prefixWord ++ tailWord_2016621).sum := by decide
  have hdescent : baseEnd_2016621 < baseStart_2016621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016651 : List Nat := [1, 1, 1, 1, 4, 3, 2, 3, 3, 2, 2]
def baseStart_2016651 : Nat := 118140960795 + 2016651 * 2 ^ 59
def prefixEnd_2016651 : Nat := 4983230072969 + 3 ^ 40 * 2016651 * 2
def baseEnd_2016651 : Nat := 1035511275370294577388097

theorem tailTrace_2016651 : CollatzResearch.WordTrace tailWord_2016651 prefixEnd_2016651 1035511275370294577388097 := by
  unfold tailWord_2016651
  simp only [CollatzResearch.WordTrace]
  refine ⟨73553304617025318415505807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49035536411350212277003871 73553304617025318415505807)
  ·
    refine ⟨110329956925537977623258711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73553304617025318415505807 110329956925537977623258711)
    ·
      refine ⟨165494935388306966434888067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110329956925537977623258711 165494935388306966434888067)
      ·
        refine ⟨248242403082460449652332101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165494935388306966434888067 248242403082460449652332101)
        ·
          refine ⟨46545450577961334309812269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248242403082460449652332101 46545450577961334309812269)
          ·
            refine ⟨17454543966735500366179601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46545450577961334309812269 17454543966735500366179601)
            ·
              refine ⟨13090907975051625274634701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17454543966735500366179601 13090907975051625274634701)
              ·
                refine ⟨4909090490644359477988013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13090907975051625274634701 4909090490644359477988013)
                ·
                  refine ⟨1840908933991634804245505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4909090490644359477988013 1840908933991634804245505)
                  ·
                    refine ⟨1380681700493726103184129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1840908933991634804245505 1380681700493726103184129)
                    ·
                      refine ⟨1035511275370294577388097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1380681700493726103184129 1035511275370294577388097)
                      ·
                        rfl

theorem cell23_2016651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3, 2, 2].length) (baseStart_2016651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016651 prefixEnd_2016651 := by exact prefixLift 2016651
  have htrace : WordTrace (prefixWord ++ tailWord_2016651) baseStart_2016651 baseEnd_2016651 := by
    simpa [prefixWord, tailWord_2016651, baseEnd_2016651] using wordTrace_append hprefix tailTrace_2016651
  have hstable : (prefixWord ++ tailWord_2016651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016651).length < 2 ^ (prefixWord ++ tailWord_2016651).sum := by decide
  have hdescent : baseEnd_2016651 < baseStart_2016651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016684 : List Nat := [2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 3]
def baseStart_2016684 : Nat := 118140960795 + 2016684 * 2 ^ 59
def prefixEnd_2016684 : Nat := 4983230072969 + 3 ^ 40 * 2016684 * 2
def baseEnd_2016684 : Nat := 1035528220231892948275445

theorem tailTrace_2016684 : CollatzResearch.WordTrace tailWord_2016684 prefixEnd_2016684 1035528220231892948275445 := by
  unfold tailWord_2016684
  simp only [CollatzResearch.WordTrace]
  refine ⟨36777254112952882525728553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49036338817270510034304737 36777254112952882525728553)
  ·
    refine ⟨27582940584714661894296415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36777254112952882525728553 27582940584714661894296415)
    ·
      refine ⟨41374410877071992841444623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27582940584714661894296415 41374410877071992841444623)
      ·
        refine ⟨62061616315607989262166935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41374410877071992841444623 62061616315607989262166935)
        ·
          refine ⟨93092424473411983893250403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62061616315607989262166935 93092424473411983893250403)
          ·
            refine ⟨139638636710117975839875605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93092424473411983893250403 139638636710117975839875605)
            ·
              refine ⟨6545561095786780117494169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 139638636710117975839875605 6545561095786780117494169)
              ·
                refine ⟨4909170821840085088120627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6545561095786780117494169 4909170821840085088120627)
                ·
                  refine ⟨7363756232760127632180941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4909170821840085088120627 7363756232760127632180941)
                  ·
                    refine ⟨2761408587285047862067853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7363756232760127632180941 2761408587285047862067853)
                    ·
                      refine ⟨1035528220231892948275445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2761408587285047862067853 1035528220231892948275445)
                      ·
                        rfl

theorem cell23_2016684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 3].length) (baseStart_2016684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016684 prefixEnd_2016684 := by exact prefixLift 2016684
  have htrace : WordTrace (prefixWord ++ tailWord_2016684) baseStart_2016684 baseEnd_2016684 := by
    simpa [prefixWord, tailWord_2016684, baseEnd_2016684] using wordTrace_append hprefix tailTrace_2016684
  have hstable : (prefixWord ++ tailWord_2016684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016684).length < 2 ^ (prefixWord ++ tailWord_2016684).sum := by decide
  have hdescent : baseEnd_2016684 < baseStart_2016684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016685 : List Nat := [1, 5, 2, 2, 1, 3, 2, 1, 1, 1, 4]
def baseStart_2016685 : Nat := 118140960795 + 2016685 * 2 ^ 59
def prefixEnd_2016685 : Nat := 4983230072969 + 3 ^ 40 * 2016685 * 2
def baseEnd_2016685 : Nat := 1035528733712547444362941

theorem tailTrace_2016685 : CollatzResearch.WordTrace tailWord_2016685 prefixEnd_2016685 1035528733712547444362941 := by
  unfold tailWord_2016685
  simp only [CollatzResearch.WordTrace]
  refine ⟨73554544698902142222243509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49036363132601428148162339 73554544698902142222243509)
  ·
    refine ⟨6895738565522075833335329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73554544698902142222243509 6895738565522075833335329)
    ·
      refine ⟨5171803924141556875001497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6895738565522075833335329 5171803924141556875001497)
      ·
        refine ⟨3878852943106167656251123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5171803924141556875001497 3878852943106167656251123)
        ·
          refine ⟨5818279414659251484376685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3878852943106167656251123 5818279414659251484376685)
          ·
            refine ⟨2181854780497219306641257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5818279414659251484376685 2181854780497219306641257)
            ·
              refine ⟨1636391085372914479980943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2181854780497219306641257 1636391085372914479980943)
              ·
                refine ⟨2454586628059371719971415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1636391085372914479980943 2454586628059371719971415)
                ·
                  refine ⟨3681879942089057579957123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2454586628059371719971415 3681879942089057579957123)
                  ·
                    refine ⟨5522819913133586369935685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3681879942089057579957123 5522819913133586369935685)
                    ·
                      refine ⟨1035528733712547444362941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5522819913133586369935685 1035528733712547444362941)
                      ·
                        rfl

theorem cell23_2016685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_2016685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016685 prefixEnd_2016685 := by exact prefixLift 2016685
  have htrace : WordTrace (prefixWord ++ tailWord_2016685) baseStart_2016685 baseEnd_2016685 := by
    simpa [prefixWord, tailWord_2016685, baseEnd_2016685] using wordTrace_append hprefix tailTrace_2016685
  have hstable : (prefixWord ++ tailWord_2016685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016685).length < 2 ^ (prefixWord ++ tailWord_2016685).sum := by decide
  have hdescent : baseEnd_2016685 < baseStart_2016685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016701 : List Nat := [1, 4, 1, 2, 2, 1, 3, 1, 4, 1, 3]
def baseStart_2016701 : Nat := 118140960795 + 2016701 * 2 ^ 59
def prefixEnd_2016701 : Nat := 4983230072969 + 3 ^ 40 * 2016701 * 2
def baseEnd_2016701 : Nat := 1035536949403019381762867

theorem tailTrace_2016701 : CollatzResearch.WordTrace tailWord_2016701 prefixEnd_2016701 1035536949403019381762867 := by
  unfold tailWord_2016701
  simp only [CollatzResearch.WordTrace]
  refine ⟨73555128266844176954825957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49036752177896117969883971 73555128266844176954825957)
  ·
    refine ⟨13791586550033283179029867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73555128266844176954825957 13791586550033283179029867)
    ·
      refine ⟨20687379825049924768544801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13791586550033283179029867 20687379825049924768544801)
      ·
        refine ⟨15515534868787443576408601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20687379825049924768544801 15515534868787443576408601)
        ·
          refine ⟨11636651151590582682306451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15515534868787443576408601 11636651151590582682306451)
          ·
            refine ⟨17454976727385874023459677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11636651151590582682306451 17454976727385874023459677)
            ·
              refine ⟨6545616272769702758797379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17454976727385874023459677 6545616272769702758797379)
              ·
                refine ⟨9818424409154554138196069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6545616272769702758797379 9818424409154554138196069)
                ·
                  refine ⟨1840954576716478900911763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9818424409154554138196069 1840954576716478900911763)
                  ·
                    refine ⟨2761431865074718351367645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1840954576716478900911763 2761431865074718351367645)
                    ·
                      refine ⟨1035536949403019381762867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2761431865074718351367645 1035536949403019381762867)
                      ·
                        rfl

theorem cell23_2016701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_2016701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016701 prefixEnd_2016701 := by exact prefixLift 2016701
  have htrace : WordTrace (prefixWord ++ tailWord_2016701) baseStart_2016701 baseEnd_2016701 := by
    simpa [prefixWord, tailWord_2016701, baseEnd_2016701] using wordTrace_append hprefix tailTrace_2016701
  have hstable : (prefixWord ++ tailWord_2016701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016701).length < 2 ^ (prefixWord ++ tailWord_2016701).sum := by decide
  have hdescent : baseEnd_2016701 < baseStart_2016701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016707 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 4]
def baseStart_2016707 : Nat := 118140960795 + 2016707 * 2 ^ 59
def prefixEnd_2016707 : Nat := 4983230072969 + 3 ^ 40 * 2016707 * 2
def baseEnd_2016707 : Nat := 1035540030286946358287839

theorem tailTrace_2016707 : CollatzResearch.WordTrace tailWord_2016707 prefixEnd_2016707 1035540030286946358287839 := by
  unfold tailWord_2016707
  simp only [CollatzResearch.WordTrace]
  refine ⟨73555347104822439979544375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49036898069881626653029583 73555347104822439979544375)
  ·
    refine ⟨110333020657233659969316563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73555347104822439979544375 110333020657233659969316563)
    ·
      refine ⟨165499530985850489953974845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110333020657233659969316563 165499530985850489953974845)
      ·
        refine ⟨62062324119693933732740567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165499530985850489953974845 62062324119693933732740567)
        ·
          refine ⟨93093486179540900599110851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62062324119693933732740567 93093486179540900599110851)
          ·
            refine ⟨139640229269311350898666277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93093486179540900599110851 139640229269311350898666277)
            ·
              refine ⟨26182542987995878293499927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139640229269311350898666277 26182542987995878293499927)
              ·
                refine ⟨39273814481993817440249891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26182542987995878293499927 39273814481993817440249891)
                ·
                  refine ⟨58910721722990726160374837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39273814481993817440249891 58910721722990726160374837)
                  ·
                    refine ⟨5522880161530380577535141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58910721722990726160374837 5522880161530380577535141)
                    ·
                      refine ⟨1035540030286946358287839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5522880161530380577535141 1035540030286946358287839)
                      ·
                        rfl

theorem cell23_2016707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_2016707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016707 prefixEnd_2016707 := by exact prefixLift 2016707
  have htrace : WordTrace (prefixWord ++ tailWord_2016707) baseStart_2016707 baseEnd_2016707 := by
    simpa [prefixWord, tailWord_2016707, baseEnd_2016707] using wordTrace_append hprefix tailTrace_2016707
  have hstable : (prefixWord ++ tailWord_2016707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016707).length < 2 ^ (prefixWord ++ tailWord_2016707).sum := by decide
  have hdescent : baseEnd_2016707 < baseStart_2016707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016727 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 5]
def baseStart_2016727 : Nat := 118140960795 + 2016727 * 2 ^ 59
def prefixEnd_2016727 : Nat := 4983230072969 + 3 ^ 40 * 2016727 * 2
def baseEnd_2016727 : Nat := 1035550299900036280037747

theorem tailTrace_2016727 : CollatzResearch.WordTrace tailWord_2016727 prefixEnd_2016727 1035550299900036280037747 := by
  unfold tailWord_2016727
  simp only [CollatzResearch.WordTrace]
  refine ⟨73556076564749983395272435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49037384376499988930181623 73556076564749983395272435)
  ·
    refine ⟨110334114847124975092908653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73556076564749983395272435 110334114847124975092908653)
    ·
      refine ⟨41375293067671865659840745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110334114847124975092908653 41375293067671865659840745)
      ·
        refine ⟨31031469800753899244880559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41375293067671865659840745 31031469800753899244880559)
        ·
          refine ⟨46547204701130848867320839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31031469800753899244880559 46547204701130848867320839)
          ·
            refine ⟨69820807051696273300981259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46547204701130848867320839 69820807051696273300981259)
            ·
              refine ⟨104731210577544409951471889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69820807051696273300981259 104731210577544409951471889)
              ·
                refine ⟨78548407933158307463603917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104731210577544409951471889 78548407933158307463603917)
                ·
                  refine ⟨29455652974934365298851469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78548407933158307463603917 29455652974934365298851469)
                  ·
                    refine ⟨11045869865600386987069301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29455652974934365298851469 11045869865600386987069301)
                    ·
                      refine ⟨1035550299900036280037747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11045869865600386987069301 1035550299900036280037747)
                      ·
                        rfl

theorem cell23_2016727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_2016727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016727 prefixEnd_2016727 := by exact prefixLift 2016727
  have htrace : WordTrace (prefixWord ++ tailWord_2016727) baseStart_2016727 baseEnd_2016727 := by
    simpa [prefixWord, tailWord_2016727, baseEnd_2016727] using wordTrace_append hprefix tailTrace_2016727
  have hstable : (prefixWord ++ tailWord_2016727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016727).length < 2 ^ (prefixWord ++ tailWord_2016727).sum := by decide
  have hdescent : baseEnd_2016727 < baseStart_2016727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016744 : List Nat := [2, 1, 4, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_2016744 : Nat := 118140960795 + 2016744 * 2 ^ 59
def prefixEnd_2016744 : Nat := 4983230072969 + 3 ^ 40 * 2016744 * 2
def baseEnd_2016744 : Nat := 1035559029071162713525169

theorem tailTrace_2016744 : CollatzResearch.WordTrace tailWord_2016744 prefixEnd_2016744 1035559029071162713525169 := by
  unfold tailWord_2016744
  simp only [CollatzResearch.WordTrace]
  refine ⟨36778348302844197649320643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49037797737125596865760857 36778348302844197649320643)
  ·
    refine ⟨55167522454266296473980965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36778348302844197649320643 55167522454266296473980965)
    ·
      refine ⟨10343910460174930588871431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55167522454266296473980965 10343910460174930588871431)
      ·
        refine ⟨15515865690262395883307147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10343910460174930588871431 15515865690262395883307147)
        ·
          refine ⟨23273798535393593824960721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15515865690262395883307147 23273798535393593824960721)
          ·
            refine ⟨17455348901545195368720541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23273798535393593824960721 17455348901545195368720541)
            ·
              refine ⟨6545755838079448263270203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17455348901545195368720541 6545755838079448263270203)
              ·
                refine ⟨9818633757119172394905305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6545755838079448263270203 9818633757119172394905305)
                ·
                  refine ⟨7363975317839379296178979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9818633757119172394905305 7363975317839379296178979)
                  ·
                    refine ⟨11045962976759068944268469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7363975317839379296178979 11045962976759068944268469)
                    ·
                      refine ⟨1035559029071162713525169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11045962976759068944268469 1035559029071162713525169)
                      ·
                        rfl

theorem cell23_2016744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_2016744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016744 prefixEnd_2016744 := by exact prefixLift 2016744
  have htrace : WordTrace (prefixWord ++ tailWord_2016744) baseStart_2016744 baseEnd_2016744 := by
    simpa [prefixWord, tailWord_2016744, baseEnd_2016744] using wordTrace_append hprefix tailTrace_2016744
  have hstable : (prefixWord ++ tailWord_2016744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016744).length < 2 ^ (prefixWord ++ tailWord_2016744).sum := by decide
  have hdescent : baseEnd_2016744 < baseStart_2016744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016764 : List Nat := [2, 2, 2, 1, 2, 1, 5, 1, 7]
def baseStart_2016764 : Nat := 118140960795 + 2016764 * 2 ^ 59
def prefixEnd_2016764 : Nat := 4983230072969 + 3 ^ 40 * 2016764 * 2
def baseEnd_2016764 : Nat := 115063255409361403919453

theorem tailTrace_2016764 : CollatzResearch.WordTrace tailWord_2016764 prefixEnd_2016764 115063255409361403919453 := by
  unfold tailWord_2016764
  simp only [CollatzResearch.WordTrace]
  refine ⟨36778713032807969357184673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49038284043743959142912897 36778713032807969357184673)
  ·
    refine ⟨27584034774605977017888505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36778713032807969357184673 27584034774605977017888505)
    ·
      refine ⟨20688026080954482763416379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27584034774605977017888505 20688026080954482763416379)
      ·
        refine ⟨31032039121431724145124569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20688026080954482763416379 31032039121431724145124569)
        ·
          refine ⟨23274029341073793108843427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31032039121431724145124569 23274029341073793108843427)
          ·
            refine ⟨34911044011610689663265141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23274029341073793108843427 34911044011610689663265141)
            ·
              refine ⟨3272910376088502155931107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34911044011610689663265141 3272910376088502155931107)
              ·
                refine ⟨4909365564132753233896661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3272910376088502155931107 4909365564132753233896661)
                ·
                  refine ⟨115063255409361403919453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4909365564132753233896661 115063255409361403919453)
                  ·
                    rfl

theorem cell23_2016764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 7].length) (baseStart_2016764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016764 prefixEnd_2016764 := by exact prefixLift 2016764
  have htrace : WordTrace (prefixWord ++ tailWord_2016764) baseStart_2016764 baseEnd_2016764 := by
    simpa [prefixWord, tailWord_2016764, baseEnd_2016764] using wordTrace_append hprefix tailTrace_2016764
  have hstable : (prefixWord ++ tailWord_2016764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016764).length < 2 ^ (prefixWord ++ tailWord_2016764).sum := by decide
  have hdescent : baseEnd_2016764 < baseStart_2016764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016767 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 8]
def baseStart_2016767 : Nat := 118140960795 + 2016767 * 2 ^ 59
def prefixEnd_2016767 : Nat := 4983230072969 + 3 ^ 40 * 2016767 * 2
def baseEnd_2016767 : Nat := 1035570839126216123537563

theorem tailTrace_2016767 : CollatzResearch.WordTrace tailWord_2016767 prefixEnd_2016767 1035570839126216123537563 := by
  unfold tailWord_2016767
  simp only [CollatzResearch.WordTrace]
  refine ⟨73557535484605070226728555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49038356989736713484485703 73557535484605070226728555)
  ·
    refine ⟨110336303226907605340092833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73557535484605070226728555 110336303226907605340092833)
    ·
      refine ⟨82752227420180704005069625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110336303226907605340092833 82752227420180704005069625)
      ·
        refine ⟨62064170565135528003802219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82752227420180704005069625 62064170565135528003802219)
        ·
          refine ⟨93096255847703292005703329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62064170565135528003802219 93096255847703292005703329)
          ·
            refine ⟨69822191885777469004277497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93096255847703292005703329 69822191885777469004277497)
            ·
              refine ⟨52366643914333101753208123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69822191885777469004277497 52366643914333101753208123)
              ·
                refine ⟨78549965871499652629812185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52366643914333101753208123 78549965871499652629812185)
                ·
                  refine ⟨58912474403624739472359139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78549965871499652629812185 58912474403624739472359139)
                  ·
                    refine ⟨88368711605437109208538709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58912474403624739472359139 88368711605437109208538709)
                    ·
                      refine ⟨1035570839126216123537563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 88368711605437109208538709 1035570839126216123537563)
                      ·
                        rfl

theorem cell23_2016767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_2016767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016767 prefixEnd_2016767 := by exact prefixLift 2016767
  have htrace : WordTrace (prefixWord ++ tailWord_2016767) baseStart_2016767 baseEnd_2016767 := by
    simpa [prefixWord, tailWord_2016767, baseEnd_2016767] using wordTrace_append hprefix tailTrace_2016767
  have hstable : (prefixWord ++ tailWord_2016767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016767).length < 2 ^ (prefixWord ++ tailWord_2016767).sum := by decide
  have hdescent : baseEnd_2016767 < baseStart_2016767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016775 : List Nat := [1, 1, 4, 3, 2, 2, 1, 3, 2, 2, 2]
def baseStart_2016775 : Nat := 118140960795 + 2016775 * 2 ^ 59
def prefixEnd_2016775 : Nat := 4983230072969 + 3 ^ 40 * 2016775 * 2
def baseEnd_2016775 : Nat := 1035574946971452092237527

theorem tailTrace_2016775 : CollatzResearch.WordTrace tailWord_2016775 prefixEnd_2016775 1035574946971452092237527 := by
  unfold tailWord_2016775
  simp only [CollatzResearch.WordTrace]
  refine ⟨73557827268576087593019779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49038551512384058395346519 73557827268576087593019779)
  ·
    refine ⟨110336740902864131389529669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73557827268576087593019779 110336740902864131389529669)
    ·
      refine ⟨20688138919287024635536813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110336740902864131389529669 20688138919287024635536813)
      ·
        refine ⟨7758052094732634238326305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20688138919287024635536813 7758052094732634238326305)
        ·
          refine ⟨5818539071049475678744729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7758052094732634238326305 5818539071049475678744729)
          ·
            refine ⟨4363904303287106759058547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5818539071049475678744729 4363904303287106759058547)
            ·
              refine ⟨6545856454930660138587821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4363904303287106759058547 6545856454930660138587821)
              ·
                refine ⟨2454696170598997551970433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6545856454930660138587821 2454696170598997551970433)
                ·
                  refine ⟨1841022127949248163977825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2454696170598997551970433 1841022127949248163977825)
                  ·
                    refine ⟨1380766595961936122983369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1841022127949248163977825 1380766595961936122983369)
                    ·
                      refine ⟨1035574946971452092237527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1380766595961936122983369 1035574946971452092237527)
                      ·
                        rfl

theorem cell23_2016775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_2016775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016775 prefixEnd_2016775 := by exact prefixLift 2016775
  have htrace : WordTrace (prefixWord ++ tailWord_2016775) baseStart_2016775 baseEnd_2016775 := by
    simpa [prefixWord, tailWord_2016775, baseEnd_2016775] using wordTrace_append hprefix tailTrace_2016775
  have hstable : (prefixWord ++ tailWord_2016775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016775).length < 2 ^ (prefixWord ++ tailWord_2016775).sum := by decide
  have hdescent : baseEnd_2016775 < baseStart_2016775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016831 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 1, 6, 2]
def baseStart_2016831 : Nat := 118140960795 + 2016831 * 2 ^ 59
def prefixEnd_2016831 : Nat := 4983230072969 + 3 ^ 40 * 2016831 * 2
def baseEnd_2016831 : Nat := 1035603701888103873137269

theorem tailTrace_2016831 : CollatzResearch.WordTrace tailWord_2016831 prefixEnd_2016831 1035603701888103873137269 := by
  unfold tailWord_2016831
  simp only [CollatzResearch.WordTrace]
  refine ⟨73559869756373209157058347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49039913170915472771372231 73559869756373209157058347)
  ·
    refine ⟨110339804634559813735587521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73559869756373209157058347 110339804634559813735587521)
    ·
      refine ⟨82754853475919860301690641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110339804634559813735587521 82754853475919860301690641)
      ·
        refine ⟨62066140106939895226267981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82754853475919860301690641 62066140106939895226267981)
        ·
          refine ⟨23274802540102460709850493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62066140106939895226267981 23274802540102460709850493)
          ·
            refine ⟨8728050952538422766193935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23274802540102460709850493 8728050952538422766193935)
            ·
              refine ⟨13092076428807634149290903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8728050952538422766193935 13092076428807634149290903)
              ·
                refine ⟨19638114643211451223936355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13092076428807634149290903 19638114643211451223936355)
                ·
                  refine ⟨29457171964817176835904533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19638114643211451223936355 29457171964817176835904533)
                  ·
                    refine ⟨1380804935850805164183025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29457171964817176835904533 1380804935850805164183025)
                    ·
                      refine ⟨1035603701888103873137269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1380804935850805164183025 1035603701888103873137269)
                      ·
                        rfl

theorem cell23_2016831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 6, 2].length) (baseStart_2016831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016831 prefixEnd_2016831 := by exact prefixLift 2016831
  have htrace : WordTrace (prefixWord ++ tailWord_2016831) baseStart_2016831 baseEnd_2016831 := by
    simpa [prefixWord, tailWord_2016831, baseEnd_2016831] using wordTrace_append hprefix tailTrace_2016831
  have hstable : (prefixWord ++ tailWord_2016831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016831).length < 2 ^ (prefixWord ++ tailWord_2016831).sum := by decide
  have hdescent : baseEnd_2016831 < baseStart_2016831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016845 : List Nat := [1, 6, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_2016845 : Nat := 118140960795 + 2016845 * 2 ^ 59
def prefixEnd_2016845 : Nat := 4983230072969 + 3 ^ 40 * 2016845 * 2
def baseEnd_2016845 : Nat := 345203630205755606120735

theorem tailTrace_2016845 : CollatzResearch.WordTrace tailWord_2016845 prefixEnd_2016845 345203630205755606120735 := by
  unfold tailWord_2016845
  simp only [CollatzResearch.WordTrace]
  refine ⟨73560380378322489548067989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49040253585548326365378659 73560380378322489548067989)
  ·
    refine ⟨3448142830233866697565687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73560380378322489548067989 3448142830233866697565687)
    ·
      refine ⟨5172214245350800046348531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3448142830233866697565687 5172214245350800046348531)
      ·
        refine ⟨7758321368026200069522797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5172214245350800046348531 7758321368026200069522797)
        ·
          refine ⟨2909370513009825026071049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7758321368026200069522797 2909370513009825026071049)
          ·
            refine ⟨2182027884757368769553287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2909370513009825026071049 2182027884757368769553287)
            ·
              refine ⟨3273041827136053154329931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2182027884757368769553287 3273041827136053154329931)
              ·
                refine ⟨4909562740704079731494897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3273041827136053154329931 4909562740704079731494897)
                ·
                  refine ⟨3682172055528059798621173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4909562740704079731494897 3682172055528059798621173)
                  ·
                    refine ⟨345203630205755606120735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3682172055528059798621173 345203630205755606120735)
                    ·
                      rfl

theorem cell23_2016845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_2016845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016845 prefixEnd_2016845 := by exact prefixLift 2016845
  have htrace : WordTrace (prefixWord ++ tailWord_2016845) baseStart_2016845 baseEnd_2016845 := by
    simpa [prefixWord, tailWord_2016845, baseEnd_2016845] using wordTrace_append hprefix tailTrace_2016845
  have hstable : (prefixWord ++ tailWord_2016845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016845).length < 2 ^ (prefixWord ++ tailWord_2016845).sum := by decide
  have hdescent : baseEnd_2016845 < baseStart_2016845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016871 : List Nat := [1, 1, 5, 1, 1, 1, 5, 2, 6]
def baseStart_2016871 : Nat := 118140960795 + 2016871 * 2 ^ 59
def prefixEnd_2016871 : Nat := 4983230072969 + 3 ^ 40 * 2016871 * 2
def baseEnd_2016871 : Nat := 115069360123809301848565

theorem tailTrace_2016871 : CollatzResearch.WordTrace tailWord_2016871 prefixEnd_2016871 115069360123809301848565 := by
  unfold tailWord_2016871
  simp only [CollatzResearch.WordTrace]
  refine ⟨73561328676228295988514467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49040885784152197325676311 73561328676228295988514467)
  ·
    refine ⟨110341993014342443982771701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73561328676228295988514467 110341993014342443982771701)
    ·
      refine ⟨10344561845094604123384847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110341993014342443982771701 10344561845094604123384847)
      ·
        refine ⟨15516842767641906185077271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10344561845094604123384847 15516842767641906185077271)
        ·
          refine ⟨23275264151462859277615907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15516842767641906185077271 23275264151462859277615907)
          ·
            refine ⟨34912896227194288916423861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23275264151462859277615907 34912896227194288916423861)
            ·
              refine ⟨3273084021299464585914737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34912896227194288916423861 3273084021299464585914737)
              ·
                refine ⟨2454813015974598439436053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3273084021299464585914737 2454813015974598439436053)
                ·
                  refine ⟨115069360123809301848565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2454813015974598439436053 115069360123809301848565)
                  ·
                    rfl

theorem cell23_2016871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 6].length) (baseStart_2016871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016871 prefixEnd_2016871 := by exact prefixLift 2016871
  have htrace : WordTrace (prefixWord ++ tailWord_2016871) baseStart_2016871 baseEnd_2016871 := by
    simpa [prefixWord, tailWord_2016871, baseEnd_2016871] using wordTrace_append hprefix tailTrace_2016871
  have hstable : (prefixWord ++ tailWord_2016871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016871).length < 2 ^ (prefixWord ++ tailWord_2016871).sum := by decide
  have hdescent : baseEnd_2016871 < baseStart_2016871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016891 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 3, 5, 2]
def baseStart_2016891 : Nat := 118140960795 + 2016891 * 2 ^ 59
def prefixEnd_2016891 : Nat := 4983230072969 + 3 ^ 40 * 2016891 * 2
def baseEnd_2016891 : Nat := 1035634510727373638386993

theorem tailTrace_2016891 : CollatzResearch.WordTrace tailWord_2016891 prefixEnd_2016891 1035634510727373638386993 := by
  unfold tailWord_2016891
  simp only [CollatzResearch.WordTrace]
  refine ⟨73562058136155839404242527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49041372090770559602828351 73562058136155839404242527)
  ·
    refine ⟨110343087204233759106363791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73562058136155839404242527 110343087204233759106363791)
    ·
      refine ⟨165514630806350638659545687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110343087204233759106363791 165514630806350638659545687)
      ·
        refine ⟨248271946209525957989318531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165514630806350638659545687 248271946209525957989318531)
        ·
          refine ⟨372407919314288936983977797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248271946209525957989318531 372407919314288936983977797)
          ·
            refine ⟨69826484871429175684495837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 372407919314288936983977797 69826484871429175684495837)
            ·
              refine ⟨26184931826785940881685939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69826484871429175684495837 26184931826785940881685939)
              ·
                refine ⟨39277397740178911322528909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26184931826785940881685939 39277397740178911322528909)
                ·
                  refine ⟨14729024152567091745948341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39277397740178911322528909 14729024152567091745948341)
                  ·
                    refine ⟨1380846014303164851182657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14729024152567091745948341 1380846014303164851182657)
                    ·
                      refine ⟨1035634510727373638386993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1380846014303164851182657 1035634510727373638386993)
                      ·
                        rfl

theorem cell23_2016891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 5, 2].length) (baseStart_2016891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016891 prefixEnd_2016891 := by exact prefixLift 2016891
  have htrace : WordTrace (prefixWord ++ tailWord_2016891) baseStart_2016891 baseEnd_2016891 := by
    simpa [prefixWord, tailWord_2016891, baseEnd_2016891] using wordTrace_append hprefix tailTrace_2016891
  have hstable : (prefixWord ++ tailWord_2016891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016891).length < 2 ^ (prefixWord ++ tailWord_2016891).sum := by decide
  have hdescent : baseEnd_2016891 < baseStart_2016891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016908 : List Nat := [2, 2, 1, 2, 1, 1, 4, 3, 2, 3, 2]
def baseStart_2016908 : Nat := 118140960795 + 2016908 * 2 ^ 59
def prefixEnd_2016908 : Nat := 4983230072969 + 3 ^ 40 * 2016908 * 2
def baseEnd_2016908 : Nat := 1035643239898500071874415

theorem tailTrace_2016908 : CollatzResearch.WordTrace tailWord_2016908 prefixEnd_2016908 1035643239898500071874415 := by
  unfold tailWord_2016908
  simp only [CollatzResearch.WordTrace]
  refine ⟨36781339088547125653805689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49041785451396167538407585 36781339088547125653805689)
  ·
    refine ⟨27586004316410344240354267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36781339088547125653805689 27586004316410344240354267)
    ·
      refine ⟨41379006474615516360531401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27586004316410344240354267 41379006474615516360531401)
      ·
        refine ⟨31034254855961637270398551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41379006474615516360531401 31034254855961637270398551)
        ·
          refine ⟨46551382283942455905597827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31034254855961637270398551 46551382283942455905597827)
          ·
            refine ⟨69827073425913683858396741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46551382283942455905597827 69827073425913683858396741)
            ·
              refine ⟨13092576267358815723449389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69827073425913683858396741 13092576267358815723449389)
              ·
                refine ⟨4909716100259555896293521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13092576267358815723449389 4909716100259555896293521)
                ·
                  refine ⟨3682287075194666922220141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4909716100259555896293521 3682287075194666922220141)
                  ·
                    refine ⟨1380857653198000095832553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3682287075194666922220141 1380857653198000095832553)
                    ·
                      refine ⟨1035643239898500071874415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1380857653198000095832553 1035643239898500071874415)
                      ·
                        rfl

theorem cell23_2016908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 2, 3, 2].length) (baseStart_2016908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016908 prefixEnd_2016908 := by exact prefixLift 2016908
  have htrace : WordTrace (prefixWord ++ tailWord_2016908) baseStart_2016908 baseEnd_2016908 := by
    simpa [prefixWord, tailWord_2016908, baseEnd_2016908] using wordTrace_append hprefix tailTrace_2016908
  have hstable : (prefixWord ++ tailWord_2016908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016908).length < 2 ^ (prefixWord ++ tailWord_2016908).sum := by decide
  have hdescent : baseEnd_2016908 < baseStart_2016908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016931 : List Nat := [1, 1, 1, 4, 1, 1, 3, 3, 4, 4]
def baseStart_2016931 : Nat := 118140960795 + 2016931 * 2 ^ 59
def prefixEnd_2016931 : Nat := 4983230072969 + 3 ^ 40 * 2016931 * 2
def baseEnd_2016931 : Nat := 345218349984517827295603

theorem tailTrace_2016931 : CollatzResearch.WordTrace tailWord_2016931 prefixEnd_2016931 345218349984517827295603 := by
  unfold tailWord_2016931
  simp only [CollatzResearch.WordTrace]
  refine ⟨73563517056010926235698647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49042344704007284157132431 73563517056010926235698647)
  ·
    refine ⟨110345275584016389353547971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73563517056010926235698647 110345275584016389353547971)
    ·
      refine ⟨165517913376024584030321957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110345275584016389353547971 165517913376024584030321957)
      ·
        refine ⟨31034608758004609505685367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165517913376024584030321957 31034608758004609505685367)
        ·
          refine ⟨46551913137006914258528051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31034608758004609505685367 46551913137006914258528051)
          ·
            refine ⟨69827869705510371387792077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46551913137006914258528051 69827869705510371387792077)
            ·
              refine ⟨26185451139566389270422029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69827869705510371387792077 26185451139566389270422029)
              ·
                refine ⟨9819544177337395976408261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26185451139566389270422029 9819544177337395976408261)
                ·
                  refine ⟨1841164533250761745576549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9819544177337395976408261 1841164533250761745576549)
                  ·
                    refine ⟨345218349984517827295603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1841164533250761745576549 345218349984517827295603)
                    ·
                      rfl

theorem cell23_2016931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 4].length) (baseStart_2016931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016931 prefixEnd_2016931 := by exact prefixLift 2016931
  have htrace : WordTrace (prefixWord ++ tailWord_2016931) baseStart_2016931 baseEnd_2016931 := by
    simpa [prefixWord, tailWord_2016931, baseEnd_2016931] using wordTrace_append hprefix tailTrace_2016931
  have hstable : (prefixWord ++ tailWord_2016931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016931).length < 2 ^ (prefixWord ++ tailWord_2016931).sum := by decide
  have hdescent : baseEnd_2016931 < baseStart_2016931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016944 : List Nat := [2, 1, 1, 1, 2, 1, 5, 10]
def baseStart_2016944 : Nat := 118140960795 + 2016944 * 2 ^ 59
def prefixEnd_2016944 : Nat := 4983230072969 + 3 ^ 40 * 2016944 * 2
def baseEnd_2016944 : Nat := 38357841674150441889787

theorem tailTrace_2016944 : CollatzResearch.WordTrace tailWord_2016944 prefixEnd_2016944 38357841674150441889787 := by
  unfold tailWord_2016944
  simp only [CollatzResearch.WordTrace]
  refine ⟨36781995602481914727960943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49042660803309219637281257 36781995602481914727960943)
  ·
    refine ⟨55172993403722872091941415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36781995602481914727960943 55172993403722872091941415)
    ·
      refine ⟨82759490105584308137912123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55172993403722872091941415 82759490105584308137912123)
      ·
        refine ⟨124139235158376462206868185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82759490105584308137912123 124139235158376462206868185)
        ·
          refine ⟨93104426368782346655151139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124139235158376462206868185 93104426368782346655151139)
          ·
            refine ⟨139656639553173519982726709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93104426368782346655151139 139656639553173519982726709)
            ·
              refine ⟨13092809958110017498380629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139656639553173519982726709 13092809958110017498380629)
              ·
                refine ⟨38357841674150441889787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13092809958110017498380629 38357841674150441889787)
                ·
                  rfl

theorem cell23_2016944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 10].length) (baseStart_2016944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016944 prefixEnd_2016944 := by exact prefixLift 2016944
  have htrace : WordTrace (prefixWord ++ tailWord_2016944) baseStart_2016944 baseEnd_2016944 := by
    simpa [prefixWord, tailWord_2016944, baseEnd_2016944] using wordTrace_append hprefix tailTrace_2016944
  have hstable : (prefixWord ++ tailWord_2016944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016944).length < 2 ^ (prefixWord ++ tailWord_2016944).sum := by decide
  have hdescent : baseEnd_2016944 < baseStart_2016944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016951 : List Nat := [1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 6]
def baseStart_2016951 : Nat := 118140960795 + 2016951 * 2 ^ 59
def prefixEnd_2016951 : Nat := 4983230072969 + 3 ^ 40 * 2016951 * 2
def baseEnd_2016951 : Nat := 1035665319566643403636717

theorem tailTrace_2016951 : CollatzResearch.WordTrace tailWord_2016951 prefixEnd_2016951 1035665319566643403636717 := by
  unfold tailWord_2016951
  simp only [CollatzResearch.WordTrace]
  refine ⟨73564246515938469651426707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49042831010625646434284471 73564246515938469651426707)
  ·
    refine ⟨110346369773907704477140061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73564246515938469651426707 110346369773907704477140061)
    ·
      refine ⟨41379888665215389178927523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110346369773907704477140061 41379888665215389178927523)
      ·
        refine ⟨62069832997823083768391285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41379888665215389178927523 62069832997823083768391285)
        ·
          refine ⟨5819046843545914103286683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62069832997823083768391285 5819046843545914103286683)
          ·
            refine ⟨8728570265318871154930025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5819046843545914103286683 8728570265318871154930025)
            ·
              refine ⟨6546427698989153366197519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8728570265318871154930025 6546427698989153366197519)
              ·
                refine ⟨9819641548483730049296279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6546427698989153366197519 9819641548483730049296279)
                ·
                  refine ⟨14729462322725595073944419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9819641548483730049296279 14729462322725595073944419)
                  ·
                    refine ⟨22094193484088392610916629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14729462322725595073944419 22094193484088392610916629)
                    ·
                      refine ⟨1035665319566643403636717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22094193484088392610916629 1035665319566643403636717)
                      ·
                        rfl

theorem cell23_2016951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_2016951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016951 prefixEnd_2016951 := by exact prefixLift 2016951
  have htrace : WordTrace (prefixWord ++ tailWord_2016951) baseStart_2016951 baseEnd_2016951 := by
    simpa [prefixWord, tailWord_2016951, baseEnd_2016951] using wordTrace_append hprefix tailTrace_2016951
  have hstable : (prefixWord ++ tailWord_2016951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016951).length < 2 ^ (prefixWord ++ tailWord_2016951).sum := by decide
  have hdescent : baseEnd_2016951 < baseStart_2016951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016972 : List Nat := [2, 2, 1, 5, 2, 1, 3, 1, 1, 1, 4]
def baseStart_2016972 : Nat := 118140960795 + 2016972 * 2 ^ 59
def prefixEnd_2016972 : Nat := 4983230072969 + 3 ^ 40 * 2016972 * 2
def baseEnd_2016972 : Nat := 1035676102660387821474121

theorem tailTrace_2016972 : CollatzResearch.WordTrace tailWord_2016972 prefixEnd_2016972 1035676102660387821474121 := by
  unfold tailWord_2016972
  simp only [CollatzResearch.WordTrace]
  refine ⟨36782506224431195118970585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49043341632574926825294113 36782506224431195118970585)
  ·
    refine ⟨27586879668323396339227939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36782506224431195118970585 27586879668323396339227939)
    ·
      refine ⟨41380319502485094508841909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27586879668323396339227939 41380319502485094508841909)
      ·
        refine ⟨3879404953357977610203929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41380319502485094508841909 3879404953357977610203929)
        ·
          refine ⟨2909553715018483207652947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3879404953357977610203929 2909553715018483207652947)
          ·
            refine ⟨4364330572527724811479421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2909553715018483207652947 4364330572527724811479421)
            ·
              refine ⟨1636623964697896804304783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4364330572527724811479421 1636623964697896804304783)
              ·
                refine ⟨2454935947046845206457175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1636623964697896804304783 2454935947046845206457175)
                ·
                  refine ⟨3682403920570267809685763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2454935947046845206457175 3682403920570267809685763)
                  ·
                    refine ⟨5523605880855401714528645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3682403920570267809685763 5523605880855401714528645)
                    ·
                      refine ⟨1035676102660387821474121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5523605880855401714528645 1035676102660387821474121)
                      ·
                        rfl

theorem cell23_2016972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_2016972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016972 prefixEnd_2016972 := by exact prefixLift 2016972
  have htrace : WordTrace (prefixWord ++ tailWord_2016972) baseStart_2016972 baseEnd_2016972 := by
    simpa [prefixWord, tailWord_2016972, baseEnd_2016972] using wordTrace_append hprefix tailTrace_2016972
  have hstable : (prefixWord ++ tailWord_2016972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016972).length < 2 ^ (prefixWord ++ tailWord_2016972).sum := by decide
  have hdescent : baseEnd_2016972 < baseStart_2016972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016995 : List Nat := [1, 1, 1, 7, 3, 1, 1, 8]
def baseStart_2016995 : Nat := 118140960795 + 2016995 * 2 ^ 59
def prefixEnd_2016995 : Nat := 4983230072969 + 3 ^ 40 * 2016995 * 2
def baseEnd_2016995 : Nat := 38358811582053378943945

theorem tailTrace_2016995 : CollatzResearch.WordTrace tailWord_2016995 prefixEnd_2016995 38358811582053378943945 := by
  unfold tailWord_2016995
  simp only [CollatzResearch.WordTrace]
  refine ⟨73565851327779065166028439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49043900885186043444018959 73565851327779065166028439)
  ·
    refine ⟨110348776991668597749042659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73565851327779065166028439 110348776991668597749042659)
    ·
      refine ⟨165523165487502896623563989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110348776991668597749042659 165523165487502896623563989)
      ·
        refine ⟨3879449191113349139614781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 165523165487502896623563989 3879449191113349139614781)
        ·
          refine ⟨1454793446667505927355543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3879449191113349139614781 1454793446667505927355543)
          ·
            refine ⟨2182190170001258891033315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1454793446667505927355543 2182190170001258891033315)
            ·
              refine ⟨3273285255001888336549973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2182190170001258891033315 3273285255001888336549973)
              ·
                refine ⟨38358811582053378943945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3273285255001888336549973 38358811582053378943945)
                ·
                  rfl

theorem cell23_2016995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 8].length) (baseStart_2016995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2016995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2016995 prefixEnd_2016995 := by exact prefixLift 2016995
  have htrace : WordTrace (prefixWord ++ tailWord_2016995) baseStart_2016995 baseEnd_2016995 := by
    simpa [prefixWord, tailWord_2016995, baseEnd_2016995] using wordTrace_append hprefix tailTrace_2016995
  have hstable : (prefixWord ++ tailWord_2016995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016995).length < 2 ^ (prefixWord ++ tailWord_2016995).sum := by decide
  have hdescent : baseEnd_2016995 < baseStart_2016995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017005 : List Nat := [1, 5, 1, 2, 1, 3, 2, 1, 1, 3, 3]
def baseStart_2017005 : Nat := 118140960795 + 2017005 * 2 ^ 59
def prefixEnd_2017005 : Nat := 4983230072969 + 3 ^ 40 * 2017005 * 2
def baseEnd_2017005 : Nat := 1035693047521986192361469

theorem tailTrace_2017005 : CollatzResearch.WordTrace tailWord_2017005 prefixEnd_2017005 1035693047521986192361469 := by
  unfold tailWord_2017005
  simp only [CollatzResearch.WordTrace]
  refine ⟨73566216057742836873892469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49044144038495224582594979 73566216057742836873892469)
  ·
    refine ⟨6896832755413390956927419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73566216057742836873892469 6896832755413390956927419)
    ·
      refine ⟨10345249133120086435391129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6896832755413390956927419 10345249133120086435391129)
      ·
        refine ⟨7758936849840064826543347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10345249133120086435391129 7758936849840064826543347)
        ·
          refine ⟨11638405274760097239815021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7758936849840064826543347 11638405274760097239815021)
          ·
            refine ⟨4364401978035036464930633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11638405274760097239815021 4364401978035036464930633)
            ·
              refine ⟨3273301483526277348697975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4364401978035036464930633 3273301483526277348697975)
              ·
                refine ⟨4909952225289416023046963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3273301483526277348697975 4909952225289416023046963)
                ·
                  refine ⟨7364928337934124034570445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4909952225289416023046963 7364928337934124034570445)
                  ·
                    refine ⟨2761848126725296512963917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7364928337934124034570445 2761848126725296512963917)
                    ·
                      refine ⟨1035693047521986192361469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2761848126725296512963917 1035693047521986192361469)
                      ·
                        rfl

theorem cell23_2017005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_2017005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017005 prefixEnd_2017005 := by exact prefixLift 2017005
  have htrace : WordTrace (prefixWord ++ tailWord_2017005) baseStart_2017005 baseEnd_2017005 := by
    simpa [prefixWord, tailWord_2017005, baseEnd_2017005] using wordTrace_append hprefix tailTrace_2017005
  have hstable : (prefixWord ++ tailWord_2017005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017005).length < 2 ^ (prefixWord ++ tailWord_2017005).sum := by decide
  have hdescent : baseEnd_2017005 < baseStart_2017005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017012 : List Nat := [2, 6, 1, 1, 1, 2, 3, 7]
def baseStart_2017012 : Nat := 118140960795 + 2017012 * 2 ^ 59
def prefixEnd_2017012 : Nat := 4983230072969 + 3 ^ 40 * 2017012 * 2
def baseEnd_2017012 : Nat := 38359134884687691295331

theorem tailTrace_2017012 : CollatzResearch.WordTrace tailWord_2017012 prefixEnd_2017012 38359134884687691295331 := by
  unfold tailWord_2017012
  simp only [CollatzResearch.WordTrace]
  refine ⟨36783235684358738534698645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49044314245811651379598193 36783235684358738534698645)
  ·
    refine ⟨1724214172704315868813999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36783235684358738534698645 1724214172704315868813999)
    ·
      refine ⟨2586321259056473803220999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1724214172704315868813999 2586321259056473803220999)
      ·
        refine ⟨3879481888584710704831499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2586321259056473803220999 3879481888584710704831499)
        ·
          refine ⟨5819222832877066057247249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3879481888584710704831499 5819222832877066057247249)
          ·
            refine ⟨4364417124657799542935437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5819222832877066057247249 4364417124657799542935437)
            ·
              refine ⟨1636656421746674828600789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4364417124657799542935437 1636656421746674828600789)
              ·
                refine ⟨38359134884687691295331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1636656421746674828600789 38359134884687691295331)
                ·
                  rfl

theorem cell23_2017012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 7].length) (baseStart_2017012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017012 prefixEnd_2017012 := by exact prefixLift 2017012
  have htrace : WordTrace (prefixWord ++ tailWord_2017012) baseStart_2017012 baseEnd_2017012 := by
    simpa [prefixWord, tailWord_2017012, baseEnd_2017012] using wordTrace_append hprefix tailTrace_2017012
  have hstable : (prefixWord ++ tailWord_2017012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017012).length < 2 ^ (prefixWord ++ tailWord_2017012).sum := by decide
  have hdescent : baseEnd_2017012 < baseStart_2017012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017058 : List Nat := [3, 3, 1, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_2017058 : Nat := 118140960795 + 2017058 * 2 ^ 59
def prefixEnd_2017058 : Nat := 4983230072969 + 3 ^ 40 * 2017058 * 2
def baseEnd_2017058 : Nat := 1035720261996674484998725

theorem tailTrace_2017058 : CollatzResearch.WordTrace tailWord_2017058 prefixEnd_2017058 1035720261996674484998725 := by
  unfold tailWord_2017058
  simp only [CollatzResearch.WordTrace]
  refine ⟨18392037281637706731392957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49045432751033884617047885 18392037281637706731392957)
  ·
    refine ⟨6897013980614140024272359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18392037281637706731392957 6897013980614140024272359)
    ·
      refine ⟨10345520970921210036408539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6897013980614140024272359 10345520970921210036408539)
      ·
        refine ⟨15518281456381815054612809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10345520970921210036408539 15518281456381815054612809)
        ·
          refine ⟨11638711092286361290959607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15518281456381815054612809 11638711092286361290959607)
          ·
            refine ⟨17458066638429541936439411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11638711092286361290959607 17458066638429541936439411)
            ·
              refine ⟨26187099957644312904659117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17458066638429541936439411 26187099957644312904659117)
              ·
                refine ⟨9820162484116617339247169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26187099957644312904659117 9820162484116617339247169)
                ·
                  refine ⟨7365121863087463004435377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9820162484116617339247169 7365121863087463004435377)
                  ·
                    refine ⟨5523841397315597253326533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7365121863087463004435377 5523841397315597253326533)
                    ·
                      refine ⟨1035720261996674484998725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5523841397315597253326533 1035720261996674484998725)
                      ·
                        rfl

theorem cell23_2017058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_2017058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017058 prefixEnd_2017058 := by exact prefixLift 2017058
  have htrace : WordTrace (prefixWord ++ tailWord_2017058) baseStart_2017058 baseEnd_2017058 := by
    simpa [prefixWord, tailWord_2017058, baseEnd_2017058] using wordTrace_append hprefix tailTrace_2017058
  have hstable : (prefixWord ++ tailWord_2017058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017058).length < 2 ^ (prefixWord ++ tailWord_2017058).sum := by decide
  have hdescent : baseEnd_2017058 < baseStart_2017058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017088 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 3, 7, 2]
def baseStart_2017088 : Nat := 118140960795 + 2017088 * 2 ^ 59
def prefixEnd_2017088 : Nat := 4983230072969 + 3 ^ 40 * 2017088 * 2
def baseEnd_2017088 : Nat := 1035735666416309367623587

theorem tailTrace_2017088 : CollatzResearch.WordTrace tailWord_2017088 prefixEnd_2017088 1035735666416309367623587 := by
  unfold tailWord_2017088
  simp only [CollatzResearch.WordTrace]
  refine ⟨36784621658221071024581959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49046162210961428032775945 36784621658221071024581959)
  ·
    refine ⟨55176932487331606536872939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36784621658221071024581959 55176932487331606536872939)
    ·
      refine ⟨82765398730997409805309409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55176932487331606536872939 82765398730997409805309409)
      ·
        refine ⟨62074049048248057353982057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82765398730997409805309409 62074049048248057353982057)
        ·
          refine ⟨46555536786186043015486543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62074049048248057353982057 46555536786186043015486543)
          ·
            refine ⟨69833305179279064523229815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46555536786186043015486543 69833305179279064523229815)
            ·
              refine ⟨104749957768918596784844723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69833305179279064523229815 104749957768918596784844723)
              ·
                refine ⟨157124936653377895177267085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104749957768918596784844723 157124936653377895177267085)
                ·
                  refine ⟨58921851245016710691475157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157124936653377895177267085 58921851245016710691475157)
                  ·
                    refine ⟨1380980888555079156831449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58921851245016710691475157 1380980888555079156831449)
                    ·
                      refine ⟨1035735666416309367623587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1380980888555079156831449 1035735666416309367623587)
                      ·
                        rfl

theorem cell23_2017088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 7, 2].length) (baseStart_2017088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017088 prefixEnd_2017088 := by exact prefixLift 2017088
  have htrace : WordTrace (prefixWord ++ tailWord_2017088) baseStart_2017088 baseEnd_2017088 := by
    simpa [prefixWord, tailWord_2017088, baseEnd_2017088] using wordTrace_append hprefix tailTrace_2017088
  have hstable : (prefixWord ++ tailWord_2017088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017088).length < 2 ^ (prefixWord ++ tailWord_2017088).sum := by decide
  have hdescent : baseEnd_2017088 < baseStart_2017088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017098 : List Nat := [3, 1, 2, 1, 1, 1, 5, 2, 2, 5]
def baseStart_2017098 : Nat := 118140960795 + 2017098 * 2 ^ 59
def prefixEnd_2017098 : Nat := 4983230072969 + 3 ^ 40 * 2017098 * 2
def baseEnd_2017098 : Nat := 345246933740951442832847

theorem tailTrace_2017098 : CollatzResearch.WordTrace tailWord_2017098 prefixEnd_2017098 345246933740951442832847 := by
  unfold tailWord_2017098
  simp only [CollatzResearch.WordTrace]
  refine ⟨18392402011601478439256987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49046405364270609171351965 18392402011601478439256987)
  ·
    refine ⟨27588603017402217658885481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18392402011601478439256987 27588603017402217658885481)
    ·
      refine ⟨20691452263051663244164111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27588603017402217658885481 20691452263051663244164111)
      ·
        refine ⟨31037178394577494866246167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20691452263051663244164111 31037178394577494866246167)
        ·
          refine ⟨46555767591866242299369251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31037178394577494866246167 46555767591866242299369251)
          ·
            refine ⟨69833651387799363449053877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46555767591866242299369251 69833651387799363449053877)
            ·
              refine ⟨6546904817606190323348801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69833651387799363449053877 6546904817606190323348801)
              ·
                refine ⟨4910178613204642742511601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6546904817606190323348801 4910178613204642742511601)
                ·
                  refine ⟨3682633959903482056883701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4910178613204642742511601 3682633959903482056883701)
                  ·
                    refine ⟨345246933740951442832847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3682633959903482056883701 345246933740951442832847)
                    ·
                      rfl

theorem cell23_2017098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_2017098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017098 prefixEnd_2017098 := by exact prefixLift 2017098
  have htrace : WordTrace (prefixWord ++ tailWord_2017098) baseStart_2017098 baseEnd_2017098 := by
    simpa [prefixWord, tailWord_2017098, baseEnd_2017098] using wordTrace_append hprefix tailTrace_2017098
  have hstable : (prefixWord ++ tailWord_2017098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017098).length < 2 ^ (prefixWord ++ tailWord_2017098).sum := by decide
  have hdescent : baseEnd_2017098 < baseStart_2017098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017108 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_2017108 : Nat := 118140960795 + 2017108 * 2 ^ 59
def prefixEnd_2017108 : Nat := 4983230072969 + 3 ^ 40 * 2017108 * 2
def baseEnd_2017108 : Nat := 1035745936029399289373495

theorem tailTrace_2017108 : CollatzResearch.WordTrace tailWord_2017108 prefixEnd_2017108 1035745936029399289373495 := by
  unfold tailWord_2017108
  simp only [CollatzResearch.WordTrace]
  refine ⟨36784986388184842732445989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49046648517579790309927985 36784986388184842732445989)
  ·
    refine ⟨6897184947784658012333623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36784986388184842732445989 6897184947784658012333623)
    ·
      refine ⟨10345777421676987018500435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6897184947784658012333623 10345777421676987018500435)
      ·
        refine ⟨15518666132515480527750653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10345777421676987018500435 15518666132515480527750653)
        ·
          refine ⟨5819499799693305197906495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15518666132515480527750653 5819499799693305197906495)
          ·
            refine ⟨8729249699539957796859743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5819499799693305197906495 8729249699539957796859743)
            ·
              refine ⟨13093874549309936695289615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8729249699539957796859743 13093874549309936695289615)
              ·
                refine ⟨19640811823964905042934423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13093874549309936695289615 19640811823964905042934423)
                ·
                  refine ⟨29461217735947357564401635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19640811823964905042934423 29461217735947357564401635)
                  ·
                    refine ⟨44191826603921036346602453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29461217735947357564401635 44191826603921036346602453)
                    ·
                      refine ⟨1035745936029399289373495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44191826603921036346602453 1035745936029399289373495)
                      ·
                        rfl

theorem cell23_2017108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_2017108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017108 prefixEnd_2017108 := by exact prefixLift 2017108
  have htrace : WordTrace (prefixWord ++ tailWord_2017108) baseStart_2017108 baseEnd_2017108 := by
    simpa [prefixWord, tailWord_2017108, baseEnd_2017108] using wordTrace_append hprefix tailTrace_2017108
  have hstable : (prefixWord ++ tailWord_2017108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017108).length < 2 ^ (prefixWord ++ tailWord_2017108).sum := by decide
  have hdescent : baseEnd_2017108 < baseStart_2017108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017131 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 6]
def baseStart_2017131 : Nat := 118140960795 + 2017131 * 2 ^ 59
def prefixEnd_2017131 : Nat := 4983230072969 + 3 ^ 40 * 2017131 * 2
def baseEnd_2017131 : Nat := 1035757746084452699385889

theorem tailTrace_2017131 : CollatzResearch.WordTrace tailWord_2017131 prefixEnd_2017131 1035757746084452699385889 := by
  unfold tailWord_2017131
  simp only [CollatzResearch.WordTrace]
  refine ⟨73570811655286360392979247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49047207770190906928652831 73570811655286360392979247)
  ·
    refine ⟨110356217482929540589468871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73570811655286360392979247 110356217482929540589468871)
    ·
      refine ⟨165534326224394310884203307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110356217482929540589468871 165534326224394310884203307)
      ·
        refine ⟨248301489336591466326304961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165534326224394310884203307 248301489336591466326304961)
        ·
          refine ⟨186226117002443599744728721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248301489336591466326304961 186226117002443599744728721)
          ·
            refine ⟨139669587751832699808546541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186226117002443599744728721 139669587751832699808546541)
            ·
              refine ⟨52376095406937262428204953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139669587751832699808546541 52376095406937262428204953)
              ·
                refine ⟨39282071555202946821153715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52376095406937262428204953 39282071555202946821153715)
                ·
                  refine ⟨58923107332804420231730573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39282071555202946821153715 58923107332804420231730573)
                  ·
                    refine ⟨22096165249801657586898965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58923107332804420231730573 22096165249801657586898965)
                    ·
                      refine ⟨1035757746084452699385889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22096165249801657586898965 1035757746084452699385889)
                      ·
                        rfl

theorem cell23_2017131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 6].length) (baseStart_2017131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017131 prefixEnd_2017131 := by exact prefixLift 2017131
  have htrace : WordTrace (prefixWord ++ tailWord_2017131) baseStart_2017131 baseEnd_2017131 := by
    simpa [prefixWord, tailWord_2017131, baseEnd_2017131] using wordTrace_append hprefix tailTrace_2017131
  have hstable : (prefixWord ++ tailWord_2017131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017131).length < 2 ^ (prefixWord ++ tailWord_2017131).sum := by decide
  have hdescent : baseEnd_2017131 < baseStart_2017131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017155 : List Nat := [1, 1, 1, 3, 4, 2, 2, 2, 2, 2, 3]
def baseStart_2017155 : Nat := 118140960795 + 2017155 * 2 ^ 59
def prefixEnd_2017155 : Nat := 4983230072969 + 3 ^ 40 * 2017155 * 2
def baseEnd_2017155 : Nat := 1035770069620160605485779

theorem tailTrace_2017155 : CollatzResearch.WordTrace tailWord_2017155 prefixEnd_2017155 1035770069620160605485779 := by
  unfold tailWord_2017155
  simp only [CollatzResearch.WordTrace]
  refine ⟨73571687007199412491852919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49047791338132941661235279 73571687007199412491852919)
  ·
    refine ⟨110357530510799118737779379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73571687007199412491852919 110357530510799118737779379)
    ·
      refine ⟨165536295766198678106669069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110357530510799118737779379 165536295766198678106669069)
      ·
        refine ⟨62076110912324504290000901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165536295766198678106669069 62076110912324504290000901)
        ·
          refine ⟨11639270796060844554375169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62076110912324504290000901 11639270796060844554375169)
          ·
            refine ⟨8729453097045633415781377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11639270796060844554375169 8729453097045633415781377)
            ·
              refine ⟨6547089822784225061836033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8729453097045633415781377 6547089822784225061836033)
              ·
                refine ⟨4910317367088168796377025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6547089822784225061836033 4910317367088168796377025)
                ·
                  refine ⟨3682738025316126597282769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4910317367088168796377025 3682738025316126597282769)
                  ·
                    refine ⟨2762053518987094947962077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3682738025316126597282769 2762053518987094947962077)
                    ·
                      refine ⟨1035770069620160605485779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2762053518987094947962077 1035770069620160605485779)
                      ·
                        rfl

theorem cell23_2017155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2, 3].length) (baseStart_2017155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017155 prefixEnd_2017155 := by exact prefixLift 2017155
  have htrace : WordTrace (prefixWord ++ tailWord_2017155) baseStart_2017155 baseEnd_2017155 := by
    simpa [prefixWord, tailWord_2017155, baseEnd_2017155] using wordTrace_append hprefix tailTrace_2017155
  have hstable : (prefixWord ++ tailWord_2017155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017155).length < 2 ^ (prefixWord ++ tailWord_2017155).sum := by decide
  have hdescent : baseEnd_2017155 < baseStart_2017155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017262 : List Nat := [4, 1, 2, 1, 3, 2, 2, 1, 1, 1, 5]
def baseStart_2017262 : Nat := 118140960795 + 2017262 * 2 ^ 59
def prefixEnd_2017262 : Nat := 4983230072969 + 3 ^ 40 * 2017262 * 2
def baseEnd_2017262 : Nat := 1035825012050191686847787

theorem tailTrace_2017262 : CollatzResearch.WordTrace tailWord_2017262 prefixEnd_2017262 1035825012050191686847787 := by
  unfold tailWord_2017262
  simp only [CollatzResearch.WordTrace]
  refine ⟨9196948702226471220749755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49050393078541179843998693 9196948702226471220749755)
  ·
    refine ⟨13795423053339706831124633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9196948702226471220749755 13795423053339706831124633)
    ·
      refine ⟨10346567290004780123343475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13795423053339706831124633 10346567290004780123343475)
      ·
        refine ⟨15519850935007170185015213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10346567290004780123343475 15519850935007170185015213)
        ·
          refine ⟨5819944100627688819380705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15519850935007170185015213 5819944100627688819380705)
          ·
            refine ⟨4364958075470766614535529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5819944100627688819380705 4364958075470766614535529)
            ·
              refine ⟨3273718556603074960901647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4364958075470766614535529 3273718556603074960901647)
              ·
                refine ⟨4910577834904612441352471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3273718556603074960901647 4910577834904612441352471)
                ·
                  refine ⟨7365866752356918662028707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4910577834904612441352471 7365866752356918662028707)
                  ·
                    refine ⟨11048800128535377993043061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7365866752356918662028707 11048800128535377993043061)
                    ·
                      refine ⟨1035825012050191686847787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11048800128535377993043061 1035825012050191686847787)
                      ·
                        rfl

theorem cell23_2017262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_2017262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017262 prefixEnd_2017262 := by exact prefixLift 2017262
  have htrace : WordTrace (prefixWord ++ tailWord_2017262) baseStart_2017262 baseEnd_2017262 := by
    simpa [prefixWord, tailWord_2017262, baseEnd_2017262] using wordTrace_append hprefix tailTrace_2017262
  have hstable : (prefixWord ++ tailWord_2017262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017262).length < 2 ^ (prefixWord ++ tailWord_2017262).sum := by decide
  have hdescent : baseEnd_2017262 < baseStart_2017262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017265 : List Nat := [1, 2, 2, 2, 5, 2, 9]
def baseStart_2017265 : Nat := 118140960795 + 2017265 * 2 ^ 59
def prefixEnd_2017265 : Nat := 4983230072969 + 3 ^ 40 * 2017265 * 2
def baseEnd_2017265 : Nat := 12787982129532779939633

theorem tailTrace_2017265 : CollatzResearch.WordTrace tailWord_2017265 prefixEnd_2017265 12787982129532779939633 := by
  unfold tailWord_2017265
  simp only [CollatzResearch.WordTrace]
  refine ⟨73575699036800901278357249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49050466024533934185571499 73575699036800901278357249)
  ·
    refine ⟨55181774277600675958767937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73575699036800901278357249 55181774277600675958767937)
    ·
      refine ⟨41386330708200506969075953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55181774277600675958767937 41386330708200506969075953)
      ·
        refine ⟨31039748031150380226806965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41386330708200506969075953 31039748031150380226806965)
        ·
          refine ⟨2909976377920348146263153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31039748031150380226806965 2909976377920348146263153)
          ·
            refine ⟨2182482283440261109697365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2909976377920348146263153 2182482283440261109697365)
            ·
              refine ⟨12787982129532779939633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2182482283440261109697365 12787982129532779939633)
              ·
                rfl

theorem cell23_2017265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 9].length) (baseStart_2017265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017265 prefixEnd_2017265 := by exact prefixLift 2017265
  have htrace : WordTrace (prefixWord ++ tailWord_2017265) baseStart_2017265 baseEnd_2017265 := by
    simpa [prefixWord, tailWord_2017265, baseEnd_2017265] using wordTrace_append hprefix tailTrace_2017265
  have hstable : (prefixWord ++ tailWord_2017265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017265).length < 2 ^ (prefixWord ++ tailWord_2017265).sum := by decide
  have hdescent : baseEnd_2017265 < baseStart_2017265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017326 : List Nat := [4, 1, 3, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_2017326 : Nat := 118140960795 + 2017326 * 2 ^ 59
def prefixEnd_2017326 : Nat := 4983230072969 + 3 ^ 40 * 2017326 * 2
def baseEnd_2017326 : Nat := 1035857874812079436447493

theorem tailTrace_2017326 : CollatzResearch.WordTrace tailWord_2017326 prefixEnd_2017326 1035857874812079436447493 := by
  unfold tailWord_2017326
  simp only [CollatzResearch.WordTrace]
  refine ⟨9197240486197488587040979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49051949259719939130885221 9197240486197488587040979)
  ·
    refine ⟨13795860729296232880561469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9197240486197488587040979 13795860729296232880561469)
    ·
      refine ⟨5173447773486087330210551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13795860729296232880561469 5173447773486087330210551)
      ·
        refine ⟨7760171660229130995315827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5173447773486087330210551 7760171660229130995315827)
        ·
          refine ⟨11640257490343696492973741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7760171660229130995315827 11640257490343696492973741)
          ·
            refine ⟨4365096558878886184865153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11640257490343696492973741 4365096558878886184865153)
            ·
              refine ⟨3273822419159164638648865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4365096558878886184865153 3273822419159164638648865)
              ·
                refine ⟨2455366814369373478986649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3273822419159164638648865 2455366814369373478986649)
                ·
                  refine ⟨1841525110777030109239987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2455366814369373478986649 1841525110777030109239987)
                  ·
                    refine ⟨2762287666165545163859981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1841525110777030109239987 2762287666165545163859981)
                    ·
                      refine ⟨1035857874812079436447493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2762287666165545163859981 1035857874812079436447493)
                      ·
                        rfl

theorem cell23_2017326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_2017326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017326 prefixEnd_2017326 := by exact prefixLift 2017326
  have htrace : WordTrace (prefixWord ++ tailWord_2017326) baseStart_2017326 baseEnd_2017326 := by
    simpa [prefixWord, tailWord_2017326, baseEnd_2017326] using wordTrace_append hprefix tailTrace_2017326
  have hstable : (prefixWord ++ tailWord_2017326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017326).length < 2 ^ (prefixWord ++ tailWord_2017326).sum := by decide
  have hdescent : baseEnd_2017326 < baseStart_2017326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017335 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 2, 4, 3]
def baseStart_2017335 : Nat := 118140960795 + 2017335 * 2 ^ 59
def prefixEnd_2017335 : Nat := 4983230072969 + 3 ^ 40 * 2017335 * 2
def baseEnd_2017335 : Nat := 1035862496137969901234951

theorem tailTrace_2017335 : CollatzResearch.WordTrace tailWord_2017335 prefixEnd_2017335 1035862496137969901234951 := by
  unfold tailWord_2017335
  simp only [CollatzResearch.WordTrace]
  refine ⟨73578252146547303233405459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49052168097698202155603639 73578252146547303233405459)
  ·
    refine ⟨110367378219820954850108189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73578252146547303233405459 110367378219820954850108189)
    ·
      refine ⟨41387766832432858068790571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110367378219820954850108189 41387766832432858068790571)
      ·
        refine ⟨62081650248649287103185857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41387766832432858068790571 62081650248649287103185857)
        ·
          refine ⟨46561237686486965327389393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62081650248649287103185857 46561237686486965327389393)
          ·
            refine ⟨34920928264865223995542045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46561237686486965327389393 34920928264865223995542045)
            ·
              refine ⟨13095348099324458998328267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34920928264865223995542045 13095348099324458998328267)
              ·
                refine ⟨19643022148986688497492401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13095348099324458998328267 19643022148986688497492401)
                ·
                  refine ⟨14732266611740016373119301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19643022148986688497492401 14732266611740016373119301)
                  ·
                    refine ⟨2762299989701253069959869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14732266611740016373119301 2762299989701253069959869)
                    ·
                      refine ⟨1035862496137969901234951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2762299989701253069959869 1035862496137969901234951)
                      ·
                        rfl

theorem cell23_2017335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4, 3].length) (baseStart_2017335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017335 prefixEnd_2017335 := by exact prefixLift 2017335
  have htrace : WordTrace (prefixWord ++ tailWord_2017335) baseStart_2017335 baseEnd_2017335 := by
    simpa [prefixWord, tailWord_2017335, baseEnd_2017335] using wordTrace_append hprefix tailTrace_2017335
  have hstable : (prefixWord ++ tailWord_2017335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017335).length < 2 ^ (prefixWord ++ tailWord_2017335).sum := by decide
  have hdescent : baseEnd_2017335 < baseStart_2017335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017385 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 4, 5]
def baseStart_2017385 : Nat := 118140960795 + 2017385 * 2 ^ 59
def prefixEnd_2017385 : Nat := 4983230072969 + 3 ^ 40 * 2017385 * 2
def baseEnd_2017385 : Nat := 345296056723564901869907

theorem tailTrace_2017385 : CollatzResearch.WordTrace tailWord_2017385 prefixEnd_2017385 345296056723564901869907 := by
  unfold tailWord_2017385
  simp only [CollatzResearch.WordTrace]
  refine ⟨73580075796366161772725609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49053383864244107848483739 73580075796366161772725609)
  ·
    refine ⟨55185056847274621329544207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73580075796366161772725609 55185056847274621329544207)
    ·
      refine ⟨82777585270911931994316311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55185056847274621329544207 82777585270911931994316311)
      ·
        refine ⟨124166377906367897991474467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82777585270911931994316311 124166377906367897991474467)
        ·
          refine ⟨186249566859551846987211701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124166377906367897991474467 186249566859551846987211701)
          ·
            refine ⟨17460896893082985655051097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186249566859551846987211701 17460896893082985655051097)
            ·
              refine ⟨13095672669812239241288323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17460896893082985655051097 13095672669812239241288323)
              ·
                refine ⟨19643509004718358861932485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13095672669812239241288323 19643509004718358861932485)
                ·
                  refine ⟨3683157938384692286612341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19643509004718358861932485 3683157938384692286612341)
                  ·
                    refine ⟨345296056723564901869907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3683157938384692286612341 345296056723564901869907)
                    ·
                      rfl

theorem cell23_2017385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 5].length) (baseStart_2017385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017385 prefixEnd_2017385 := by exact prefixLift 2017385
  have htrace : WordTrace (prefixWord ++ tailWord_2017385) baseStart_2017385 baseEnd_2017385 := by
    simpa [prefixWord, tailWord_2017385, baseEnd_2017385] using wordTrace_append hprefix tailTrace_2017385
  have hstable : (prefixWord ++ tailWord_2017385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017385).length < 2 ^ (prefixWord ++ tailWord_2017385).sum := by decide
  have hdescent : baseEnd_2017385 < baseStart_2017385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017439 : List Nat := [1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 4]
def baseStart_2017439 : Nat := 118140960795 + 2017439 * 2 ^ 59
def prefixEnd_2017439 : Nat := 4983230072969 + 3 ^ 40 * 2017439 * 2
def baseEnd_2017439 : Nat := 1035915898126037494334473

theorem tailTrace_2017439 : CollatzResearch.WordTrace tailWord_2017439 prefixEnd_2017439 1035915898126037494334473 := by
  unfold tailWord_2017439
  simp only [CollatzResearch.WordTrace]
  refine ⟨73582045338170528995191371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49054696892113685996794247 73582045338170528995191371)
  ·
    refine ⟨110373068007255793492787057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73582045338170528995191371 110373068007255793492787057)
    ·
      refine ⟨82779801005441845119590293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110373068007255793492787057 82779801005441845119590293)
      ·
        refine ⟨3880303172130086489980795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 82779801005441845119590293 3880303172130086489980795)
        ·
          refine ⟨5820454758195129734971193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3880303172130086489980795 5820454758195129734971193)
          ·
            refine ⟨4365341068646347301228395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5820454758195129734971193 4365341068646347301228395)
            ·
              refine ⟨6548011602969520951842593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4365341068646347301228395 6548011602969520951842593)
              ·
                refine ⟨4911008702227140713881945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6548011602969520951842593 4911008702227140713881945)
                ·
                  refine ⟨3683256526670355535411459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4911008702227140713881945 3683256526670355535411459)
                  ·
                    refine ⟨5524884790005533303117189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3683256526670355535411459 5524884790005533303117189)
                    ·
                      refine ⟨1035915898126037494334473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5524884790005533303117189 1035915898126037494334473)
                      ·
                        rfl

theorem cell23_2017439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_2017439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017439 prefixEnd_2017439 := by exact prefixLift 2017439
  have htrace : WordTrace (prefixWord ++ tailWord_2017439) baseStart_2017439 baseEnd_2017439 := by
    simpa [prefixWord, tailWord_2017439, baseEnd_2017439] using wordTrace_append hprefix tailTrace_2017439
  have hstable : (prefixWord ++ tailWord_2017439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017439).length < 2 ^ (prefixWord ++ tailWord_2017439).sum := by decide
  have hdescent : baseEnd_2017439 < baseStart_2017439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017445 : List Nat := [1, 3, 1, 2, 1, 3, 1, 3, 8]
def baseStart_2017445 : Nat := 118140960795 + 2017445 * 2 ^ 59
def prefixEnd_2017445 : Nat := 4983230072969 + 3 ^ 40 * 2017445 * 2
def baseEnd_2017445 : Nat := 115102108778884941206605

theorem tailTrace_2017445 : CollatzResearch.WordTrace tailWord_2017445 prefixEnd_2017445 115102108778884941206605 := by
  unfold tailWord_2017445
  simp only [CollatzResearch.WordTrace]
  refine ⟨73582264176148792019909789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49054842784099194679939859 73582264176148792019909789)
  ·
    refine ⟨27593349066055797007466171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73582264176148792019909789 27593349066055797007466171)
    ·
      refine ⟨41390023599083695511199257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27593349066055797007466171 41390023599083695511199257)
      ·
        refine ⟨31042517699312771633399443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41390023599083695511199257 31042517699312771633399443)
        ·
          refine ⟨46563776548969157450099165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31042517699312771633399443 46563776548969157450099165)
          ·
            refine ⟨17461416205863434043787187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46563776548969157450099165 17461416205863434043787187)
            ·
              refine ⟨26192124308795151065680781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17461416205863434043787187 26192124308795151065680781)
              ·
                refine ⟨9822046615798181649630293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26192124308795151065680781 9822046615798181649630293)
                ·
                  refine ⟨115102108778884941206605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9822046615798181649630293 115102108778884941206605)
                  ·
                    rfl

theorem cell23_2017445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 8].length) (baseStart_2017445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017445 prefixEnd_2017445 := by exact prefixLift 2017445
  have htrace : WordTrace (prefixWord ++ tailWord_2017445) baseStart_2017445 baseEnd_2017445 := by
    simpa [prefixWord, tailWord_2017445, baseEnd_2017445] using wordTrace_append hprefix tailTrace_2017445
  have hstable : (prefixWord ++ tailWord_2017445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017445).length < 2 ^ (prefixWord ++ tailWord_2017445).sum := by decide
  have hdescent : baseEnd_2017445 < baseStart_2017445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017476 : List Nat := [2, 3, 3, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_2017476 : Nat := 118140960795 + 2017476 * 2 ^ 59
def prefixEnd_2017476 : Nat := 4983230072969 + 3 ^ 40 * 2017476 * 2
def baseEnd_2017476 : Nat := 1035934896910253849571803

theorem tailTrace_2017476 : CollatzResearch.WordTrace tailWord_2017476 prefixEnd_2017476 1035934896910253849571803 := by
  unfold tailWord_2017476
  simp only [CollatzResearch.WordTrace]
  refine ⟨36791697419518242157144141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49055596559357656209525521 36791697419518242157144141)
  ·
    refine ⟨13796886532319340808929053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36791697419518242157144141 13796886532319340808929053)
    ·
      refine ⟨5173832449619752803348395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13796886532319340808929053 5173832449619752803348395)
      ·
        refine ⟨7760748674429629205022593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5173832449619752803348395 7760748674429629205022593)
        ·
          refine ⟨5820561505822221903766945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7760748674429629205022593 5820561505822221903766945)
          ·
            refine ⟨4365421129366666427825209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5820561505822221903766945 4365421129366666427825209)
            ·
              refine ⟨3274065847024999820868907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4365421129366666427825209 3274065847024999820868907)
              ·
                refine ⟨4911098770537499731303361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3274065847024999820868907 4911098770537499731303361)
                ·
                  refine ⟨3683324077903124798477521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4911098770537499731303361 3683324077903124798477521)
                  ·
                    refine ⟨2762493058427343598858141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3683324077903124798477521 2762493058427343598858141)
                    ·
                      refine ⟨1035934896910253849571803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2762493058427343598858141 1035934896910253849571803)
                      ·
                        rfl

theorem cell23_2017476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_2017476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017476 prefixEnd_2017476 := by exact prefixLift 2017476
  have htrace : WordTrace (prefixWord ++ tailWord_2017476) baseStart_2017476 baseEnd_2017476 := by
    simpa [prefixWord, tailWord_2017476, baseEnd_2017476] using wordTrace_append hprefix tailTrace_2017476
  have hstable : (prefixWord ++ tailWord_2017476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017476).length < 2 ^ (prefixWord ++ tailWord_2017476).sum := by decide
  have hdescent : baseEnd_2017476 < baseStart_2017476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017500 : List Nat := [2, 2, 5, 2, 1, 1, 1, 4, 1, 4]
def baseStart_2017500 : Nat := 118140960795 + 2017500 * 2 ^ 59
def prefixEnd_2017500 : Nat := 4983230072969 + 3 ^ 40 * 2017500 * 2
def baseEnd_2017500 : Nat := 345315740148653918557231

theorem tailTrace_2017500 : CollatzResearch.WordTrace tailWord_2017500 prefixEnd_2017500 345315740148653918557231 := by
  unfold tailWord_2017500
  simp only [CollatzResearch.WordTrace]
  refine ⟨36792135095474768206580977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49056180127299690942107969 36792135095474768206580977)
  ·
    refine ⟨27594101321606076154935733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36792135095474768206580977 27594101321606076154935733)
    ·
      refine ⟨2586946998900569639525225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27594101321606076154935733 2586946998900569639525225)
      ·
        refine ⟨1940210249175427229643919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2586946998900569639525225 1940210249175427229643919)
        ·
          refine ⟨2910315373763140844465879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1940210249175427229643919 2910315373763140844465879)
          ·
            refine ⟨4365473060644711266698819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2910315373763140844465879 4365473060644711266698819)
            ·
              refine ⟨6548209590967066900048229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4365473060644711266698819 6548209590967066900048229)
              ·
                refine ⟨1227789298306325043759043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6548209590967066900048229 1227789298306325043759043)
                ·
                  refine ⟨1841683947459487565638565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1227789298306325043759043 1841683947459487565638565)
                  ·
                    refine ⟨345315740148653918557231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1841683947459487565638565 345315740148653918557231)
                    ·
                      rfl

theorem cell23_2017500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_2017500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017500 prefixEnd_2017500 := by exact prefixLift 2017500
  have htrace : WordTrace (prefixWord ++ tailWord_2017500) baseStart_2017500 baseEnd_2017500 := by
    simpa [prefixWord, tailWord_2017500, baseEnd_2017500] using wordTrace_append hprefix tailTrace_2017500
  have hstable : (prefixWord ++ tailWord_2017500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017500).length < 2 ^ (prefixWord ++ tailWord_2017500).sum := by decide
  have hdescent : baseEnd_2017500 < baseStart_2017500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017540 : List Nat := [2, 3, 2, 2, 3, 1, 2, 3, 1, 1, 3]
def baseStart_2017540 : Nat := 118140960795 + 2017540 * 2 ^ 59
def prefixEnd_2017540 : Nat := 4983230072969 + 3 ^ 40 * 2017540 * 2
def baseEnd_2017540 : Nat := 1035967759672141599171509

theorem tailTrace_2017540 : CollatzResearch.WordTrace tailWord_2017540 prefixEnd_2017540 1035967759672141599171509 := by
  unfold tailWord_2017540
  simp only [CollatzResearch.WordTrace]
  refine ⟨36792864555402311622309037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49057152740536415496412049 36792864555402311622309037)
  ·
    refine ⟨13797324208275866858365889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36792864555402311622309037 13797324208275866858365889)
    ·
      refine ⟨10347993156206900143774417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13797324208275866858365889 10347993156206900143774417)
      ·
        refine ⟨7760994867155175107830813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10347993156206900143774417 7760994867155175107830813)
        ·
          refine ⟨2910373075183190665436555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7760994867155175107830813 2910373075183190665436555)
          ·
            refine ⟨4365559612774785998154833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2910373075183190665436555 4365559612774785998154833)
            ·
              refine ⟨3274169709581089498616125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4365559612774785998154833 3274169709581089498616125)
              ·
                refine ⟨1227813641092908561981047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3274169709581089498616125 1227813641092908561981047)
                ·
                  refine ⟨1841720461639362842971571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1227813641092908561981047 1841720461639362842971571)
                  ·
                    refine ⟨2762580692459044264457357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1841720461639362842971571 2762580692459044264457357)
                    ·
                      refine ⟨1035967759672141599171509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2762580692459044264457357 1035967759672141599171509)
                      ·
                        rfl

theorem cell23_2017540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_2017540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017540 prefixEnd_2017540 := by exact prefixLift 2017540
  have htrace : WordTrace (prefixWord ++ tailWord_2017540) baseStart_2017540 baseEnd_2017540 := by
    simpa [prefixWord, tailWord_2017540, baseEnd_2017540] using wordTrace_append hprefix tailTrace_2017540
  have hstable : (prefixWord ++ tailWord_2017540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017540).length < 2 ^ (prefixWord ++ tailWord_2017540).sum := by decide
  have hdescent : baseEnd_2017540 < baseStart_2017540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017546 : List Nat := [3, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4]
def baseStart_2017546 : Nat := 118140960795 + 2017546 * 2 ^ 59
def prefixEnd_2017546 : Nat := 4983230072969 + 3 ^ 40 * 2017546 * 2
def baseEnd_2017546 : Nat := 1035970840556068575696481

theorem tailTrace_2017546 : CollatzResearch.WordTrace tailWord_2017546 prefixEnd_2017546 1035970840556068575696481 := by
  unfold tailWord_2017546
  simp only [CollatzResearch.WordTrace]
  refine ⟨18396486987195721567334123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49057298632521924179557661 18396486987195721567334123)
  ·
    refine ⟨27594730480793582351001185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18396486987195721567334123 27594730480793582351001185)
    ·
      refine ⟨20696047860595186763250889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27594730480793582351001185 20696047860595186763250889)
      ·
        refine ⟨15522035895446390072438167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20696047860595186763250889 15522035895446390072438167)
        ·
          refine ⟨23283053843169585108657251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15522035895446390072438167 23283053843169585108657251)
          ·
            refine ⟨34924580764754377662985877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23283053843169585108657251 34924580764754377662985877)
            ·
              refine ⟨1637089723347861452952463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34924580764754377662985877 1637089723347861452952463)
              ·
                refine ⟨2455634585021792179428695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1637089723347861452952463 2455634585021792179428695)
                ·
                  refine ⟨3683451877532688269143043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2455634585021792179428695 3683451877532688269143043)
                  ·
                    refine ⟨5525177816299032403714565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3683451877532688269143043 5525177816299032403714565)
                    ·
                      refine ⟨1035970840556068575696481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5525177816299032403714565 1035970840556068575696481)
                      ·
                        rfl

theorem cell23_2017546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_2017546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017546 prefixEnd_2017546 := by exact prefixLift 2017546
  have htrace : WordTrace (prefixWord ++ tailWord_2017546) baseStart_2017546 baseEnd_2017546 := by
    simpa [prefixWord, tailWord_2017546, baseEnd_2017546] using wordTrace_append hprefix tailTrace_2017546
  have hstable : (prefixWord ++ tailWord_2017546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017546).length < 2 ^ (prefixWord ++ tailWord_2017546).sum := by decide
  have hdescent : baseEnd_2017546 < baseStart_2017546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017563 : List Nat := [1, 1, 1, 1, 1, 1, 8, 4, 1, 2, 2]
def baseStart_2017563 : Nat := 118140960795 + 2017563 * 2 ^ 59
def prefixEnd_2017563 : Nat := 4983230072969 + 3 ^ 40 * 2017563 * 2
def baseEnd_2017563 : Nat := 1035979569727195009183903

theorem tailTrace_2017563 : CollatzResearch.WordTrace tailWord_2017563 prefixEnd_2017563 1035979569727195009183903 := by
  unfold tailWord_2017563
  simp only [CollatzResearch.WordTrace]
  refine ⟨73586567989721298172705343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49057711993147532115136895 73586567989721298172705343)
  ·
    refine ⟨110379851984581947259058015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73586567989721298172705343 110379851984581947259058015)
    ·
      refine ⟨165569777976872920888587023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110379851984581947259058015 165569777976872920888587023)
      ·
        refine ⟨248354666965309381332880535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165569777976872920888587023 248354666965309381332880535)
        ·
          refine ⟨372532000447964071999320803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248354666965309381332880535 372532000447964071999320803)
          ·
            refine ⟨558798000671946107998981205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372532000447964071999320803 558798000671946107998981205)
            ·
              refine ⟨6548414070374368453113061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 558798000671946107998981205 6548414070374368453113061)
              ·
                refine ⟨1227827638195194084958699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6548414070374368453113061 1227827638195194084958699)
                ·
                  refine ⟨1841741457292791127438049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1227827638195194084958699 1841741457292791127438049)
                  ·
                    refine ⟨1381306092969593345578537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1841741457292791127438049 1381306092969593345578537)
                    ·
                      refine ⟨1035979569727195009183903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1381306092969593345578537 1035979569727195009183903)
                      ·
                        rfl

theorem cell23_2017563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4, 1, 2, 2].length) (baseStart_2017563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017563 prefixEnd_2017563 := by exact prefixLift 2017563
  have htrace : WordTrace (prefixWord ++ tailWord_2017563) baseStart_2017563 baseEnd_2017563 := by
    simpa [prefixWord, tailWord_2017563, baseEnd_2017563] using wordTrace_append hprefix tailTrace_2017563
  have hstable : (prefixWord ++ tailWord_2017563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017563).length < 2 ^ (prefixWord ++ tailWord_2017563).sum := by decide
  have hdescent : baseEnd_2017563 < baseStart_2017563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017566 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_2017566 : Nat := 118140960795 + 2017566 * 2 ^ 59
def prefixEnd_2017566 : Nat := 4983230072969 + 3 ^ 40 * 2017566 * 2
def baseEnd_2017566 : Nat := 1035981110169158497446389

theorem tailTrace_2017566 : CollatzResearch.WordTrace tailWord_2017566 prefixEnd_2017566 1035981110169158497446389 := by
  unfold tailWord_2017566
  simp only [CollatzResearch.WordTrace]
  refine ⟨9198334676088803710633069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49057784939140286456709701 9198334676088803710633069)
  ·
    refine ⟨3449375503533301391487401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9198334676088803710633069 3449375503533301391487401)
    ·
      refine ⟨2587031627649976043615551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3449375503533301391487401 2587031627649976043615551)
      ·
        refine ⟨3880547441474964065423327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2587031627649976043615551 3880547441474964065423327)
        ·
          refine ⟨5820821162212446098134991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3880547441474964065423327 5820821162212446098134991)
          ·
            refine ⟨8731231743318669147202487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5820821162212446098134991 8731231743318669147202487)
            ·
              refine ⟨13096847614978003720803731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8731231743318669147202487 13096847614978003720803731)
              ·
                refine ⟨19645271422467005581205597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13096847614978003720803731 19645271422467005581205597)
                ·
                  refine ⟨7366976783425127092952099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19645271422467005581205597 7366976783425127092952099)
                  ·
                    refine ⟨11050465175137690639428149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7366976783425127092952099 11050465175137690639428149)
                    ·
                      refine ⟨1035981110169158497446389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11050465175137690639428149 1035981110169158497446389)
                      ·
                        rfl

theorem cell23_2017566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_2017566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017566 prefixEnd_2017566 := by exact prefixLift 2017566
  have htrace : WordTrace (prefixWord ++ tailWord_2017566) baseStart_2017566 baseEnd_2017566 := by
    simpa [prefixWord, tailWord_2017566, baseEnd_2017566] using wordTrace_append hprefix tailTrace_2017566
  have hstable : (prefixWord ++ tailWord_2017566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017566).length < 2 ^ (prefixWord ++ tailWord_2017566).sum := by decide
  have hdescent : baseEnd_2017566 < baseStart_2017566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017573 : List Nat := [1, 3, 1, 2, 5, 1, 3, 1, 2, 4]
def baseStart_2017573 : Nat := 118140960795 + 2017573 * 2 ^ 59
def prefixEnd_2017573 : Nat := 4983230072969 + 3 ^ 40 * 2017573 * 2
def baseEnd_2017573 : Nat := 345328234844579990019619

theorem tailTrace_2017573 : CollatzResearch.WordTrace tailWord_2017573 prefixEnd_2017573 345328234844579990019619 := by
  unfold tailWord_2017573
  simp only [CollatzResearch.WordTrace]
  refine ⟨73586932719685069880569373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49057955146456713253712915 73586932719685069880569373)
  ·
    refine ⟨27595099769881901205213515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73586932719685069880569373 27595099769881901205213515)
    ·
      refine ⟨41392649654822851807820273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27595099769881901205213515 41392649654822851807820273)
      ·
        refine ⟨31044487241117138855865205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41392649654822851807820273 31044487241117138855865205)
        ·
          refine ⟨2910420678854731767737363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31044487241117138855865205 2910420678854731767737363)
          ·
            refine ⟨4365631018282097651606045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2910420678854731767737363 4365631018282097651606045)
            ·
              refine ⟨1637111631855786619352267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4365631018282097651606045 1637111631855786619352267)
              ·
                refine ⟨2455667447783679929028401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1637111631855786619352267 2455667447783679929028401)
                ·
                  refine ⟨1841750585837759946771301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2455667447783679929028401 1841750585837759946771301)
                  ·
                    refine ⟨345328234844579990019619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1841750585837759946771301 345328234844579990019619)
                    ·
                      rfl

theorem cell23_2017573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 2, 4].length) (baseStart_2017573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017573 prefixEnd_2017573 := by exact prefixLift 2017573
  have htrace : WordTrace (prefixWord ++ tailWord_2017573) baseStart_2017573 baseEnd_2017573 := by
    simpa [prefixWord, tailWord_2017573, baseEnd_2017573] using wordTrace_append hprefix tailTrace_2017573
  have hstable : (prefixWord ++ tailWord_2017573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017573).length < 2 ^ (prefixWord ++ tailWord_2017573).sum := by decide
  have hdescent : baseEnd_2017573 < baseStart_2017573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017586 : List Nat := [3, 2, 1, 1, 5, 2, 2, 7]
def baseStart_2017586 : Nat := 118140960795 + 2017586 * 2 ^ 59
def prefixEnd_2017586 : Nat := 4983230072969 + 3 ^ 40 * 2017586 * 2
def baseEnd_2017586 : Nat := 38370051103046237748011

theorem tailTrace_2017586 : CollatzResearch.WordTrace tailWord_2017586 prefixEnd_2017586 38370051103046237748011 := by
  unfold tailWord_2017586
  simp only [CollatzResearch.WordTrace]
  refine ⟨18396851717159493275198153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49058271245758648733861741 18396851717159493275198153)
  ·
    refine ⟨13797638787869619956398615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18396851717159493275198153 13797638787869619956398615)
    ·
      refine ⟨20696458181804429934597923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13797638787869619956398615 20696458181804429934597923)
      ·
        refine ⟨31044687272706644901896885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20696458181804429934597923 31044687272706644901896885)
        ·
          refine ⟨2910439431816247959552833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31044687272706644901896885 2910439431816247959552833)
          ·
            refine ⟨2182829573862185969664625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2910439431816247959552833 2182829573862185969664625)
            ·
              refine ⟨1637122180396639477248469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2182829573862185969664625 1637122180396639477248469)
              ·
                refine ⟨38370051103046237748011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1637122180396639477248469 38370051103046237748011)
                ·
                  rfl

theorem cell23_2017586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 7].length) (baseStart_2017586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017586 prefixEnd_2017586 := by exact prefixLift 2017586
  have htrace : WordTrace (prefixWord ++ tailWord_2017586) baseStart_2017586 baseEnd_2017586 := by
    simpa [prefixWord, tailWord_2017586, baseEnd_2017586] using wordTrace_append hprefix tailTrace_2017586
  have hstable : (prefixWord ++ tailWord_2017586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017586).length < 2 ^ (prefixWord ++ tailWord_2017586).sum := by decide
  have hdescent : baseEnd_2017586 < baseStart_2017586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017592 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 2, 2, 5]
def baseStart_2017592 : Nat := 118140960795 + 2017592 * 2 ^ 59
def prefixEnd_2017592 : Nat := 4983230072969 + 3 ^ 40 * 2017592 * 2
def baseEnd_2017592 : Nat := 1035994460666175395721269

theorem tailTrace_2017592 : CollatzResearch.WordTrace tailWord_2017592 prefixEnd_2017592 1035994460666175395721269 := by
  unfold tailWord_2017592
  simp only [CollatzResearch.WordTrace]
  refine ⟨36793812853308118062755515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49058417137744157417007353 36793812853308118062755515)
  ·
    refine ⟨55190719279962177094133273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36793812853308118062755515 55190719279962177094133273)
    ·
      refine ⟨41393039459971632820599955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55190719279962177094133273 41393039459971632820599955)
      ·
        refine ⟨62089559189957449230899933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41393039459971632820599955 62089559189957449230899933)
        ·
          refine ⟨23283584696234043461587475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62089559189957449230899933 23283584696234043461587475)
          ·
            refine ⟨34925377044351065192381213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23283584696234043461587475 34925377044351065192381213)
            ·
              refine ⟨13097016391631649447142955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34925377044351065192381213 13097016391631649447142955)
              ·
                refine ⟨19645524587447474170714433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13097016391631649447142955 19645524587447474170714433)
                ·
                  refine ⟨14734143440585605628035825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19645524587447474170714433 14734143440585605628035825)
                  ·
                    refine ⟨11050607580439204221026869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14734143440585605628035825 11050607580439204221026869)
                    ·
                      refine ⟨1035994460666175395721269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11050607580439204221026869 1035994460666175395721269)
                      ·
                        rfl

theorem cell23_2017592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_2017592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017592 prefixEnd_2017592 := by exact prefixLift 2017592
  have htrace : WordTrace (prefixWord ++ tailWord_2017592) baseStart_2017592 baseEnd_2017592 := by
    simpa [prefixWord, tailWord_2017592, baseEnd_2017592] using wordTrace_append hprefix tailTrace_2017592
  have hstable : (prefixWord ++ tailWord_2017592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017592).length < 2 ^ (prefixWord ++ tailWord_2017592).sum := by decide
  have hdescent : baseEnd_2017592 < baseStart_2017592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017619 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 5, 4, 2]
def baseStart_2017619 : Nat := 118140960795 + 2017619 * 2 ^ 59
def prefixEnd_2017619 : Nat := 4983230072969 + 3 ^ 40 * 2017619 * 2
def baseEnd_2017619 : Nat := 1036008324643846790083645

theorem tailTrace_2017619 : CollatzResearch.WordTrace tailWord_2017619 prefixEnd_2017619 1036008324643846790083645 := by
  unfold tailWord_2017619
  simp only [CollatzResearch.WordTrace]
  refine ⟨73588610477518419736743911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49059073651678946491162607 73588610477518419736743911)
  ·
    refine ⟨110382915716277629605115867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73588610477518419736743911 110382915716277629605115867)
    ·
      refine ⟨165574373574416444407673801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110382915716277629605115867 165574373574416444407673801)
      ·
        refine ⟨124180780180812333305755351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165574373574416444407673801 124180780180812333305755351)
        ·
          refine ⟨186271170271218499958633027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124180780180812333305755351 186271170271218499958633027)
          ·
            refine ⟨279406755406827749937949541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186271170271218499958633027 279406755406827749937949541)
            ·
              refine ⟨52388766638780203113365539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 279406755406827749937949541 52388766638780203113365539)
              ·
                refine ⟨78583149958170304670048309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52388766638780203113365539 78583149958170304670048309)
                ·
                  refine ⟨7367170308578466062817029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78583149958170304670048309 7367170308578466062817029)
                  ·
                    refine ⟨1381344432858462386778193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7367170308578466062817029 1381344432858462386778193)
                    ·
                      refine ⟨1036008324643846790083645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1381344432858462386778193 1036008324643846790083645)
                      ·
                        rfl

theorem cell23_2017619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 4, 2].length) (baseStart_2017619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017619 prefixEnd_2017619 := by exact prefixLift 2017619
  have htrace : WordTrace (prefixWord ++ tailWord_2017619) baseStart_2017619 baseEnd_2017619 := by
    simpa [prefixWord, tailWord_2017619, baseEnd_2017619] using wordTrace_append hprefix tailTrace_2017619
  have hstable : (prefixWord ++ tailWord_2017619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017619).length < 2 ^ (prefixWord ++ tailWord_2017619).sum := by decide
  have hdescent : baseEnd_2017619 < baseStart_2017619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017636 : List Nat := [2, 3, 1, 1, 3, 1, 2, 3, 1, 4, 2]
def baseStart_2017636 : Nat := 118140960795 + 2017636 * 2 ^ 59
def prefixEnd_2017636 : Nat := 4983230072969 + 3 ^ 40 * 2017636 * 2
def baseEnd_2017636 : Nat := 1036017053814973223571067

theorem tailTrace_2017636 : CollatzResearch.WordTrace tailWord_2017636 prefixEnd_2017636 1036017053814973223571067 := by
  unfold tailWord_2017636
  simp only [CollatzResearch.WordTrace]
  refine ⟨36794615259228415820056381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49059487012304554426741841 36794615259228415820056381)
  ·
    refine ⟨13797980722210655932521143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36794615259228415820056381 13797980722210655932521143)
    ·
      refine ⟨20696971083315983898781715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13797980722210655932521143 20696971083315983898781715)
      ·
        refine ⟨31045456624973975848172573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20696971083315983898781715 31045456624973975848172573)
        ·
          refine ⟨11642046234365240943064715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31045456624973975848172573 11642046234365240943064715)
          ·
            refine ⟨17463069351547861414597073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11642046234365240943064715 17463069351547861414597073)
            ·
              refine ⟨13097302013660896060947805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17463069351547861414597073 13097302013660896060947805)
              ·
                refine ⟨4911488255122836022855427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13097302013660896060947805 4911488255122836022855427)
                ·
                  refine ⟨7367232382684254034283141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4911488255122836022855427 7367232382684254034283141)
                  ·
                    refine ⟨1381356071753297631428089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7367232382684254034283141 1381356071753297631428089)
                    ·
                      refine ⟨1036017053814973223571067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1381356071753297631428089 1036017053814973223571067)
                      ·
                        rfl

theorem cell23_2017636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 1, 4, 2].length) (baseStart_2017636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017636 prefixEnd_2017636 := by exact prefixLift 2017636
  have htrace : WordTrace (prefixWord ++ tailWord_2017636) baseStart_2017636 baseEnd_2017636 := by
    simpa [prefixWord, tailWord_2017636, baseEnd_2017636] using wordTrace_append hprefix tailTrace_2017636
  have hstable : (prefixWord ++ tailWord_2017636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017636).length < 2 ^ (prefixWord ++ tailWord_2017636).sum := by decide
  have hdescent : baseEnd_2017636 < baseStart_2017636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017639 : List Nat := [1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_2017639 : Nat := 118140960795 + 2017639 * 2 ^ 59
def prefixEnd_2017639 : Nat := 4983230072969 + 3 ^ 40 * 2017639 * 2
def baseEnd_2017639 : Nat := 1036018594256936711833553

theorem tailTrace_2017639 : CollatzResearch.WordTrace tailWord_2017639 prefixEnd_2017639 1036018594256936711833553 := by
  unfold tailWord_2017639
  simp only [CollatzResearch.WordTrace]
  refine ⟨73589339937445963152471971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49059559958297308768314647 73589339937445963152471971)
  ·
    refine ⟨110384009906168944728707957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73589339937445963152471971 110384009906168944728707957)
    ·
      refine ⟨10348500928703338568316371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110384009906168944728707957 10348500928703338568316371)
      ·
        refine ⟨15522751393055007852474557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10348500928703338568316371 15522751393055007852474557)
        ·
          refine ⟨5821031772395627944677959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15522751393055007852474557 5821031772395627944677959)
          ·
            refine ⟨8731547658593441917016939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5821031772395627944677959 8731547658593441917016939)
            ·
              refine ⟨13097321487890162875525409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8731547658593441917016939 13097321487890162875525409)
              ·
                refine ⟨9822991115917622156644057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13097321487890162875525409 9822991115917622156644057)
                ·
                  refine ⟨7367243336938216617483043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9822991115917622156644057 7367243336938216617483043)
                  ·
                    refine ⟨11050865005407324926224565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7367243336938216617483043 11050865005407324926224565)
                    ·
                      refine ⟨1036018594256936711833553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11050865005407324926224565 1036018594256936711833553)
                      ·
                        rfl

theorem cell23_2017639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_2017639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017639 prefixEnd_2017639 := by exact prefixLift 2017639
  have htrace : WordTrace (prefixWord ++ tailWord_2017639) baseStart_2017639 baseEnd_2017639 := by
    simpa [prefixWord, tailWord_2017639, baseEnd_2017639] using wordTrace_append hprefix tailTrace_2017639
  have hstable : (prefixWord ++ tailWord_2017639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017639).length < 2 ^ (prefixWord ++ tailWord_2017639).sum := by decide
  have hdescent : baseEnd_2017639 < baseStart_2017639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017640 : List Nat := [2, 1, 4, 2, 2, 3, 1, 2, 1, 3, 2]
def baseStart_2017640 : Nat := 118140960795 + 2017640 * 2 ^ 59
def prefixEnd_2017640 : Nat := 4983230072969 + 3 ^ 40 * 2017640 * 2
def baseEnd_2017640 : Nat := 1036019107737591207921049

theorem tailTrace_2017640 : CollatzResearch.WordTrace tailWord_2017640 prefixEnd_2017640 1036019107737591207921049 := by
  unfold tailWord_2017640
  simp only [CollatzResearch.WordTrace]
  refine ⟨36794688205221170161629187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49059584273628226882172249 36794688205221170161629187)
  ·
    refine ⟨55192032307831755242443781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36794688205221170161629187 55192032307831755242443781)
    ·
      refine ⟨10348506057718454107958209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55192032307831755242443781 10348506057718454107958209)
      ·
        refine ⟨7761379543288840580968657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10348506057718454107958209 7761379543288840580968657)
        ·
          refine ⟨5821034657466630435726493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7761379543288840580968657 5821034657466630435726493)
          ·
            refine ⟨2182887996549986413397435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5821034657466630435726493 2182887996549986413397435)
            ·
              refine ⟨3274331994824979620096153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2182887996549986413397435 3274331994824979620096153)
              ·
                refine ⟨2455748996118734715072115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3274331994824979620096153 2455748996118734715072115)
                ·
                  refine ⟨3683623494178102072608173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2455748996118734715072115 3683623494178102072608173)
                  ·
                    refine ⟨1381358810316788277228065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3683623494178102072608173 1381358810316788277228065)
                    ·
                      refine ⟨1036019107737591207921049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1381358810316788277228065 1036019107737591207921049)
                      ·
                        rfl

theorem cell23_2017640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_2017640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017640 prefixEnd_2017640 := by exact prefixLift 2017640
  have htrace : WordTrace (prefixWord ++ tailWord_2017640) baseStart_2017640 baseEnd_2017640 := by
    simpa [prefixWord, tailWord_2017640, baseEnd_2017640] using wordTrace_append hprefix tailTrace_2017640
  have hstable : (prefixWord ++ tailWord_2017640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017640).length < 2 ^ (prefixWord ++ tailWord_2017640).sum := by decide
  have hdescent : baseEnd_2017640 < baseStart_2017640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017653 : List Nat := [1, 3, 4, 1, 2, 2, 1, 2, 1, 4, 2]
def baseStart_2017653 : Nat := 118140960795 + 2017653 * 2 ^ 59
def prefixEnd_2017653 : Nat := 4983230072969 + 3 ^ 40 * 2017653 * 2
def baseEnd_2017653 : Nat := 1036025782986099657058489

theorem tailTrace_2017653 : CollatzResearch.WordTrace tailWord_2017653 prefixEnd_2017653 1036025782986099657058489 := by
  unfold tailWord_2017653
  simp only [CollatzResearch.WordTrace]
  refine ⟨73589850559395243543481613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49059900372930162362321075 73589850559395243543481613)
  ·
    refine ⟨27596193959773216328805605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73589850559395243543481613 27596193959773216328805605)
    ·
      refine ⟨5174286367457478061651051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27596193959773216328805605 5174286367457478061651051)
      ·
        refine ⟨7761429551186217092476577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5174286367457478061651051 7761429551186217092476577)
        ·
          refine ⟨5821072163389662819357433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7761429551186217092476577 5821072163389662819357433)
          ·
            refine ⟨4365804122542247114518075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5821072163389662819357433 4365804122542247114518075)
            ·
              refine ⟨6548706183813370671777113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4365804122542247114518075 6548706183813370671777113)
              ·
                refine ⟨4911529637860028003832835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6548706183813370671777113 4911529637860028003832835)
                ·
                  refine ⟨7367294456790042005749253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4911529637860028003832835 7367294456790042005749253)
                  ·
                    refine ⟨1381367710648132876077985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7367294456790042005749253 1381367710648132876077985)
                    ·
                      refine ⟨1036025782986099657058489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1381367710648132876077985 1036025782986099657058489)
                      ·
                        rfl

theorem cell23_2017653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_2017653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017653 prefixEnd_2017653 := by exact prefixLift 2017653
  have htrace : WordTrace (prefixWord ++ tailWord_2017653) baseStart_2017653 baseEnd_2017653 := by
    simpa [prefixWord, tailWord_2017653, baseEnd_2017653] using wordTrace_append hprefix tailTrace_2017653
  have hstable : (prefixWord ++ tailWord_2017653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017653).length < 2 ^ (prefixWord ++ tailWord_2017653).sum := by decide
  have hdescent : baseEnd_2017653 < baseStart_2017653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017669 : List Nat := [1, 3, 1, 1, 3, 1, 1, 4, 2, 3, 3]
def baseStart_2017669 : Nat := 118140960795 + 2017669 * 2 ^ 59
def prefixEnd_2017669 : Nat := 4983230072969 + 3 ^ 40 * 2017669 * 2
def baseEnd_2017669 : Nat := 1036033998676571594458415

theorem tailTrace_2017669 : CollatzResearch.WordTrace tailWord_2017669 prefixEnd_2017669 1036033998676571594458415 := by
  unfold tailWord_2017669
  simp only [CollatzResearch.WordTrace]
  refine ⟨73590434127337278276064061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49060289418224852184042707 73590434127337278276064061)
  ·
    refine ⟨27596412797751479353524023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73590434127337278276064061 27596412797751479353524023)
    ·
      refine ⟨41394619196627219030286035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27596412797751479353524023 41394619196627219030286035)
      ·
        refine ⟨62091928794940828545429053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41394619196627219030286035 62091928794940828545429053)
        ·
          refine ⟨23284473298102810704535895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62091928794940828545429053 23284473298102810704535895)
          ·
            refine ⟨34926709947154216056803843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23284473298102810704535895 34926709947154216056803843)
            ·
              refine ⟨52390064920731324085205765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34926709947154216056803843 52390064920731324085205765)
              ·
                refine ⟨9823137172637123265976081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52390064920731324085205765 9823137172637123265976081)
                ·
                  refine ⟨7367352879477842449482061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9823137172637123265976081 7367352879477842449482061)
                  ·
                    refine ⟨2762757329804190918555773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7367352879477842449482061 2762757329804190918555773)
                    ·
                      refine ⟨1036033998676571594458415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2762757329804190918555773 1036033998676571594458415)
                      ·
                        rfl

theorem cell23_2017669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 3, 3].length) (baseStart_2017669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017669 prefixEnd_2017669 := by exact prefixLift 2017669
  have htrace : WordTrace (prefixWord ++ tailWord_2017669) baseStart_2017669 baseEnd_2017669 := by
    simpa [prefixWord, tailWord_2017669, baseEnd_2017669] using wordTrace_append hprefix tailTrace_2017669
  have hstable : (prefixWord ++ tailWord_2017669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017669).length < 2 ^ (prefixWord ++ tailWord_2017669).sum := by decide
  have hdescent : baseEnd_2017669 < baseStart_2017669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017676 : List Nat := [2, 2, 1, 2, 1, 5, 1, 4, 5]
def baseStart_2017676 : Nat := 118140960795 + 2017676 * 2 ^ 59
def prefixEnd_2017676 : Nat := 4983230072969 + 3 ^ 40 * 2017676 * 2
def baseEnd_2017676 : Nat := 115115288115683674118987

theorem tailTrace_2017676 : CollatzResearch.WordTrace tailWord_2017676 prefixEnd_2017676 115115288115683674118987 := by
  unfold tailWord_2017676
  simp only [CollatzResearch.WordTrace]
  refine ⟨36795344719155959235784441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49060459625541278981045921 36795344719155959235784441)
  ·
    refine ⟨27596508539366969426838331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36795344719155959235784441 27596508539366969426838331)
    ·
      refine ⟨41394762809050454140257497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27596508539366969426838331 41394762809050454140257497)
      ·
        refine ⟨31046072106787840605193123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41394762809050454140257497 31046072106787840605193123)
        ·
          refine ⟨46569108160181760907789685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31046072106787840605193123 46569108160181760907789685)
          ·
            refine ⟨4365853890017040085105283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46569108160181760907789685 4365853890017040085105283)
            ·
              refine ⟨6548780835025560127657925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4365853890017040085105283 6548780835025560127657925)
              ·
                refine ⟨1227896406567292523935861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6548780835025560127657925 1227896406567292523935861)
                ·
                  refine ⟨115115288115683674118987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1227896406567292523935861 115115288115683674118987)
                  ·
                    rfl

theorem cell23_2017676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4, 5].length) (baseStart_2017676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017676 prefixEnd_2017676 := by exact prefixLift 2017676
  have htrace : WordTrace (prefixWord ++ tailWord_2017676) baseStart_2017676 baseEnd_2017676 := by
    simpa [prefixWord, tailWord_2017676, baseEnd_2017676] using wordTrace_append hprefix tailTrace_2017676
  have hstable : (prefixWord ++ tailWord_2017676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017676).length < 2 ^ (prefixWord ++ tailWord_2017676).sum := by decide
  have hdescent : baseEnd_2017676 < baseStart_2017676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017726 : List Nat := [4, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_2017726 : Nat := 118140960795 + 2017726 * 2 ^ 59
def prefixEnd_2017726 : Nat := 4983230072969 + 3 ^ 40 * 2017726 * 2
def baseEnd_2017726 : Nat := 1036063267073877871445653

theorem tailTrace_2017726 : CollatzResearch.WordTrace tailWord_2017726 prefixEnd_2017726 1036063267073877871445653 := by
  unfold tailWord_2017726
  simp only [CollatzResearch.WordTrace]
  refine ⟨9199064136016347126361129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49061675392087184673926021 9199064136016347126361129)
  ·
    refine ⟨6899298102012260344770847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9199064136016347126361129 6899298102012260344770847)
    ·
      refine ⟨10348947153018390517156271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6899298102012260344770847 10348947153018390517156271)
      ·
        refine ⟨15523420729527585775734407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10348947153018390517156271 15523420729527585775734407)
        ·
          refine ⟨23285131094291378663601611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15523420729527585775734407 23285131094291378663601611)
          ·
            refine ⟨34927696641437067995402417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23285131094291378663601611 34927696641437067995402417)
            ·
              refine ⟨26195772481077800996551813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34927696641437067995402417 26195772481077800996551813)
              ·
                refine ⟨4911707340202087686853465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26195772481077800996551813 4911707340202087686853465)
                ·
                  refine ⟨3683780505151565765140099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4911707340202087686853465 3683780505151565765140099)
                  ·
                    refine ⟨5525670757727348647710149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3683780505151565765140099 5525670757727348647710149)
                    ·
                      refine ⟨1036063267073877871445653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5525670757727348647710149 1036063267073877871445653)
                      ·
                        rfl

theorem cell23_2017726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_2017726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017726 prefixEnd_2017726 := by exact prefixLift 2017726
  have htrace : WordTrace (prefixWord ++ tailWord_2017726) baseStart_2017726 baseEnd_2017726 := by
    simpa [prefixWord, tailWord_2017726, baseEnd_2017726] using wordTrace_append hprefix tailTrace_2017726
  have hstable : (prefixWord ++ tailWord_2017726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017726).length < 2 ^ (prefixWord ++ tailWord_2017726).sum := by decide
  have hdescent : baseEnd_2017726 < baseStart_2017726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017736 : List Nat := [2, 1, 3, 1, 3, 2, 1, 3, 3, 4]
def baseStart_2017736 : Nat := 118140960795 + 2017736 * 2 ^ 59
def prefixEnd_2017736 : Nat := 4983230072969 + 3 ^ 40 * 2017736 * 2
def baseEnd_2017736 : Nat := 345356133960140944106869

theorem tailTrace_2017736 : CollatzResearch.WordTrace tailWord_2017736 prefixEnd_2017736 345356133960140944106869 := by
  unfold tailWord_2017736
  simp only [CollatzResearch.WordTrace]
  refine ⟨36796438909047274359376531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49061918545396365812502041 36796438909047274359376531)
  ·
    refine ⟨55194658363570911539064797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36796438909047274359376531 55194658363570911539064797)
    ·
      refine ⟨20697996886339091827149299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55194658363570911539064797 20697996886339091827149299)
      ·
        refine ⟨31046995329508637740723949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20697996886339091827149299 31046995329508637740723949)
        ·
          refine ⟨11642623248565739152771481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31046995329508637740723949 11642623248565739152771481)
          ·
            refine ⟨8731967436424304364578611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11642623248565739152771481 8731967436424304364578611)
            ·
              refine ⟨13097951154636456546867917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8731967436424304364578611 13097951154636456546867917)
              ·
                refine ⟨4911731682988671205075469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13097951154636456546867917 4911731682988671205075469)
                ·
                  refine ⟨1841899381120751701903301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4911731682988671205075469 1841899381120751701903301)
                  ·
                    refine ⟨345356133960140944106869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1841899381120751701903301 345356133960140944106869)
                    ·
                      rfl

theorem cell23_2017736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_2017736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017736 prefixEnd_2017736 := by exact prefixLift 2017736
  have htrace : WordTrace (prefixWord ++ tailWord_2017736) baseStart_2017736 baseEnd_2017736 := by
    simpa [prefixWord, tailWord_2017736, baseEnd_2017736] using wordTrace_append hprefix tailTrace_2017736
  have hstable : (prefixWord ++ tailWord_2017736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017736).length < 2 ^ (prefixWord ++ tailWord_2017736).sum := by decide
  have hdescent : baseEnd_2017736 < baseStart_2017736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017770 : List Nat := [3, 1, 3, 1, 3, 1, 3, 3, 1, 4]
def baseStart_2017770 : Nat := 118140960795 + 2017770 * 2 ^ 59
def prefixEnd_2017770 : Nat := 4983230072969 + 3 ^ 40 * 2017770 * 2
def baseEnd_2017770 : Nat := 345361953407558566431817

theorem tailTrace_2017770 : CollatzResearch.WordTrace tailWord_2017770 prefixEnd_2017770 345361953407558566431817 := by
  unfold tailWord_2017770
  simp only [CollatzResearch.WordTrace]
  refine ⟨18398529474992843131372691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49062745266647581683660509 18398529474992843131372691)
  ·
    refine ⟨27597794212489264697059037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18398529474992843131372691 27597794212489264697059037)
    ·
      refine ⟨10349172829683474261397139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27597794212489264697059037 10349172829683474261397139)
      ·
        refine ⟨15523759244525211392095709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10349172829683474261397139 15523759244525211392095709)
        ·
          refine ⟨5821409716696954272035891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15523759244525211392095709 5821409716696954272035891)
          ·
            refine ⟨8732114575045431408053837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5821409716696954272035891 8732114575045431408053837)
            ·
              refine ⟨3274542965642036778020189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8732114575045431408053837 3274542965642036778020189)
              ·
                refine ⟨1227953612115763791757571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3274542965642036778020189 1227953612115763791757571)
                ·
                  refine ⟨1841930418173645687636357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1227953612115763791757571 1841930418173645687636357)
                  ·
                    refine ⟨345361953407558566431817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1841930418173645687636357 345361953407558566431817)
                    ·
                      rfl

theorem cell23_2017770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_2017770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017770 prefixEnd_2017770 := by exact prefixLift 2017770
  have htrace : WordTrace (prefixWord ++ tailWord_2017770) baseStart_2017770 baseEnd_2017770 := by
    simpa [prefixWord, tailWord_2017770, baseEnd_2017770] using wordTrace_append hprefix tailTrace_2017770
  have hstable : (prefixWord ++ tailWord_2017770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017770).length < 2 ^ (prefixWord ++ tailWord_2017770).sum := by decide
  have hdescent : baseEnd_2017770 < baseStart_2017770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017786 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2]
def baseStart_2017786 : Nat := 118140960795 + 2017786 * 2 ^ 59
def prefixEnd_2017786 : Nat := 4983230072969 + 3 ^ 40 * 2017786 * 2
def baseEnd_2017786 : Nat := 1036094075913147636695377

theorem tailTrace_2017786 : CollatzResearch.WordTrace tailWord_2017786 prefixEnd_2017786 1036094075913147636695377 := by
  unfold tailWord_2017786
  simp only [CollatzResearch.WordTrace]
  refine ⟨18398675366978351814518303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49063134311942271505382141 18398675366978351814518303)
  ·
    refine ⟨27598013050467527721777455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18398675366978351814518303 27598013050467527721777455)
    ·
      refine ⟨41397019575701291582666183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27598013050467527721777455 41397019575701291582666183)
      ·
        refine ⟨62095529363551937373999275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41397019575701291582666183 62095529363551937373999275)
        ·
          refine ⟨93143294045327906060998913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62095529363551937373999275 93143294045327906060998913)
          ·
            refine ⟨69857470533995929545749185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93143294045327906060998913 69857470533995929545749185)
            ·
              refine ⟨52393102900496947159311889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69857470533995929545749185 52393102900496947159311889)
              ·
                refine ⟨39294827175372710369483917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52393102900496947159311889 39294827175372710369483917)
                ·
                  refine ⟨14735560190764766388556469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39294827175372710369483917 14735560190764766388556469)
                  ·
                    refine ⟨1381458767884196848927169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14735560190764766388556469 1381458767884196848927169)
                    ·
                      refine ⟨1036094075913147636695377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1381458767884196848927169 1036094075913147636695377)
                      ·
                        rfl

theorem cell23_2017786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2].length) (baseStart_2017786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017786 prefixEnd_2017786 := by exact prefixLift 2017786
  have htrace : WordTrace (prefixWord ++ tailWord_2017786) baseStart_2017786 baseEnd_2017786 := by
    simpa [prefixWord, tailWord_2017786, baseEnd_2017786] using wordTrace_append hprefix tailTrace_2017786
  have hstable : (prefixWord ++ tailWord_2017786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017786).length < 2 ^ (prefixWord ++ tailWord_2017786).sum := by decide
  have hdescent : baseEnd_2017786 < baseStart_2017786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017820 : List Nat := [2, 2, 3, 1, 2, 3, 2, 1, 2, 3, 2]
def baseStart_2017820 : Nat := 118140960795 + 2017820 * 2 ^ 59
def prefixEnd_2017820 : Nat := 4983230072969 + 3 ^ 40 * 2017820 * 2
def baseEnd_2017820 : Nat := 1036111534255400503670221

theorem tailTrace_2017820 : CollatzResearch.WordTrace tailWord_2017820 prefixEnd_2017820 1036111534255400503670221 := by
  unfold tailWord_2017820
  simp only [CollatzResearch.WordTrace]
  refine ⟨36797970774895115532405457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49063961033193487376540609 36797970774895115532405457)
  ·
    refine ⟨27598478081171336649304093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36797970774895115532405457 27598478081171336649304093)
    ·
      refine ⟨10349429280439251243489035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27598478081171336649304093 10349429280439251243489035)
      ·
        refine ⟨15524143920658876865233553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10349429280439251243489035 15524143920658876865233553)
        ·
          refine ⟨11643107940494157648925165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15524143920658876865233553 11643107940494157648925165)
          ·
            refine ⟨4366165477685309118346937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11643107940494157648925165 4366165477685309118346937)
            ·
              refine ⟨3274624108263981838760203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4366165477685309118346937 3274624108263981838760203)
              ·
                refine ⟨4911936162395972758140305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3274624108263981838760203 4911936162395972758140305)
                ·
                  refine ⟨3683952121796979568605229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4911936162395972758140305 3683952121796979568605229)
                  ·
                    refine ⟨1381482045673867338226961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3683952121796979568605229 1381482045673867338226961)
                    ·
                      refine ⟨1036111534255400503670221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1381482045673867338226961 1036111534255400503670221)
                      ·
                        rfl

theorem cell23_2017820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_2017820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017820 prefixEnd_2017820 := by exact prefixLift 2017820
  have htrace : WordTrace (prefixWord ++ tailWord_2017820) baseStart_2017820 baseEnd_2017820 := by
    simpa [prefixWord, tailWord_2017820, baseEnd_2017820] using wordTrace_append hprefix tailTrace_2017820
  have hstable : (prefixWord ++ tailWord_2017820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017820).length < 2 ^ (prefixWord ++ tailWord_2017820).sum := by decide
  have hdescent : baseEnd_2017820 < baseStart_2017820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017843 : List Nat := [1, 1, 1, 2, 4, 2, 4, 2, 2, 4]
def baseStart_2017843 : Nat := 118140960795 + 2017843 * 2 ^ 59
def prefixEnd_2017843 : Nat := 4983230072969 + 3 ^ 40 * 2017843 * 2
def baseEnd_2017843 : Nat := 345374448103484637894205

theorem tailTrace_2017843 : CollatzResearch.WordTrace tailWord_2017843 prefixEnd_2017843 345374448103484637894205 := by
  unfold tailWord_2017843
  simp only [CollatzResearch.WordTrace]
  refine ⟨73596780428706905992898183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49064520285804603995265455 73596780428706905992898183)
  ·
    refine ⟨110395170643060358989347275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73596780428706905992898183 110395170643060358989347275)
    ·
      refine ⟨165592755964590538484020913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110395170643060358989347275 165592755964590538484020913)
      ·
        refine ⟨124194566973442903863015685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165592755964590538484020913 124194566973442903863015685)
        ·
          refine ⟨23286481307520544474315441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124194566973442903863015685 23286481307520544474315441)
          ·
            refine ⟨17464860980640408355736581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23286481307520544474315441 17464860980640408355736581)
            ·
              refine ⟨3274661433870076566700609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17464860980640408355736581 3274661433870076566700609)
              ·
                refine ⟨2455996075402557425025457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3274661433870076566700609 2455996075402557425025457)
                ·
                  refine ⟨1841997056551918068769093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2455996075402557425025457 1841997056551918068769093)
                  ·
                    refine ⟨345374448103484637894205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1841997056551918068769093 345374448103484637894205)
                    ·
                      rfl

theorem cell23_2017843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2, 4].length) (baseStart_2017843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017843 prefixEnd_2017843 := by exact prefixLift 2017843
  have htrace : WordTrace (prefixWord ++ tailWord_2017843) baseStart_2017843 baseEnd_2017843 := by
    simpa [prefixWord, tailWord_2017843, baseEnd_2017843] using wordTrace_append hprefix tailTrace_2017843
  have hstable : (prefixWord ++ tailWord_2017843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017843).length < 2 ^ (prefixWord ++ tailWord_2017843).sum := by decide
  have hdescent : baseEnd_2017843 < baseStart_2017843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017853 : List Nat := [1, 4, 1, 3, 2, 1, 1, 2, 3, 2, 3]
def baseStart_2017853 : Nat := 118140960795 + 2017853 * 2 ^ 59
def prefixEnd_2017853 : Nat := 4983230072969 + 3 ^ 40 * 2017853 * 2
def baseEnd_2017853 : Nat := 1036128479116998874557569

theorem tailTrace_2017853 : CollatzResearch.WordTrace tailWord_2017853 prefixEnd_2017853 1036128479116998874557569 := by
  unfold tailWord_2017853
  simp only [CollatzResearch.WordTrace]
  refine ⟨73597145158670677700762213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49064763439113785133841475 73597145158670677700762213)
  ·
    refine ⟨13799464717250752068892915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73597145158670677700762213 13799464717250752068892915)
    ·
      refine ⟨20699197075876128103339373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13799464717250752068892915 20699197075876128103339373)
      ·
        refine ⟨7762198903453548038752265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20699197075876128103339373 7762198903453548038752265)
        ·
          refine ⟨5821649177590161029064199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7762198903453548038752265 5821649177590161029064199)
          ·
            refine ⟨8732473766385241543596299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5821649177590161029064199 8732473766385241543596299)
            ·
              refine ⟨13098710649577862315394449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8732473766385241543596299 13098710649577862315394449)
              ·
                refine ⟨9824032987183396736545837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13098710649577862315394449 9824032987183396736545837)
                ·
                  refine ⟨3684012370193773776204689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9824032987183396736545837 3684012370193773776204689)
                  ·
                    refine ⟨2763009277645330332153517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3684012370193773776204689 2763009277645330332153517)
                    ·
                      refine ⟨1036128479116998874557569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2763009277645330332153517 1036128479116998874557569)
                      ·
                        rfl

theorem cell23_2017853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_2017853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017853 prefixEnd_2017853 := by exact prefixLift 2017853
  have htrace : WordTrace (prefixWord ++ tailWord_2017853) baseStart_2017853 baseEnd_2017853 := by
    simpa [prefixWord, tailWord_2017853, baseEnd_2017853] using wordTrace_append hprefix tailTrace_2017853
  have hstable : (prefixWord ++ tailWord_2017853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017853).length < 2 ^ (prefixWord ++ tailWord_2017853).sum := by decide
  have hdescent : baseEnd_2017853 < baseStart_2017853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017859 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 6]
def baseStart_2017859 : Nat := 118140960795 + 2017859 * 2 ^ 59
def prefixEnd_2017859 : Nat := 4983230072969 + 3 ^ 40 * 2017859 * 2
def baseEnd_2017859 : Nat := 1036131560000925851082541

theorem tailTrace_2017859 : CollatzResearch.WordTrace tailWord_2017859 prefixEnd_2017859 1036131560000925851082541 := by
  unfold tailWord_2017859
  simp only [CollatzResearch.WordTrace]
  refine ⟨73597363996648940725480631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49064909331099293816987087 73597363996648940725480631)
  ·
    refine ⟨110396045994973411088220947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73597363996648940725480631 110396045994973411088220947)
    ·
      refine ⟨165594068992460116632331421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110396045994973411088220947 165594068992460116632331421)
      ·
        refine ⟨62097775872172543737124283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165594068992460116632331421 62097775872172543737124283)
        ·
          refine ⟨93146663808258815605686425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62097775872172543737124283 93146663808258815605686425)
          ·
            refine ⟨69859997856194111704264819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93146663808258815605686425 69859997856194111704264819)
            ·
              refine ⟨104789996784291167556397229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69859997856194111704264819 104789996784291167556397229)
              ·
                refine ⟨39296248794109187833648961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104789996784291167556397229 39296248794109187833648961)
                ·
                  refine ⟨29472186595581890875236721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39296248794109187833648961 29472186595581890875236721)
                  ·
                    refine ⟨22104139946686418156427541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29472186595581890875236721 22104139946686418156427541)
                    ·
                      refine ⟨1036131560000925851082541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22104139946686418156427541 1036131560000925851082541)
                      ·
                        rfl

theorem cell23_2017859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_2017859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017859 prefixEnd_2017859 := by exact prefixLift 2017859
  have htrace : WordTrace (prefixWord ++ tailWord_2017859) baseStart_2017859 baseEnd_2017859 := by
    simpa [prefixWord, tailWord_2017859, baseEnd_2017859] using wordTrace_append hprefix tailTrace_2017859
  have hstable : (prefixWord ++ tailWord_2017859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017859).length < 2 ^ (prefixWord ++ tailWord_2017859).sum := by decide
  have hdescent : baseEnd_2017859 < baseStart_2017859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017863 : List Nat := [1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 4]
def baseStart_2017863 : Nat := 118140960795 + 2017863 * 2 ^ 59
def prefixEnd_2017863 : Nat := 4983230072969 + 3 ^ 40 * 2017863 * 2
def baseEnd_2017863 : Nat := 1036133613923543835432523

theorem tailTrace_2017863 : CollatzResearch.WordTrace tailWord_2017863 prefixEnd_2017863 1036133613923543835432523 := by
  unfold tailWord_2017863
  simp only [CollatzResearch.WordTrace]
  refine ⟨73597509888634449408626243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49065006592422966272417495 73597509888634449408626243)
  ·
    refine ⟨110396264832951674112939365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73597509888634449408626243 110396264832951674112939365)
    ·
      refine ⟨20699299656178438896176131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110396264832951674112939365 20699299656178438896176131)
      ·
        refine ⟨31048949484267658344264197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20699299656178438896176131 31048949484267658344264197)
        ·
          refine ⟨5821678028300185939549537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31048949484267658344264197 5821678028300185939549537)
          ·
            refine ⟨4366258521225139454662153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5821678028300185939549537 4366258521225139454662153)
            ·
              refine ⟨3274693890918854590996615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4366258521225139454662153 3274693890918854590996615)
              ·
                refine ⟨4912040836378281886494923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3274693890918854590996615 4912040836378281886494923)
                ·
                  refine ⟨7368061254567422829742385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4912040836378281886494923 7368061254567422829742385)
                  ·
                    refine ⟨5526045940925567122306789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7368061254567422829742385 5526045940925567122306789)
                    ·
                      refine ⟨1036133613923543835432523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5526045940925567122306789 1036133613923543835432523)
                      ·
                        rfl

theorem cell23_2017863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_2017863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017863 prefixEnd_2017863 := by exact prefixLift 2017863
  have htrace : WordTrace (prefixWord ++ tailWord_2017863) baseStart_2017863 baseEnd_2017863 := by
    simpa [prefixWord, tailWord_2017863, baseEnd_2017863] using wordTrace_append hprefix tailTrace_2017863
  have hstable : (prefixWord ++ tailWord_2017863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017863).length < 2 ^ (prefixWord ++ tailWord_2017863).sum := by decide
  have hdescent : baseEnd_2017863 < baseStart_2017863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017884 : List Nat := [2, 2, 4, 1, 4, 1, 2, 1, 1, 1, 4]
def baseStart_2017884 : Nat := 118140960795 + 2017884 * 2 ^ 59
def prefixEnd_2017884 : Nat := 4983230072969 + 3 ^ 40 * 2017884 * 2
def baseEnd_2017884 : Nat := 1036144397017288253269927

theorem tailTrace_2017884 : CollatzResearch.WordTrace tailWord_2017884 prefixEnd_2017884 1036144397017288253269927 := by
  unfold tailWord_2017884
  simp only [CollatzResearch.WordTrace]
  refine ⟨36799137910779184997570353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49065517214372246663427137 36799137910779184997570353)
  ·
    refine ⟨27599353433084388748177765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36799137910779184997570353 27599353433084388748177765)
    ·
      refine ⟨5174878768703322890283331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27599353433084388748177765 5174878768703322890283331)
      ·
        refine ⟨7762318153054984335424997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5174878768703322890283331 7762318153054984335424997)
        ·
          refine ⟨1455434653697809562892187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7762318153054984335424997 1455434653697809562892187)
          ·
            refine ⟨2183151980546714344338281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1455434653697809562892187 2183151980546714344338281)
            ·
              refine ⟨1637363985410035758253711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2183151980546714344338281 1637363985410035758253711)
              ·
                refine ⟨2456045978115053637380567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1637363985410035758253711 2456045978115053637380567)
                ·
                  refine ⟨3684068967172580456070851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2456045978115053637380567 3684068967172580456070851)
                  ·
                    refine ⟨5526103450758870684106277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3684068967172580456070851 5526103450758870684106277)
                    ·
                      refine ⟨1036144397017288253269927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5526103450758870684106277 1036144397017288253269927)
                      ·
                        rfl

theorem cell23_2017884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_2017884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017884 prefixEnd_2017884 := by exact prefixLift 2017884
  have htrace : WordTrace (prefixWord ++ tailWord_2017884) baseStart_2017884 baseEnd_2017884 := by
    simpa [prefixWord, tailWord_2017884, baseEnd_2017884] using wordTrace_append hprefix tailTrace_2017884
  have hstable : (prefixWord ++ tailWord_2017884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017884).length < 2 ^ (prefixWord ++ tailWord_2017884).sum := by decide
  have hdescent : baseEnd_2017884 < baseStart_2017884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017900 : List Nat := [2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 3]
def baseStart_2017900 : Nat := 118140960795 + 2017900 * 2 ^ 59
def prefixEnd_2017900 : Nat := 4983230072969 + 3 ^ 40 * 2017900 * 2
def baseEnd_2017900 : Nat := 1036152612707760190669853

theorem tailTrace_2017900 : CollatzResearch.WordTrace tailWord_2017900 prefixEnd_2017900 1036152612707760190669853 := by
  unfold tailWord_2017900
  simp only [CollatzResearch.WordTrace]
  refine ⟨36799429694750202363861577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49065906259666936485148769 36799429694750202363861577)
  ·
    refine ⟨27599572271062651772896183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36799429694750202363861577 27599572271062651772896183)
    ·
      refine ⟨41399358406593977659344275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27599572271062651772896183 41399358406593977659344275)
      ·
        refine ⟨62099037609890966489016413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41399358406593977659344275 62099037609890966489016413)
        ·
          refine ⟨23287139103709112433381155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62099037609890966489016413 23287139103709112433381155)
          ·
            refine ⟨34930708655563668650071733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23287139103709112433381155 34930708655563668650071733)
            ·
              refine ⟨3274753936459093935944225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34930708655563668650071733 3274753936459093935944225)
              ·
                refine ⟨2456065452344320451958169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3274753936459093935944225 2456065452344320451958169)
                ·
                  refine ⟨1842049089258240338968627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2456065452344320451958169 1842049089258240338968627)
                  ·
                    refine ⟨2763073633887360508452941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1842049089258240338968627 2763073633887360508452941)
                    ·
                      refine ⟨1036152612707760190669853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2763073633887360508452941 1036152612707760190669853)
                      ·
                        rfl

theorem cell23_2017900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 3].length) (baseStart_2017900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017900 prefixEnd_2017900 := by exact prefixLift 2017900
  have htrace : WordTrace (prefixWord ++ tailWord_2017900) baseStart_2017900 baseEnd_2017900 := by
    simpa [prefixWord, tailWord_2017900, baseEnd_2017900] using wordTrace_append hprefix tailTrace_2017900
  have hstable : (prefixWord ++ tailWord_2017900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017900).length < 2 ^ (prefixWord ++ tailWord_2017900).sum := by decide
  have hdescent : baseEnd_2017900 < baseStart_2017900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017916 : List Nat := [2, 2, 2, 1, 1, 2, 4, 1, 2, 6]
def baseStart_2017916 : Nat := 118140960795 + 2017916 * 2 ^ 59
def prefixEnd_2017916 : Nat := 4983230072969 + 3 ^ 40 * 2017916 * 2
def baseEnd_2017916 : Nat := 345386942799410709356593

theorem tailTrace_2017916 : CollatzResearch.WordTrace tailWord_2017916 prefixEnd_2017916 345386942799410709356593 := by
  unfold tailWord_2017916
  simp only [CollatzResearch.WordTrace]
  refine ⟨36799721478721219730152801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49066295304961626306870401 36799721478721219730152801)
  ·
    refine ⟨27599791109040914797614601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36799721478721219730152801 27599791109040914797614601)
    ·
      refine ⟨20699843331780686098210951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27599791109040914797614601 20699843331780686098210951)
      ·
        refine ⟨31049764997671029147316427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20699843331780686098210951 31049764997671029147316427)
        ·
          refine ⟨46574647496506543720974641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31049764997671029147316427 46574647496506543720974641)
          ·
            refine ⟨34930985622379907790730981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46574647496506543720974641 34930985622379907790730981)
            ·
              refine ⟨6549559804196232710762059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34930985622379907790730981 6549559804196232710762059)
              ·
                refine ⟨9824339706294349066143089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6549559804196232710762059 9824339706294349066143089)
                ·
                  refine ⟨7368254779720761799607317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9824339706294349066143089 7368254779720761799607317)
                  ·
                    refine ⟨345386942799410709356593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7368254779720761799607317 345386942799410709356593)
                    ·
                      rfl

theorem cell23_2017916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_2017916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017916 prefixEnd_2017916 := by exact prefixLift 2017916
  have htrace : WordTrace (prefixWord ++ tailWord_2017916) baseStart_2017916 baseEnd_2017916 := by
    simpa [prefixWord, tailWord_2017916, baseEnd_2017916] using wordTrace_append hprefix tailTrace_2017916
  have hstable : (prefixWord ++ tailWord_2017916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017916).length < 2 ^ (prefixWord ++ tailWord_2017916).sum := by decide
  have hdescent : baseEnd_2017916 < baseStart_2017916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017917 : List Nat := [1, 4, 1, 1, 6, 1, 1, 1, 1, 3, 3]
def baseStart_2017917 : Nat := 118140960795 + 2017917 * 2 ^ 59
def prefixEnd_2017917 : Nat := 4983230072969 + 3 ^ 40 * 2017917 * 2
def baseEnd_2017917 : Nat := 1036161341878886624157275

theorem tailTrace_2017917 : CollatzResearch.WordTrace tailWord_2017917 prefixEnd_2017917 1036161341878886624157275 := by
  unfold tailWord_2017917
  simp only [CollatzResearch.WordTrace]
  refine ⟨73599479430438816631092005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49066319620292544420728003 73599479430438816631092005)
  ·
    refine ⟨13799902393207278118329751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73599479430438816631092005 13799902393207278118329751)
    ·
      refine ⟨20699853589810917177494627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13799902393207278118329751 20699853589810917177494627)
      ·
        refine ⟨31049780384716375766241941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20699853589810917177494627 31049780384716375766241941)
        ·
          refine ⟨1455458455533580114042591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31049780384716375766241941 1455458455533580114042591)
          ·
            refine ⟨2183187683300370171063887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1455458455533580114042591 2183187683300370171063887)
            ·
              refine ⟨3274781524950555256595831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2183187683300370171063887 3274781524950555256595831)
              ·
                refine ⟨4912172287425832884893747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3274781524950555256595831 4912172287425832884893747)
                ·
                  refine ⟨7368258431138749327340621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4912172287425832884893747 7368258431138749327340621)
                  ·
                    refine ⟨2763096911677030997752733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7368258431138749327340621 2763096911677030997752733)
                    ·
                      refine ⟨1036161341878886624157275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2763096911677030997752733 1036161341878886624157275)
                      ·
                        rfl

theorem cell23_2017917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 1, 3, 3].length) (baseStart_2017917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017917 prefixEnd_2017917 := by exact prefixLift 2017917
  have htrace : WordTrace (prefixWord ++ tailWord_2017917) baseStart_2017917 baseEnd_2017917 := by
    simpa [prefixWord, tailWord_2017917, baseEnd_2017917] using wordTrace_append hprefix tailTrace_2017917
  have hstable : (prefixWord ++ tailWord_2017917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017917).length < 2 ^ (prefixWord ++ tailWord_2017917).sum := by decide
  have hdescent : baseEnd_2017917 < baseStart_2017917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017956 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 1, 2, 7]
def baseStart_2017956 : Nat := 118140960795 + 2017956 * 2 ^ 59
def prefixEnd_2017956 : Nat := 4983230072969 + 3 ^ 40 * 2017956 * 2
def baseEnd_2017956 : Nat := 1036181367624411971569595

theorem tailTrace_2017956 : CollatzResearch.WordTrace tailWord_2017956 prefixEnd_2017956 1036181367624411971569595 := by
  unfold tailWord_2017956
  simp only [CollatzResearch.WordTrace]
  refine ⟨36800450938648763145880861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49067267918198350861174481 36800450938648763145880861)
  ·
    refine ⟨13800169101993286179705323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36800450938648763145880861 13800169101993286179705323)
    ·
      refine ⟨20700253652989929269557985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13800169101993286179705323 20700253652989929269557985)
      ·
        refine ⟨15525190239742446952168489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20700253652989929269557985 15525190239742446952168489)
        ·
          refine ⟨11643892679806835214126367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15525190239742446952168489 11643892679806835214126367)
          ·
            refine ⟨17465839019710252821189551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11643892679806835214126367 17465839019710252821189551)
            ·
              refine ⟨26198758529565379231784327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17465839019710252821189551 26198758529565379231784327)
              ·
                refine ⟨39298137794348068847676491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26198758529565379231784327 39298137794348068847676491)
                ·
                  refine ⟨58947206691522103271514737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39298137794348068847676491 58947206691522103271514737)
                  ·
                    refine ⟨44210405018641577453636053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58947206691522103271514737 44210405018641577453636053)
                    ·
                      refine ⟨1036181367624411971569595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44210405018641577453636053 1036181367624411971569595)
                      ·
                        rfl

theorem cell23_2017956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_2017956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2017956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2017956 prefixEnd_2017956 := by exact prefixLift 2017956
  have htrace : WordTrace (prefixWord ++ tailWord_2017956) baseStart_2017956 baseEnd_2017956 := by
    simpa [prefixWord, tailWord_2017956, baseEnd_2017956] using wordTrace_append hprefix tailTrace_2017956
  have hstable : (prefixWord ++ tailWord_2017956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017956).length < 2 ^ (prefixWord ++ tailWord_2017956).sum := by decide
  have hdescent : baseEnd_2017956 < baseStart_2017956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018016 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 5]
def baseStart_2018016 : Nat := 118140960795 + 2018016 * 2 ^ 59
def prefixEnd_2018016 : Nat := 4983230072969 + 3 ^ 40 * 2018016 * 2
def baseEnd_2018016 : Nat := 1036212176463681736819319

theorem tailTrace_2018016 : CollatzResearch.WordTrace tailWord_2018016 prefixEnd_2018016 1036212176463681736819319 := by
  unfold tailWord_2018016
  simp only [CollatzResearch.WordTrace]
  refine ⟨36801545128540078269472951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49068726838053437692630601 36801545128540078269472951)
  ·
    refine ⟨55202317692810117404209427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36801545128540078269472951 55202317692810117404209427)
    ·
      refine ⟨82803476539215176106314141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55202317692810117404209427 82803476539215176106314141)
      ·
        refine ⟨31051303702205691039867803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82803476539215176106314141 31051303702205691039867803)
        ·
          refine ⟨46576955553308536559801705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31051303702205691039867803 46576955553308536559801705)
          ·
            refine ⟨34932716664981402419851279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46576955553308536559801705 34932716664981402419851279)
            ·
              refine ⟨52399074997472103629776919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34932716664981402419851279 52399074997472103629776919)
              ·
                refine ⟨78598612496208155444665379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52399074997472103629776919 78598612496208155444665379)
                ·
                  refine ⟨117897918744312233166998069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78598612496208155444665379 117897918744312233166998069)
                  ·
                    refine ⟨11052929882279271859406069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117897918744312233166998069 11052929882279271859406069)
                    ·
                      refine ⟨1036212176463681736819319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11052929882279271859406069 1036212176463681736819319)
                      ·
                        rfl

theorem cell23_2018016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_2018016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018016 prefixEnd_2018016 := by exact prefixLift 2018016
  have htrace : WordTrace (prefixWord ++ tailWord_2018016) baseStart_2018016 baseEnd_2018016 := by
    simpa [prefixWord, tailWord_2018016, baseEnd_2018016] using wordTrace_append hprefix tailTrace_2018016
  have hstable : (prefixWord ++ tailWord_2018016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018016).length < 2 ^ (prefixWord ++ tailWord_2018016).sum := by decide
  have hdescent : baseEnd_2018016 < baseStart_2018016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018030 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 1, 6, 2]
def baseStart_2018030 : Nat := 118140960795 + 2018030 * 2 ^ 59
def prefixEnd_2018030 : Nat := 4983230072969 + 3 ^ 40 * 2018030 * 2
def baseEnd_2018030 : Nat := 1036219365192844682044255

theorem tailTrace_2018030 : CollatzResearch.WordTrace tailWord_2018030 prefixEnd_2018030 1036219365192844682044255 := by
  unfold tailWord_2018030
  simp only [CollatzResearch.WordTrace]
  refine ⟨9200450109878679616244443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49069067252686291286637029 9200450109878679616244443)
  ·
    refine ⟨13800675164818019424366665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9200450109878679616244443 13800675164818019424366665)
    ·
      refine ⟨10350506373613514568274999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13800675164818019424366665 10350506373613514568274999)
      ·
        refine ⟨15525759560420271852412499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10350506373613514568274999 15525759560420271852412499)
        ·
          refine ⟨23288639340630407778618749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15525759560420271852412499 23288639340630407778618749)
          ·
            refine ⟨8733239752736402916982031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23288639340630407778618749 8733239752736402916982031)
            ·
              refine ⟨13099859629104604375473047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8733239752736402916982031 13099859629104604375473047)
              ·
                refine ⟨19649789443656906563209571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13099859629104604375473047 19649789443656906563209571)
                ·
                  refine ⟨29474684165485359844814357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19649789443656906563209571 29474684165485359844814357)
                  ·
                    refine ⟨1381625820257126242725673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29474684165485359844814357 1381625820257126242725673)
                    ·
                      refine ⟨1036219365192844682044255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1381625820257126242725673 1036219365192844682044255)
                      ·
                        rfl

theorem cell23_2018030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_2018030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018030 prefixEnd_2018030 := by exact prefixLift 2018030
  have htrace : WordTrace (prefixWord ++ tailWord_2018030) baseStart_2018030 baseEnd_2018030 := by
    simpa [prefixWord, tailWord_2018030, baseEnd_2018030] using wordTrace_append hprefix tailTrace_2018030
  have hstable : (prefixWord ++ tailWord_2018030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018030).length < 2 ^ (prefixWord ++ tailWord_2018030).sum := by decide
  have hdescent : baseEnd_2018030 < baseStart_2018030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018033 : List Nat := [1, 2, 2, 2, 2, 2, 2, 2, 1, 4, 3]
def baseStart_2018033 : Nat := 118140960795 + 2018033 * 2 ^ 59
def prefixEnd_2018033 : Nat := 4983230072969 + 3 ^ 40 * 2018033 * 2
def baseEnd_2018033 : Nat := 1036220905634808170306741

theorem tailTrace_2018033 : CollatzResearch.WordTrace tailWord_2018033 prefixEnd_2018033 1036220905634808170306741 := by
  unfold tailWord_2018033
  simp only [CollatzResearch.WordTrace]
  refine ⟨73603710298018568442314753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49069140198679045628209835 73603710298018568442314753)
  ·
    refine ⟨55202782723513926331736065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73603710298018568442314753 55202782723513926331736065)
    ·
      refine ⟨41402087042635444748802049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55202782723513926331736065 41402087042635444748802049)
      ·
        refine ⟨31051565281976583561601537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41402087042635444748802049 31051565281976583561601537)
        ·
          refine ⟨23288673961482437671201153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31051565281976583561601537 23288673961482437671201153)
          ·
            refine ⟨17466505471111828253400865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23288673961482437671201153 17466505471111828253400865)
            ·
              refine ⟨13099879103333871190050649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17466505471111828253400865 13099879103333871190050649)
              ·
                refine ⟨9824909327500403392537987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13099879103333871190050649 9824909327500403392537987)
                ·
                  refine ⟨14737363991250605088806981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9824909327500403392537987 14737363991250605088806981)
                  ·
                    refine ⟨2763255748359488454151309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14737363991250605088806981 2763255748359488454151309)
                    ·
                      refine ⟨1036220905634808170306741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2763255748359488454151309 1036220905634808170306741)
                      ·
                        rfl

theorem cell23_2018033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_2018033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018033 prefixEnd_2018033 := by exact prefixLift 2018033
  have htrace : WordTrace (prefixWord ++ tailWord_2018033) baseStart_2018033 baseEnd_2018033 := by
    simpa [prefixWord, tailWord_2018033, baseEnd_2018033] using wordTrace_append hprefix tailTrace_2018033
  have hstable : (prefixWord ++ tailWord_2018033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018033).length < 2 ^ (prefixWord ++ tailWord_2018033).sum := by decide
  have hdescent : baseEnd_2018033 < baseStart_2018033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018120 : List Nat := [2, 1, 3, 1, 1, 3, 1, 5, 1, 1, 4]
def baseStart_2018120 : Nat := 118140960795 + 2018120 * 2 ^ 59
def prefixEnd_2018120 : Nat := 4983230072969 + 3 ^ 40 * 2018120 * 2
def baseEnd_2018120 : Nat := 1036265578451749329918841

theorem tailTrace_2018120 : CollatzResearch.WordTrace tailWord_2018120 prefixEnd_2018120 1036265578451749329918841 := by
  unfold tailWord_2018120
  simp only [CollatzResearch.WordTrace]
  refine ⟨36803441724351691150365907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49071255632468921533821209 36803441724351691150365907)
  ·
    refine ⟨55205162586527536725548861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36803441724351691150365907 55205162586527536725548861)
    ·
      refine ⟨20701935969947826272080823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55205162586527536725548861 20701935969947826272080823)
      ·
        refine ⟨31052903954921739408121235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20701935969947826272080823 31052903954921739408121235)
        ·
          refine ⟨46579355932382609112181853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31052903954921739408121235 46579355932382609112181853)
          ·
            refine ⟨17467258474643478417068195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46579355932382609112181853 17467258474643478417068195)
            ·
              refine ⟨26200887711965217625602293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17467258474643478417068195 26200887711965217625602293)
              ·
                refine ⟨2456333222996739152400215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26200887711965217625602293 2456333222996739152400215)
                ·
                  refine ⟨3684499834495108728600323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2456333222996739152400215 3684499834495108728600323)
                  ·
                    refine ⟨5526749751742663092900485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3684499834495108728600323 5526749751742663092900485)
                    ·
                      refine ⟨1036265578451749329918841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5526749751742663092900485 1036265578451749329918841)
                      ·
                        rfl

theorem cell23_2018120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_2018120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018120 prefixEnd_2018120 := by exact prefixLift 2018120
  have htrace : WordTrace (prefixWord ++ tailWord_2018120) baseStart_2018120 baseEnd_2018120 := by
    simpa [prefixWord, tailWord_2018120, baseEnd_2018120] using wordTrace_append hprefix tailTrace_2018120
  have hstable : (prefixWord ++ tailWord_2018120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018120).length < 2 ^ (prefixWord ++ tailWord_2018120).sum := by decide
  have hdescent : baseEnd_2018120 < baseStart_2018120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018130 : List Nat := [3, 2, 2, 1, 1, 2, 1, 3, 4, 4]
def baseStart_2018130 : Nat := 118140960795 + 2018130 * 2 ^ 59
def prefixEnd_2018130 : Nat := 4983230072969 + 3 ^ 40 * 2018130 * 2
def baseEnd_2018130 : Nat := 345423571086098096931265

theorem tailTrace_2018130 : CollatzResearch.WordTrace tailWord_2018130 prefixEnd_2018130 345423571086098096931265 := by
  unfold tailWord_2018130
  simp only [CollatzResearch.WordTrace]
  refine ⟨18401812044666788502148961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49071498785778102672397229 18401812044666788502148961)
  ·
    refine ⟨13801359033500091376611721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18401812044666788502148961 13801359033500091376611721)
    ·
      refine ⟨10351019275125068532458791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13801359033500091376611721 10351019275125068532458791)
      ·
        refine ⟨15526528912687602798688187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10351019275125068532458791 15526528912687602798688187)
        ·
          refine ⟨23289793369031404198032281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15526528912687602798688187 23289793369031404198032281)
          ·
            refine ⟨17467345026773553148524211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23289793369031404198032281 17467345026773553148524211)
            ·
              refine ⟨26201017540160329722786317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17467345026773553148524211 26201017540160329722786317)
              ·
                refine ⟨9825381577560123646044869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26201017540160329722786317 9825381577560123646044869)
                ·
                  refine ⟨1842259045792523183633413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9825381577560123646044869 1842259045792523183633413)
                  ·
                    refine ⟨345423571086098096931265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1842259045792523183633413 345423571086098096931265)
                    ·
                      rfl

theorem cell23_2018130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_2018130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018130 prefixEnd_2018130 := by exact prefixLift 2018130
  have htrace : WordTrace (prefixWord ++ tailWord_2018130) baseStart_2018130 baseEnd_2018130 := by
    simpa [prefixWord, tailWord_2018130, baseEnd_2018130] using wordTrace_append hprefix tailTrace_2018130
  have hstable : (prefixWord ++ tailWord_2018130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018130).length < 2 ^ (prefixWord ++ tailWord_2018130).sum := by decide
  have hdescent : baseEnd_2018130 < baseStart_2018130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018133 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 3, 1, 6]
def baseStart_2018133 : Nat := 118140960795 + 2018133 * 2 ^ 59
def prefixEnd_2018133 : Nat := 4983230072969 + 3 ^ 40 * 2018133 * 2
def baseEnd_2018133 : Nat := 1036272253700257779056281

theorem tailTrace_2018133 : CollatzResearch.WordTrace tailWord_2018133 prefixEnd_2018133 1036272253700257779056281 := by
  unfold tailWord_2018133
  simp only [CollatzResearch.WordTrace]
  refine ⟨73607357597656285520955053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49071571731770857013970035 73607357597656285520955053)
  ·
    refine ⟨27602759099121107070358145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73607357597656285520955053 27602759099121107070358145)
    ·
      refine ⟨20702069324340830302768609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27602759099121107070358145 20702069324340830302768609)
      ·
        refine ⟨15526551993255622727076457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20702069324340830302768609 15526551993255622727076457)
        ·
          refine ⟨11644913994941717045307343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15526551993255622727076457 11644913994941717045307343)
          ·
            refine ⟨17467370992412575567961015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11644913994941717045307343 17467370992412575567961015)
            ·
              refine ⟨26201056488618863351941523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17467370992412575567961015 26201056488618863351941523)
              ·
                refine ⟨39301584732928295027912285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26201056488618863351941523 39301584732928295027912285)
                ·
                  refine ⟨14738094274848110635467107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39301584732928295027912285 14738094274848110635467107)
                  ·
                    refine ⟨22107141412272165953200661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14738094274848110635467107 22107141412272165953200661)
                    ·
                      refine ⟨1036272253700257779056281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22107141412272165953200661 1036272253700257779056281)
                      ·
                        rfl

theorem cell23_2018133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_2018133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018133 prefixEnd_2018133 := by exact prefixLift 2018133
  have htrace : WordTrace (prefixWord ++ tailWord_2018133) baseStart_2018133 baseEnd_2018133 := by
    simpa [prefixWord, tailWord_2018133, baseEnd_2018133] using wordTrace_append hprefix tailTrace_2018133
  have hstable : (prefixWord ++ tailWord_2018133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018133).length < 2 ^ (prefixWord ++ tailWord_2018133).sum := by decide
  have hdescent : baseEnd_2018133 < baseStart_2018133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018143 : List Nat := [1, 1, 2, 3, 1, 3, 4, 8]
def baseStart_2018143 : Nat := 118140960795 + 2018143 * 2 ^ 59
def prefixEnd_2018143 : Nat := 4983230072969 + 3 ^ 40 * 2018143 * 2
def baseEnd_2018143 : Nat := 38380644018770471849305

theorem tailTrace_2018143 : CollatzResearch.WordTrace tailWord_2018143 prefixEnd_2018143 38380644018770471849305 := by
  unfold tailWord_2018143
  simp only [CollatzResearch.WordTrace]
  refine ⟨73607722327620057228819083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49071814885080038152546055 73607722327620057228819083)
  ·
    refine ⟨110411583491430085843228625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73607722327620057228819083 110411583491430085843228625)
    ·
      refine ⟨82808687618572564382421469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110411583491430085843228625 82808687618572564382421469)
      ·
        refine ⟨31053257856964711643408051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82808687618572564382421469 31053257856964711643408051)
        ·
          refine ⟨46579886785447067465112077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31053257856964711643408051 46579886785447067465112077)
          ·
            refine ⟨17467457544542650299417029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46579886785447067465112077 17467457544542650299417029)
            ·
              refine ⟨3275148289601746931140693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17467457544542650299417029 3275148289601746931140693)
              ·
                refine ⟨38380644018770471849305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3275148289601746931140693 38380644018770471849305)
                ·
                  rfl

theorem cell23_2018143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 8].length) (baseStart_2018143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018143 prefixEnd_2018143 := by exact prefixLift 2018143
  have htrace : WordTrace (prefixWord ++ tailWord_2018143) baseStart_2018143 baseEnd_2018143 := by
    simpa [prefixWord, tailWord_2018143, baseEnd_2018143] using wordTrace_append hprefix tailTrace_2018143
  have hstable : (prefixWord ++ tailWord_2018143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018143).length < 2 ^ (prefixWord ++ tailWord_2018143).sum := by decide
  have hdescent : baseEnd_2018143 < baseStart_2018143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018147 : List Nat := [1, 1, 1, 5, 3, 2, 1, 3, 2, 4]
def baseStart_2018147 : Nat := 118140960795 + 2018147 * 2 ^ 59
def prefixEnd_2018147 : Nat := 4983230072969 + 3 ^ 40 * 2018147 * 2
def baseEnd_2018147 : Nat := 345426480809806908093739

theorem tailTrace_2018147 : CollatzResearch.WordTrace tailWord_2018147 prefixEnd_2018147 345426480809806908093739 := by
  unfold tailWord_2018147
  simp only [CollatzResearch.WordTrace]
  refine ⟨73607868219605565911964695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49071912146403710607976463 73607868219605565911964695)
  ·
    refine ⟨110411802329408348867947043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73607868219605565911964695 110411802329408348867947043)
    ·
      refine ⟨165617703494112523301920565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110411802329408348867947043 165617703494112523301920565)
      ·
        refine ⟨15526659702573049059555053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165617703494112523301920565 15526659702573049059555053)
        ·
          refine ⟨5822497388464893397333145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15526659702573049059555053 5822497388464893397333145)
          ·
            refine ⟨4366873041348670047999859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5822497388464893397333145 4366873041348670047999859)
            ·
              refine ⟨6550309562023005071999789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4366873041348670047999859 6550309562023005071999789)
              ·
                refine ⟨2456366085758626901999921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6550309562023005071999789 2456366085758626901999921)
                ·
                  refine ⟨1842274564318970176499941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2456366085758626901999921 1842274564318970176499941)
                  ·
                    refine ⟨345426480809806908093739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1842274564318970176499941 345426480809806908093739)
                    ·
                      rfl

theorem cell23_2018147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2, 4].length) (baseStart_2018147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018147 prefixEnd_2018147 := by exact prefixLift 2018147
  have htrace : WordTrace (prefixWord ++ tailWord_2018147) baseStart_2018147 baseEnd_2018147 := by
    simpa [prefixWord, tailWord_2018147, baseEnd_2018147] using wordTrace_append hprefix tailTrace_2018147
  have hstable : (prefixWord ++ tailWord_2018147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018147).length < 2 ^ (prefixWord ++ tailWord_2018147).sum := by decide
  have hdescent : baseEnd_2018147 < baseStart_2018147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018187 : List Nat := [1, 1, 1, 1, 4, 2, 3, 4, 2, 1, 3]
def baseStart_2018187 : Nat := 118140960795 + 2018187 * 2 ^ 59
def prefixEnd_2018187 : Nat := 4983230072969 + 3 ^ 40 * 2018187 * 2
def baseEnd_2018187 : Nat := 1036299981655600567781033

theorem tailTrace_2018187 : CollatzResearch.WordTrace tailWord_2018187 prefixEnd_2018187 1036299981655600567781033 := by
  unfold tailWord_2018187
  simp only [CollatzResearch.WordTrace]
  refine ⟨73609327139460652743420815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49072884759640435162280543 73609327139460652743420815)
  ·
    refine ⟨110413990709190979115131223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73609327139460652743420815 110413990709190979115131223)
    ·
      refine ⟨165620986063786468672696835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110413990709190979115131223 165620986063786468672696835)
      ·
        refine ⟨248431479095679703009045253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165620986063786468672696835 248431479095679703009045253)
        ·
          refine ⟨46580902330439944314195985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248431479095679703009045253 46580902330439944314195985)
          ·
            refine ⟨34935676747829958235646989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46580902330439944314195985 34935676747829958235646989)
            ·
              refine ⟨13100878780436234338367621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34935676747829958235646989 13100878780436234338367621)
              ·
                refine ⟨2456414771331793938443929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13100878780436234338367621 2456414771331793938443929)
                ·
                  refine ⟨1842311078498845453832947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2456414771331793938443929 1842311078498845453832947)
                  ·
                    refine ⟨2763466617748268180749421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1842311078498845453832947 2763466617748268180749421)
                    ·
                      refine ⟨1036299981655600567781033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2763466617748268180749421 1036299981655600567781033)
                      ·
                        rfl

theorem cell23_2018187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2, 1, 3].length) (baseStart_2018187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018187 prefixEnd_2018187 := by exact prefixLift 2018187
  have htrace : WordTrace (prefixWord ++ tailWord_2018187) baseStart_2018187 baseEnd_2018187 := by
    simpa [prefixWord, tailWord_2018187, baseEnd_2018187] using wordTrace_append hprefix tailTrace_2018187
  have hstable : (prefixWord ++ tailWord_2018187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018187).length < 2 ^ (prefixWord ++ tailWord_2018187).sum := by decide
  have hdescent : baseEnd_2018187 < baseStart_2018187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018194 : List Nat := [3, 2, 3, 2, 3, 1, 1, 8]
def baseStart_2018194 : Nat := 118140960795 + 2018194 * 2 ^ 59
def prefixEnd_2018194 : Nat := 4983230072969 + 3 ^ 40 * 2018194 * 2
def baseEnd_2018194 : Nat := 38381613926673408903463

theorem tailTrace_2018194 : CollatzResearch.WordTrace tailWord_2018194 prefixEnd_2018194 38381613926673408903463 := by
  unfold tailWord_2018194
  simp only [CollatzResearch.WordTrace]
  refine ⟨18402395612608823234731409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49073054966956861959283757 18402395612608823234731409)
  ·
    refine ⟨13801796709456617426048557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18402395612608823234731409 13801796709456617426048557)
    ·
      refine ⟨5175673766046231534768209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13801796709456617426048557 5175673766046231534768209)
      ·
        refine ⟨3881755324534673651076157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5175673766046231534768209 3881755324534673651076157)
        ·
          refine ⟨1455658246700502619153559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3881755324534673651076157 1455658246700502619153559)
          ·
            refine ⟨2183487370050753928730339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1455658246700502619153559 2183487370050753928730339)
            ·
              refine ⟨3275231055076130893095509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2183487370050753928730339 3275231055076130893095509)
              ·
                refine ⟨38381613926673408903463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3275231055076130893095509 38381613926673408903463)
                ·
                  rfl

theorem cell23_2018194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 8].length) (baseStart_2018194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018194 prefixEnd_2018194 := by exact prefixLift 2018194
  have htrace : WordTrace (prefixWord ++ tailWord_2018194) baseStart_2018194 baseEnd_2018194 := by
    simpa [prefixWord, tailWord_2018194, baseEnd_2018194] using wordTrace_append hprefix tailTrace_2018194
  have hstable : (prefixWord ++ tailWord_2018194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018194).length < 2 ^ (prefixWord ++ tailWord_2018194).sum := by decide
  have hdescent : baseEnd_2018194 < baseStart_2018194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018197 : List Nat := [1, 3, 2, 1, 1, 4, 1, 2, 3, 3, 2]
def baseStart_2018197 : Nat := 118140960795 + 2018197 * 2 ^ 59
def prefixEnd_2018197 : Nat := 4983230072969 + 3 ^ 40 * 2018197 * 2
def baseEnd_2018197 : Nat := 1036305116462145528655987

theorem tailTrace_2018197 : CollatzResearch.WordTrace tailWord_2018197 prefixEnd_2018197 1036305116462145528655987 := by
  unfold tailWord_2018197
  simp only [CollatzResearch.WordTrace]
  refine ⟨73609691869424424451284845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49073127912949616300856563 73609691869424424451284845)
  ·
    refine ⟨27603634451034159169231817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73609691869424424451284845 27603634451034159169231817)
    ·
      refine ⟨20702725838275619376923863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27603634451034159169231817 20702725838275619376923863)
      ·
        refine ⟨31054088757413429065385795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20702725838275619376923863 31054088757413429065385795)
        ·
          refine ⟨46581133136120143598078693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31054088757413429065385795 46581133136120143598078693)
          ·
            refine ⟨8733962463022526924639755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46581133136120143598078693 8733962463022526924639755)
            ·
              refine ⟨13100943694533790386959633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8733962463022526924639755 13100943694533790386959633)
              ·
                refine ⟨9825707770900342790219725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13100943694533790386959633 9825707770900342790219725)
                ·
                  refine ⟨3684640414087628546332397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9825707770900342790219725 3684640414087628546332397)
                  ·
                    refine ⟨1381740155282860704874649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3684640414087628546332397 1381740155282860704874649)
                    ·
                      refine ⟨1036305116462145528655987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1381740155282860704874649 1036305116462145528655987)
                      ·
                        rfl

theorem cell23_2018197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 3, 2].length) (baseStart_2018197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018197 prefixEnd_2018197 := by exact prefixLift 2018197
  have htrace : WordTrace (prefixWord ++ tailWord_2018197) baseStart_2018197 baseEnd_2018197 := by
    simpa [prefixWord, tailWord_2018197, baseEnd_2018197] using wordTrace_append hprefix tailTrace_2018197
  have hstable : (prefixWord ++ tailWord_2018197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018197).length < 2 ^ (prefixWord ++ tailWord_2018197).sum := by decide
  have hdescent : baseEnd_2018197 < baseStart_2018197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018204 : List Nat := [2, 2, 3, 3, 2, 1, 2, 1, 1, 3, 3]
def baseStart_2018204 : Nat := 118140960795 + 2018204 * 2 ^ 59
def prefixEnd_2018204 : Nat := 4983230072969 + 3 ^ 40 * 2018204 * 2
def baseEnd_2018204 : Nat := 1036308710826727001268455

theorem tailTrace_2018204 : CollatzResearch.WordTrace tailWord_2018204 prefixEnd_2018204 1036308710826727001268455 := by
  unfold tailWord_2018204
  simp only [CollatzResearch.WordTrace]
  refine ⟨36804973590199532323394833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49073298120266043097859777 36804973590199532323394833)
  ·
    refine ⟨27603730192649649242546125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36804973590199532323394833 27603730192649649242546125)
    ·
      refine ⟨10351398822243618465954797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27603730192649649242546125 10351398822243618465954797)
      ·
        refine ⟨3881774558341356924733049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10351398822243618465954797 3881774558341356924733049)
        ·
          refine ⟨2911330918756017693549787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3881774558341356924733049 2911330918756017693549787)
          ·
            refine ⟨4366996378134026540324681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2911330918756017693549787 4366996378134026540324681)
            ·
              refine ⟨3275247283600519905243511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4366996378134026540324681 3275247283600519905243511)
              ·
                refine ⟨4912870925400779857865267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3275247283600519905243511 4912870925400779857865267)
                ·
                  refine ⟨7369306388101169786797901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4912870925400779857865267 7369306388101169786797901)
                  ·
                    refine ⟨2763489895537938670049213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7369306388101169786797901 2763489895537938670049213)
                    ·
                      refine ⟨1036308710826727001268455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2763489895537938670049213 1036308710826727001268455)
                      ·
                        rfl

theorem cell23_2018204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_2018204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018204 prefixEnd_2018204 := by exact prefixLift 2018204
  have htrace : WordTrace (prefixWord ++ tailWord_2018204) baseStart_2018204 baseEnd_2018204 := by
    simpa [prefixWord, tailWord_2018204, baseEnd_2018204] using wordTrace_append hprefix tailTrace_2018204
  have hstable : (prefixWord ++ tailWord_2018204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018204).length < 2 ^ (prefixWord ++ tailWord_2018204).sum := by decide
  have hdescent : baseEnd_2018204 < baseStart_2018204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018240 : List Nat := [2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 4]
def baseStart_2018240 : Nat := 118140960795 + 2018240 * 2 ^ 59
def prefixEnd_2018240 : Nat := 4983230072969 + 3 ^ 40 * 2018240 * 2
def baseEnd_2018240 : Nat := 1036327196130288860418289

theorem tailTrace_2018240 : CollatzResearch.WordTrace tailWord_2018240 prefixEnd_2018240 1036327196130288860418289 := by
  unfold tailWord_2018240
  simp only [CollatzResearch.WordTrace]
  refine ⟨36805630104134321397550087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49074173472179095196733449 36805630104134321397550087)
  ·
    refine ⟨55208445156201482096325131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36805630104134321397550087 55208445156201482096325131)
    ·
      refine ⟨82812667734302223144487697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55208445156201482096325131 82812667734302223144487697)
      ·
        refine ⟨62109500800726667358365773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82812667734302223144487697 62109500800726667358365773)
        ·
          refine ⟨23291062800272500259387165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62109500800726667358365773 23291062800272500259387165)
          ·
            refine ⟨8734148550102187597270187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23291062800272500259387165 8734148550102187597270187)
            ·
              refine ⟨13101222825153281395905281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8734148550102187597270187 13101222825153281395905281)
              ·
                refine ⟨9825917118864961046928961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13101222825153281395905281 9825917118864961046928961)
                ·
                  refine ⟨7369437839148720785196721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9825917118864961046928961 7369437839148720785196721)
                  ·
                    refine ⟨5527078379361540588897541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7369437839148720785196721 5527078379361540588897541)
                    ·
                      refine ⟨1036327196130288860418289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5527078379361540588897541 1036327196130288860418289)
                      ·
                        rfl

theorem cell23_2018240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_2018240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018240 prefixEnd_2018240 := by exact prefixLift 2018240
  have htrace : WordTrace (prefixWord ++ tailWord_2018240) baseStart_2018240 baseEnd_2018240 := by
    simpa [prefixWord, tailWord_2018240, baseEnd_2018240] using wordTrace_append hprefix tailTrace_2018240
  have hstable : (prefixWord ++ tailWord_2018240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018240).length < 2 ^ (prefixWord ++ tailWord_2018240).sum := by decide
  have hdescent : baseEnd_2018240 < baseStart_2018240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018243 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 7]
def baseStart_2018243 : Nat := 118140960795 + 2018243 * 2 ^ 59
def prefixEnd_2018243 : Nat := 4983230072969 + 3 ^ 40 * 2018243 * 2
def baseEnd_2018243 : Nat := 1036328736572252348680775

theorem tailTrace_2018243 : CollatzResearch.WordTrace tailWord_2018243 prefixEnd_2018243 1036328736572252348680775 := by
  unfold tailWord_2018243
  simp only [CollatzResearch.WordTrace]
  refine ⟨73611369627257774307459383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49074246418171849538306255 73611369627257774307459383)
  ·
    refine ⟨110417054440886661461189075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73611369627257774307459383 110417054440886661461189075)
    ·
      refine ⟨165625581661329992191783613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110417054440886661461189075 165625581661329992191783613)
      ·
        refine ⟨62109593122998747071918855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165625581661329992191783613 62109593122998747071918855)
        ·
          refine ⟨93164389684498120607878283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62109593122998747071918855 93164389684498120607878283)
          ·
            refine ⟨139746584526747180911817425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93164389684498120607878283 139746584526747180911817425)
            ·
              refine ⟨104809938395060385683863069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139746584526747180911817425 104809938395060385683863069)
              ·
                refine ⟨39303726898147644631448651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104809938395060385683863069 39303726898147644631448651)
                ·
                  refine ⟨58955590347221466947172977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39303726898147644631448651 58955590347221466947172977)
                  ·
                    refine ⟨44216692760416100210379733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58955590347221466947172977 44216692760416100210379733)
                    ·
                      refine ⟨1036328736572252348680775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44216692760416100210379733 1036328736572252348680775)
                      ·
                        rfl

theorem cell23_2018243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_2018243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018243 prefixEnd_2018243 := by exact prefixLift 2018243
  have htrace : WordTrace (prefixWord ++ tailWord_2018243) baseStart_2018243 baseEnd_2018243 := by
    simpa [prefixWord, tailWord_2018243, baseEnd_2018243] using wordTrace_append hprefix tailTrace_2018243
  have hstable : (prefixWord ++ tailWord_2018243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018243).length < 2 ^ (prefixWord ++ tailWord_2018243).sum := by decide
  have hdescent : baseEnd_2018243 < baseStart_2018243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018261 : List Nat := [1, 3, 2, 3, 3, 2, 1, 1, 1, 4, 2]
def baseStart_2018261 : Nat := 118140960795 + 2018261 * 2 ^ 59
def prefixEnd_2018261 : Nat := 4983230072969 + 3 ^ 40 * 2018261 * 2
def baseEnd_2018261 : Nat := 1036337979224033278255693

theorem tailTrace_2018261 : CollatzResearch.WordTrace tailWord_2018261 prefixEnd_2018261 1036337979224033278255693 := by
  unfold tailWord_2018261
  simp only [CollatzResearch.WordTrace]
  refine ⟨73612026141192563381614637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49074684094128375587743091 73612026141192563381614637)
  ·
    refine ⟨27604509802947211268105489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73612026141192563381614637 27604509802947211268105489)
    ·
      refine ⟨20703382352210408451079117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27604509802947211268105489 20703382352210408451079117)
      ·
        refine ⟨7763768382078903169154669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20703382352210408451079117 7763768382078903169154669)
        ·
          refine ⟨2911413143279588688433001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7763768382078903169154669 2911413143279588688433001)
          ·
            refine ⟨2183559857459691516324751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2911413143279588688433001 2183559857459691516324751)
            ·
              refine ⟨3275339786189537274487127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2183559857459691516324751 3275339786189537274487127)
              ·
                refine ⟨4913009679284305911730691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3275339786189537274487127 4913009679284305911730691)
                ·
                  refine ⟨7369514518926458867596037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4913009679284305911730691 7369514518926458867596037)
                  ·
                    refine ⟨1381783972298711037674257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7369514518926458867596037 1381783972298711037674257)
                    ·
                      refine ⟨1036337979224033278255693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1381783972298711037674257 1036337979224033278255693)
                      ·
                        rfl

theorem cell23_2018261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_2018261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018261 prefixEnd_2018261 := by exact prefixLift 2018261
  have htrace : WordTrace (prefixWord ++ tailWord_2018261) baseStart_2018261 baseEnd_2018261 := by
    simpa [prefixWord, tailWord_2018261, baseEnd_2018261] using wordTrace_append hprefix tailTrace_2018261
  have hstable : (prefixWord ++ tailWord_2018261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018261).length < 2 ^ (prefixWord ++ tailWord_2018261).sum := by decide
  have hdescent : baseEnd_2018261 < baseStart_2018261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018280 : List Nat := [2, 1, 4, 1, 1, 1, 4, 1, 1, 7]
def baseStart_2018280 : Nat := 118140960795 + 2018280 * 2 ^ 59
def prefixEnd_2018280 : Nat := 4983230072969 + 3 ^ 40 * 2018280 * 2
def baseEnd_2018280 : Nat := 345449245118822901306035

theorem tailTrace_2018280 : CollatzResearch.WordTrace tailWord_2018280 prefixEnd_2018280 345449245118822901306035 := by
  unfold tailWord_2018280
  simp only [CollatzResearch.WordTrace]
  refine ⟨36806359564061864813278147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49075146085415819751037529 36806359564061864813278147)
  ·
    refine ⟨55209539346092797219917221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36806359564061864813278147 55209539346092797219917221)
    ·
      refine ⟨10351788627392399478734479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55209539346092797219917221 10351788627392399478734479)
      ·
        refine ⟨15527682941088599218101719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10351788627392399478734479 15527682941088599218101719)
        ·
          refine ⟨23291524411632898827152579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15527682941088599218101719 23291524411632898827152579)
          ·
            refine ⟨34937286617449348240728869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23291524411632898827152579 34937286617449348240728869)
            ·
              refine ⟨6550741240771752795136663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34937286617449348240728869 6550741240771752795136663)
              ·
                refine ⟨9826111861157629192704995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6550741240771752795136663 9826111861157629192704995)
                ·
                  refine ⟨14739167791736443789057493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9826111861157629192704995 14739167791736443789057493)
                  ·
                    refine ⟨345449245118822901306035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14739167791736443789057493 345449245118822901306035)
                    ·
                      rfl

theorem cell23_2018280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_2018280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018280 prefixEnd_2018280 := by exact prefixLift 2018280
  have htrace : WordTrace (prefixWord ++ tailWord_2018280) baseStart_2018280 baseEnd_2018280 := by
    simpa [prefixWord, tailWord_2018280, baseEnd_2018280] using wordTrace_append hprefix tailTrace_2018280
  have hstable : (prefixWord ++ tailWord_2018280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018280).length < 2 ^ (prefixWord ++ tailWord_2018280).sum := by decide
  have hdescent : baseEnd_2018280 < baseStart_2018280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018361 : List Nat := [1, 2, 1, 5, 2, 2, 1, 4, 1, 4]
def baseStart_2018361 : Nat := 118140960795 + 2018361 * 2 ^ 59
def prefixEnd_2018361 : Nat := 4983230072969 + 3 ^ 40 * 2018361 * 2
def baseEnd_2018361 : Nat := 345463109096494295668411

theorem tailTrace_2018361 : CollatzResearch.WordTrace tailWord_2018361 prefixEnd_2018361 345463109096494295668411 := by
  unfold tailWord_2018361
  simp only [CollatzResearch.WordTrace]
  refine ⟨73615673440830280460254937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49077115627220186973503291 73615673440830280460254937)
  ·
    refine ⟨55211755080622710345191203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73615673440830280460254937 55211755080622710345191203)
    ·
      refine ⟨82817632620934065517786805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55211755080622710345191203 82817632620934065517786805)
      ·
        refine ⟨7764153058212568642292513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82817632620934065517786805 7764153058212568642292513)
        ·
          refine ⟨5823114793659426481719385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7764153058212568642292513 5823114793659426481719385)
          ·
            refine ⟨4367336095244569861289539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5823114793659426481719385 4367336095244569861289539)
            ·
              refine ⟨6551004142866854791934309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4367336095244569861289539 6551004142866854791934309)
              ·
                refine ⟨1228313276787535273487683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6551004142866854791934309 1228313276787535273487683)
                ·
                  refine ⟨1842469915181302910231525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1228313276787535273487683 1842469915181302910231525)
                  ·
                    refine ⟨345463109096494295668411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1842469915181302910231525 345463109096494295668411)
                    ·
                      rfl

theorem cell23_2018361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4, 1, 4].length) (baseStart_2018361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018361 prefixEnd_2018361 := by exact prefixLift 2018361
  have htrace : WordTrace (prefixWord ++ tailWord_2018361) baseStart_2018361 baseEnd_2018361 := by
    simpa [prefixWord, tailWord_2018361, baseEnd_2018361] using wordTrace_append hprefix tailTrace_2018361
  have hstable : (prefixWord ++ tailWord_2018361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018361).length < 2 ^ (prefixWord ++ tailWord_2018361).sum := by decide
  have hdescent : baseEnd_2018361 < baseStart_2018361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018380 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 1, 3, 7]
def baseStart_2018380 : Nat := 118140960795 + 2018380 * 2 ^ 59
def prefixEnd_2018380 : Nat := 4983230072969 + 3 ^ 40 * 2018380 * 2
def baseEnd_2018380 : Nat := 1036399083421918312667645

theorem tailTrace_2018380 : CollatzResearch.WordTrace tailWord_2018380 prefixEnd_2018380 1036399083421918312667645 := by
  unfold tailWord_2018380
  simp only [CollatzResearch.WordTrace]
  refine ⟨36808183213880723352598297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49077577618507631136797729 36808183213880723352598297)
  ·
    refine ⟨27606137410410542514448723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36808183213880723352598297 27606137410410542514448723)
    ·
      refine ⟨41409206115615813771673085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27606137410410542514448723 41409206115615813771673085)
      ·
        refine ⟨15528452293355930164377407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41409206115615813771673085 15528452293355930164377407)
        ·
          refine ⟨23292678440033895246566111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15528452293355930164377407 23292678440033895246566111)
          ·
            refine ⟨34939017660050842869849167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23292678440033895246566111 34939017660050842869849167)
            ·
              refine ⟨52408526490076264304773751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34939017660050842869849167 52408526490076264304773751)
              ·
                refine ⟨78612789735114396457160627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52408526490076264304773751 78612789735114396457160627)
                ·
                  refine ⟨117919184602671594685740941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78612789735114396457160627 117919184602671594685740941)
                  ·
                    refine ⟨44219694226001848007152853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117919184602671594685740941 44219694226001848007152853)
                    ·
                      refine ⟨1036399083421918312667645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44219694226001848007152853 1036399083421918312667645)
                      ·
                        rfl

theorem cell23_2018380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_2018380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018380 prefixEnd_2018380 := by exact prefixLift 2018380
  have htrace : WordTrace (prefixWord ++ tailWord_2018380) baseStart_2018380 baseEnd_2018380 := by
    simpa [prefixWord, tailWord_2018380, baseEnd_2018380] using wordTrace_append hprefix tailTrace_2018380
  have hstable : (prefixWord ++ tailWord_2018380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018380).length < 2 ^ (prefixWord ++ tailWord_2018380).sum := by decide
  have hdescent : baseEnd_2018380 < baseStart_2018380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018394 : List Nat := [3, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2]
def baseStart_2018394 : Nat := 118140960795 + 2018394 * 2 ^ 59
def prefixEnd_2018394 : Nat := 4983230072969 + 3 ^ 40 * 2018394 * 2
def baseEnd_2018394 : Nat := 1036406272151081257892581

theorem tailTrace_2018394 : CollatzResearch.WordTrace tailWord_2018394 prefixEnd_2018394 1036406272151081257892581 := by
  unfold tailWord_2018394
  simp only [CollatzResearch.WordTrace]
  refine ⟨18404219262427681774051559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49077918033140484730804157 18404219262427681774051559)
  ·
    refine ⟨27606328893641522661077339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18404219262427681774051559 27606328893641522661077339)
    ·
      refine ⟨41409493340462283991616009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27606328893641522661077339 41409493340462283991616009)
      ·
        refine ⟨31057120005346712993712007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41409493340462283991616009 31057120005346712993712007)
        ·
          refine ⟨46585680008020069490568011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31057120005346712993712007 46585680008020069490568011)
          ·
            refine ⟨69878520012030104235852017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46585680008020069490568011 69878520012030104235852017)
            ·
              refine ⟨52408890009022578176889013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69878520012030104235852017 52408890009022578176889013)
              ·
                refine ⟨4913333438345866704083345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52408890009022578176889013 4913333438345866704083345)
                ·
                  refine ⟨3685000078759400028062509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4913333438345866704083345 3685000078759400028062509)
                  ·
                    refine ⟨1381875029534775010523441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3685000078759400028062509 1381875029534775010523441)
                    ·
                      refine ⟨1036406272151081257892581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1381875029534775010523441 1036406272151081257892581)
                      ·
                        rfl

theorem cell23_2018394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2].length) (baseStart_2018394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018394 prefixEnd_2018394 := by exact prefixLift 2018394
  have htrace : WordTrace (prefixWord ++ tailWord_2018394) baseStart_2018394 baseEnd_2018394 := by
    simpa [prefixWord, tailWord_2018394, baseEnd_2018394] using wordTrace_append hprefix tailTrace_2018394
  have hstable : (prefixWord ++ tailWord_2018394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018394).length < 2 ^ (prefixWord ++ tailWord_2018394).sum := by decide
  have hdescent : baseEnd_2018394 < baseStart_2018394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018401 : List Nat := [1, 2, 3, 1, 1, 2, 3, 5, 1, 1, 3]
def baseStart_2018401 : Nat := 118140960795 + 2018401 * 2 ^ 59
def prefixEnd_2018401 : Nat := 4983230072969 + 3 ^ 40 * 2018401 * 2
def baseEnd_2018401 : Nat := 1036409866515662730505049

theorem tailTrace_2018401 : CollatzResearch.WordTrace tailWord_2018401 prefixEnd_2018401 1036409866515662730505049 := by
  unfold tailWord_2018401
  simp only [CollatzResearch.WordTrace]
  refine ⟨73617132360685367291711057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49078088240456911527807371 73617132360685367291711057)
  ·
    refine ⟨55212849270514025468783293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73617132360685367291711057 55212849270514025468783293)
    ·
      refine ⟨20704818476442759550793735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55212849270514025468783293 20704818476442759550793735)
      ·
        refine ⟨31057227714664139326190603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20704818476442759550793735 31057227714664139326190603)
        ·
          refine ⟨46585841571996208989285905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31057227714664139326190603 46585841571996208989285905)
          ·
            refine ⟨34939381178997156741964429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46585841571996208989285905 34939381178997156741964429)
            ·
              refine ⟨13102267942123933778236661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34939381178997156741964429 13102267942123933778236661)
              ·
                refine ⟨1228337619574118791709687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13102267942123933778236661 1228337619574118791709687)
                ·
                  refine ⟨1842506429361178187564531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1228337619574118791709687 1842506429361178187564531)
                  ·
                    refine ⟨2763759644041767281346797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1842506429361178187564531 2763759644041767281346797)
                    ·
                      refine ⟨1036409866515662730505049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2763759644041767281346797 1036409866515662730505049)
                      ·
                        rfl

theorem cell23_2018401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5, 1, 1, 3].length) (baseStart_2018401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018401 prefixEnd_2018401 := by exact prefixLift 2018401
  have htrace : WordTrace (prefixWord ++ tailWord_2018401) baseStart_2018401 baseEnd_2018401 := by
    simpa [prefixWord, tailWord_2018401, baseEnd_2018401] using wordTrace_append hprefix tailTrace_2018401
  have hstable : (prefixWord ++ tailWord_2018401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018401).length < 2 ^ (prefixWord ++ tailWord_2018401).sum := by decide
  have hdescent : baseEnd_2018401 < baseStart_2018401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018408 : List Nat := [2, 1, 4, 4, 2, 1, 1, 2, 6]
def baseStart_2018408 : Nat := 118140960795 + 2018408 * 2 ^ 59
def prefixEnd_2018408 : Nat := 4983230072969 + 3 ^ 40 * 2018408 * 2
def baseEnd_2018408 : Nat := 115157051208916022568613

theorem tailTrace_2018408 : CollatzResearch.WordTrace tailWord_2018408 prefixEnd_2018408 115157051208916022568613 := by
  unfold tailWord_2018408
  simp only [CollatzResearch.WordTrace]
  refine ⟨36808693835830003743607939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49078258447773338324810585 36808693835830003743607939)
  ·
    refine ⟨55213040753745005615411909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36808693835830003743607939 55213040753745005615411909)
    ·
      refine ⟨10352445141327188552889733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55213040753745005615411909 10352445141327188552889733)
      ·
        refine ⟨1941083463998847853666825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10352445141327188552889733 1941083463998847853666825)
        ·
          refine ⟨1455812597999135890250119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1941083463998847853666825 1455812597999135890250119)
          ·
            refine ⟨2183718896998703835375179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1455812597999135890250119 2183718896998703835375179)
            ·
              refine ⟨3275578345498055753062769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2183718896998703835375179 3275578345498055753062769)
              ·
                refine ⟨2456683759123541814797077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3275578345498055753062769 2456683759123541814797077)
                ·
                  refine ⟨115157051208916022568613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2456683759123541814797077 115157051208916022568613)
                  ·
                    rfl

theorem cell23_2018408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 6].length) (baseStart_2018408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018408 prefixEnd_2018408 := by exact prefixLift 2018408
  have htrace : WordTrace (prefixWord ++ tailWord_2018408) baseStart_2018408 baseEnd_2018408 := by
    simpa [prefixWord, tailWord_2018408, baseEnd_2018408] using wordTrace_append hprefix tailTrace_2018408
  have hstable : (prefixWord ++ tailWord_2018408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018408).length < 2 ^ (prefixWord ++ tailWord_2018408).sum := by decide
  have hdescent : baseEnd_2018408 < baseStart_2018408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018427 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 5, 2, 3]
def baseStart_2018427 : Nat := 118140960795 + 2018427 * 2 ^ 59
def prefixEnd_2018427 : Nat := 4983230072969 + 3 ^ 40 * 2018427 * 2
def baseEnd_2018427 : Nat := 1036423217012679628779929

theorem tailTrace_2018427 : CollatzResearch.WordTrace tailWord_2018427 prefixEnd_2018427 1036423217012679628779929 := by
  unfold tailWord_2018427
  simp only [CollatzResearch.WordTrace]
  refine ⟨73618080658591173732157535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49078720439060782488105023 73618080658591173732157535)
  ·
    refine ⟨110427120987886760598236303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73618080658591173732157535 110427120987886760598236303)
    ·
      refine ⟨165640681481830140897354455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110427120987886760598236303 165640681481830140897354455)
      ·
        refine ⟨248461022222745211346031683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165640681481830140897354455 248461022222745211346031683)
        ·
          refine ⟨372691533334117817019047525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248461022222745211346031683 372691533334117817019047525)
          ·
            refine ⟨69879662500147090691071411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 372691533334117817019047525 69879662500147090691071411)
            ·
              refine ⟨104819493750220636036607117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69879662500147090691071411 104819493750220636036607117)
              ·
                refine ⟨39307310156332738513727669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104819493750220636036607117 39307310156332738513727669)
                ·
                  refine ⟨3685060327156194235661969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39307310156332738513727669 3685060327156194235661969)
                  ·
                    refine ⟨2763795245367145676746477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3685060327156194235661969 2763795245367145676746477)
                    ·
                      refine ⟨1036423217012679628779929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2763795245367145676746477 1036423217012679628779929)
                      ·
                        rfl

theorem cell23_2018427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2, 3].length) (baseStart_2018427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018427 prefixEnd_2018427 := by exact prefixLift 2018427
  have htrace : WordTrace (prefixWord ++ tailWord_2018427) baseStart_2018427 baseEnd_2018427 := by
    simpa [prefixWord, tailWord_2018427, baseEnd_2018427] using wordTrace_append hprefix tailTrace_2018427
  have hstable : (prefixWord ++ tailWord_2018427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018427).length < 2 ^ (prefixWord ++ tailWord_2018427).sum := by decide
  have hdescent : baseEnd_2018427 < baseStart_2018427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018441 : List Nat := [1, 2, 1, 1, 4, 3, 2, 2, 3, 2, 2]
def baseStart_2018441 : Nat := 118140960795 + 2018441 * 2 ^ 59
def prefixEnd_2018441 : Nat := 4983230072969 + 3 ^ 40 * 2018441 * 2
def baseEnd_2018441 : Nat := 1036430405741842574004865

theorem tailTrace_2018441 : CollatzResearch.WordTrace tailWord_2018441 prefixEnd_2018441 1036430405741842574004865 := by
  unfold tailWord_2018441
  simp only [CollatzResearch.WordTrace]
  refine ⟨73618591280540454123167177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49079060853693636082111451 73618591280540454123167177)
  ·
    refine ⟨55213943460405340592375383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73618591280540454123167177 55213943460405340592375383)
    ·
      refine ⟨82820915190608010888563075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55213943460405340592375383 82820915190608010888563075)
      ·
        refine ⟨124231372785912016332844613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82820915190608010888563075 124231372785912016332844613)
        ·
          refine ⟨23293382397358503062408365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124231372785912016332844613 23293382397358503062408365)
          ·
            refine ⟨8735018399009438648403137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23293382397358503062408365 8735018399009438648403137)
            ·
              refine ⟨6551263799257078986302353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8735018399009438648403137 6551263799257078986302353)
              ·
                refine ⟨4913447849442809239726765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6551263799257078986302353 4913447849442809239726765)
                ·
                  refine ⟨1842542943541053464897537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4913447849442809239726765 1842542943541053464897537)
                  ·
                    refine ⟨1381907207655790098673153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1842542943541053464897537 1381907207655790098673153)
                    ·
                      refine ⟨1036430405741842574004865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1381907207655790098673153 1036430405741842574004865)
                      ·
                        rfl

theorem cell23_2018441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3, 2, 2].length) (baseStart_2018441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018441 prefixEnd_2018441 := by exact prefixLift 2018441
  have htrace : WordTrace (prefixWord ++ tailWord_2018441) baseStart_2018441 baseEnd_2018441 := by
    simpa [prefixWord, tailWord_2018441, baseEnd_2018441] using wordTrace_append hprefix tailTrace_2018441
  have hstable : (prefixWord ++ tailWord_2018441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018441).length < 2 ^ (prefixWord ++ tailWord_2018441).sum := by decide
  have hdescent : baseEnd_2018441 < baseStart_2018441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018525 : List Nat := [1, 4, 3, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_2018525 : Nat := 118140960795 + 2018525 * 2 ^ 59
def prefixEnd_2018525 : Nat := 4983230072969 + 3 ^ 40 * 2018525 * 2
def baseEnd_2018525 : Nat := 1036473538116820245354479

theorem tailTrace_2018525 : CollatzResearch.WordTrace tailWord_2018525 prefixEnd_2018525 1036473538116820245354479 := by
  unfold tailWord_2018525
  simp only [CollatzResearch.WordTrace]
  refine ⟨73621655012236136469225029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49081103341490757646150019 73621655012236136469225029)
  ·
    refine ⟨13804060314794275587979693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73621655012236136469225029 13804060314794275587979693)
    ·
      refine ⟨5176522618047853345492385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13804060314794275587979693 5176522618047853345492385)
      ·
        refine ⟨3882391963535890009119289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5176522618047853345492385 3882391963535890009119289)
        ·
          refine ⟨2911793972651917506839467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3882391963535890009119289 2911793972651917506839467)
          ·
            refine ⟨4367690958977876260259201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2911793972651917506839467 4367690958977876260259201)
            ·
              refine ⟨3275768219233407195194401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4367690958977876260259201 3275768219233407195194401)
              ·
                refine ⟨2456826164425055396395801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3275768219233407195194401 2456826164425055396395801)
                ·
                  refine ⟨1842619623318791547296851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2456826164425055396395801 1842619623318791547296851)
                  ·
                    refine ⟨2763929434978187320945277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1842619623318791547296851 2763929434978187320945277)
                    ·
                      refine ⟨1036473538116820245354479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2763929434978187320945277 1036473538116820245354479)
                      ·
                        rfl

theorem cell23_2018525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_2018525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018525 prefixEnd_2018525 := by exact prefixLift 2018525
  have htrace : WordTrace (prefixWord ++ tailWord_2018525) baseStart_2018525 baseEnd_2018525 := by
    simpa [prefixWord, tailWord_2018525, baseEnd_2018525] using wordTrace_append hprefix tailTrace_2018525
  have hstable : (prefixWord ++ tailWord_2018525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018525).length < 2 ^ (prefixWord ++ tailWord_2018525).sum := by decide
  have hdescent : baseEnd_2018525 < baseStart_2018525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018571 : List Nat := [1, 1, 1, 1, 5, 4, 2, 3, 5]
def baseStart_2018571 : Nat := 118140960795 + 2018571 * 2 ^ 59
def prefixEnd_2018571 : Nat := 4983230072969 + 3 ^ 40 * 2018571 * 2
def baseEnd_2018571 : Nat := 115166350914103007264363

theorem tailTrace_2018571 : CollatzResearch.WordTrace tailWord_2018571 prefixEnd_2018571 115166350914103007264363 := by
  unfold tailWord_2018571
  simp only [CollatzResearch.WordTrace]
  refine ⟨73623332770069486325399567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49082221846712990883599711 73623332770069486325399567)
  ·
    refine ⟨110434999155104229488099351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73623332770069486325399567 110434999155104229488099351)
    ·
      refine ⟨165652498732656344232149027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110434999155104229488099351 165652498732656344232149027)
      ·
        refine ⟨248478748098984516348223541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165652498732656344232149027 248478748098984516348223541)
        ·
          refine ⟨23294882634279798407645957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 248478748098984516348223541 23294882634279798407645957)
          ·
            refine ⟨4367790493927462201433617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23294882634279798407645957 4367790493927462201433617)
            ·
              refine ⟨3275842870445596651075213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4367790493927462201433617 3275842870445596651075213)
              ·
                refine ⟨1228441076417098744153205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3275842870445596651075213 1228441076417098744153205)
                ·
                  refine ⟨115166350914103007264363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1228441076417098744153205 115166350914103007264363)
                  ·
                    rfl

theorem cell23_2018571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3, 5].length) (baseStart_2018571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018571 prefixEnd_2018571 := by exact prefixLift 2018571
  have htrace : WordTrace (prefixWord ++ tailWord_2018571) baseStart_2018571 baseEnd_2018571 := by
    simpa [prefixWord, tailWord_2018571, baseEnd_2018571] using wordTrace_append hprefix tailTrace_2018571
  have hstable : (prefixWord ++ tailWord_2018571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018571).length < 2 ^ (prefixWord ++ tailWord_2018571).sum := by decide
  have hdescent : baseEnd_2018571 < baseStart_2018571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018624 : List Nat := [2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 3]
def baseStart_2018624 : Nat := 118140960795 + 2018624 * 2 ^ 59
def prefixEnd_2018624 : Nat := 4983230072969 + 3 ^ 40 * 2018624 * 2
def baseEnd_2018624 : Nat := 1036524372701615358016523

theorem tailTrace_2018624 : CollatzResearch.WordTrace tailWord_2018624 prefixEnd_2018624 1036524372701615358016523 := by
  unfold tailWord_2018624
  simp only [CollatzResearch.WordTrace]
  refine ⟨36812632919438738188539463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49083510559251650918052617 36812632919438738188539463)
  ·
    refine ⟨55218949379158107282809195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36812632919438738188539463 55218949379158107282809195)
    ·
      refine ⟨82828424068737160924213793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55218949379158107282809195 82828424068737160924213793)
      ·
        refine ⟨62121318051552870693160345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82828424068737160924213793 62121318051552870693160345)
        ·
          refine ⟨46590988538664653019870259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62121318051552870693160345 46590988538664653019870259)
          ·
            refine ⟨69886482807996979529805389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46590988538664653019870259 69886482807996979529805389)
            ·
              refine ⟨26207431052998867323677021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69886482807996979529805389 26207431052998867323677021)
              ·
                refine ⟨9827786644874575246378883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26207431052998867323677021 9827786644874575246378883)
                ·
                  refine ⟨14741679967311862869568325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9827786644874575246378883 14741679967311862869568325)
                  ·
                    refine ⟨2764064993870974288044061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14741679967311862869568325 2764064993870974288044061)
                    ·
                      refine ⟨1036524372701615358016523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2764064993870974288044061 1036524372701615358016523)
                      ·
                        rfl

theorem cell23_2018624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 3].length) (baseStart_2018624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018624 prefixEnd_2018624 := by exact prefixLift 2018624
  have htrace : WordTrace (prefixWord ++ tailWord_2018624) baseStart_2018624 baseEnd_2018624 := by
    simpa [prefixWord, tailWord_2018624, baseEnd_2018624] using wordTrace_append hprefix tailTrace_2018624
  have hstable : (prefixWord ++ tailWord_2018624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018624).length < 2 ^ (prefixWord ++ tailWord_2018624).sum := by decide
  have hdescent : baseEnd_2018624 < baseStart_2018624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018641 : List Nat := [1, 2, 2, 1, 4, 1, 3, 2, 2, 2, 3]
def baseStart_2018641 : Nat := 118140960795 + 2018641 * 2 ^ 59
def prefixEnd_2018641 : Nat := 4983230072969 + 3 ^ 40 * 2018641 * 2
def baseEnd_2018641 : Nat := 1036533101872741791503945

theorem tailTrace_2018641 : CollatzResearch.WordTrace tailWord_2018641 prefixEnd_2018641 1036533101872741791503945 := by
  unfold tailWord_2018641
  simp only [CollatzResearch.WordTrace]
  refine ⟨73625885879815888280447777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49083923919877258853631851 73625885879815888280447777)
  ·
    refine ⟨55219414409861916210335833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73625885879815888280447777 55219414409861916210335833)
    ·
      refine ⟨41414560807396437157751875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55219414409861916210335833 41414560807396437157751875)
      ·
        refine ⟨62121841211094655736627813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41414560807396437157751875 62121841211094655736627813)
        ·
          refine ⟨11647845227080247950617715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62121841211094655736627813 11647845227080247950617715)
          ·
            refine ⟨17471767840620371925926573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11647845227080247950617715 17471767840620371925926573)
            ·
              refine ⟨6551912940232639472222465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17471767840620371925926573 6551912940232639472222465)
              ·
                refine ⟨4913934705174479604166849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6551912940232639472222465 4913934705174479604166849)
                ·
                  refine ⟨3685451028880859703125137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4913934705174479604166849 3685451028880859703125137)
                  ·
                    refine ⟨2764088271660644777343853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3685451028880859703125137 2764088271660644777343853)
                    ·
                      refine ⟨1036533101872741791503945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2764088271660644777343853 1036533101872741791503945)
                      ·
                        rfl

theorem cell23_2018641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 2, 3].length) (baseStart_2018641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018641 prefixEnd_2018641 := by exact prefixLift 2018641
  have htrace : WordTrace (prefixWord ++ tailWord_2018641) baseStart_2018641 baseEnd_2018641 := by
    simpa [prefixWord, tailWord_2018641, baseEnd_2018641] using wordTrace_append hprefix tailTrace_2018641
  have hstable : (prefixWord ++ tailWord_2018641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018641).length < 2 ^ (prefixWord ++ tailWord_2018641).sum := by decide
  have hdescent : baseEnd_2018641 < baseStart_2018641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018644 : List Nat := [2, 4, 1, 1, 2, 1, 1, 3, 8]
def baseStart_2018644 : Nat := 118140960795 + 2018644 * 2 ^ 59
def prefixEnd_2018644 : Nat := 4983230072969 + 3 ^ 40 * 2018644 * 2
def baseEnd_2018644 : Nat := 115170515812745031085159

theorem tailTrace_2018644 : CollatzResearch.WordTrace tailWord_2018644 prefixEnd_2018644 115170515812745031085159 := by
  unfold tailWord_2018644
  simp only [CollatzResearch.WordTrace]
  refine ⟨36812997649402509896403493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49083996865870013195204657 36812997649402509896403493)
  ·
    refine ⟨6902437059262970605575655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36812997649402509896403493 6902437059262970605575655)
    ·
      refine ⟨10353655588894455908363483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6902437059262970605575655 10353655588894455908363483)
      ·
        refine ⟨15530483383341683862545225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10353655588894455908363483 15530483383341683862545225)
        ·
          refine ⟨11647862537506262896908919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15530483383341683862545225 11647862537506262896908919)
          ·
            refine ⟨17471793806259394345363379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11647862537506262896908919 17471793806259394345363379)
            ·
              refine ⟨26207690709389091518045069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17471793806259394345363379 26207690709389091518045069)
              ·
                refine ⟨9827884016020909319266901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26207690709389091518045069 9827884016020909319266901)
                ·
                  refine ⟨115170515812745031085159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9827884016020909319266901 115170515812745031085159)
                  ·
                    rfl

theorem cell23_2018644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_2018644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018644 prefixEnd_2018644 := by exact prefixLift 2018644
  have htrace : WordTrace (prefixWord ++ tailWord_2018644) baseStart_2018644 baseEnd_2018644 := by
    simpa [prefixWord, tailWord_2018644, baseEnd_2018644] using wordTrace_append hprefix tailTrace_2018644
  have hstable : (prefixWord ++ tailWord_2018644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018644).length < 2 ^ (prefixWord ++ tailWord_2018644).sum := by decide
  have hdescent : baseEnd_2018644 < baseStart_2018644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018671 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 5, 1, 3]
def baseStart_2018671 : Nat := 118140960795 + 2018671 * 2 ^ 59
def prefixEnd_2018671 : Nat := 4983230072969 + 3 ^ 40 * 2018671 * 2
def baseEnd_2018671 : Nat := 1036548506292376674128807

theorem tailTrace_2018671 : CollatzResearch.WordTrace tailWord_2018671 prefixEnd_2018671 1036548506292376674128807 := by
  unfold tailWord_2018671
  simp only [CollatzResearch.WordTrace]
  refine ⟨73626980069707203404039867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49084653379804802269359911 73626980069707203404039867)
  ·
    refine ⟨110440470104560805106059801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73626980069707203404039867 110440470104560805106059801)
    ·
      refine ⟨82830352578420603829544851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110440470104560805106059801 82830352578420603829544851)
      ·
        refine ⟨124245528867630905744317277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82830352578420603829544851 124245528867630905744317277)
        ·
          refine ⟨46592073325361589654118979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124245528867630905744317277 46592073325361589654118979)
          ·
            refine ⟨69888109988042384481178469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46592073325361589654118979 69888109988042384481178469)
            ·
              refine ⟨13104020622757947090220963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69888109988042384481178469 13104020622757947090220963)
              ·
                refine ⟨19656030934136920635331445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13104020622757947090220963 19656030934136920635331445)
                ·
                  refine ⟨1842752900075336309562323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19656030934136920635331445 1842752900075336309562323)
                  ·
                    refine ⟨2764129350113004464343485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1842752900075336309562323 2764129350113004464343485)
                    ·
                      refine ⟨1036548506292376674128807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2764129350113004464343485 1036548506292376674128807)
                      ·
                        rfl

theorem cell23_2018671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 1, 3].length) (baseStart_2018671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018671 prefixEnd_2018671 := by exact prefixLift 2018671
  have htrace : WordTrace (prefixWord ++ tailWord_2018671) baseStart_2018671 baseEnd_2018671 := by
    simpa [prefixWord, tailWord_2018671, baseEnd_2018671] using wordTrace_append hprefix tailTrace_2018671
  have hstable : (prefixWord ++ tailWord_2018671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018671).length < 2 ^ (prefixWord ++ tailWord_2018671).sum := by decide
  have hdescent : baseEnd_2018671 < baseStart_2018671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018681 : List Nat := [1, 2, 1, 3, 2, 1, 2, 3, 1, 5, 2]
def baseStart_2018681 : Nat := 118140960795 + 2018681 * 2 ^ 59
def prefixEnd_2018681 : Nat := 4983230072969 + 3 ^ 40 * 2018681 * 2
def baseEnd_2018681 : Nat := 1036553641098921635003761

theorem tailTrace_2018681 : CollatzResearch.WordTrace tailWord_2018681 prefixEnd_2018681 1036553641098921635003761 := by
  unfold tailWord_2018681
  simp only [CollatzResearch.WordTrace]
  refine ⟨73627344799670975111903897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49084896533113983407935931 73627344799670975111903897)
  ·
    refine ⟨55220508599753231333927923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73627344799670975111903897 55220508599753231333927923)
    ·
      refine ⟨82830762899629847000891885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55220508599753231333927923 82830762899629847000891885)
      ·
        refine ⟨31061536087361192625334457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82830762899629847000891885 31061536087361192625334457)
        ·
          refine ⟨23296152065520894469000843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31061536087361192625334457 23296152065520894469000843)
          ·
            refine ⟨34944228098281341703501265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23296152065520894469000843 34944228098281341703501265)
            ·
              refine ⟨26208171073711006277625949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34944228098281341703501265 26208171073711006277625949)
              ·
                refine ⟨9828064152641627354109731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26208171073711006277625949 9828064152641627354109731)
                ·
                  refine ⟨14742096228962441031164597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9828064152641627354109731 14742096228962441031164597)
                  ·
                    refine ⟨1382071521465228846671681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14742096228962441031164597 1382071521465228846671681)
                    ·
                      refine ⟨1036553641098921635003761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1382071521465228846671681 1036553641098921635003761)
                      ·
                        rfl

theorem cell23_2018681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 5, 2].length) (baseStart_2018681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018681 prefixEnd_2018681 := by exact prefixLift 2018681
  have htrace : WordTrace (prefixWord ++ tailWord_2018681) baseStart_2018681 baseEnd_2018681 := by
    simpa [prefixWord, tailWord_2018681, baseEnd_2018681] using wordTrace_append hprefix tailTrace_2018681
  have hstable : (prefixWord ++ tailWord_2018681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018681).length < 2 ^ (prefixWord ++ tailWord_2018681).sum := by decide
  have hdescent : baseEnd_2018681 < baseStart_2018681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018711 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 2, 6, 2]
def baseStart_2018711 : Nat := 118140960795 + 2018711 * 2 ^ 59
def prefixEnd_2018711 : Nat := 4983230072969 + 3 ^ 40 * 2018711 * 2
def baseEnd_2018711 : Nat := 1036569045518556517628623

theorem tailTrace_2018711 : CollatzResearch.WordTrace tailWord_2018711 prefixEnd_2018711 1036569045518556517628623 := by
  unfold tailWord_2018711
  simp only [CollatzResearch.WordTrace]
  refine ⟨73628438989562290235495987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49085625993041526823663991 73628438989562290235495987)
  ·
    refine ⟨110442658484343435353243981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73628438989562290235495987 110442658484343435353243981)
    ·
      refine ⟨41415996931628788257466493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110442658484343435353243981 41415996931628788257466493)
      ·
        refine ⟨15530998849360795596549935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41415996931628788257466493 15530998849360795596549935)
        ·
          refine ⟨23296498274041193394824903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15530998849360795596549935 23296498274041193394824903)
          ·
            refine ⟨34944747411061790092237355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23296498274041193394824903 34944747411061790092237355)
            ·
              refine ⟨52417121116592685138356033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34944747411061790092237355 52417121116592685138356033)
              ·
                refine ⟨39312840837444513853767025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52417121116592685138356033 39312840837444513853767025)
                ·
                  refine ⟨29484630628083385390325269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39312840837444513853767025 29484630628083385390325269)
                  ·
                    refine ⟨1382092060691408690171497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29484630628083385390325269 1382092060691408690171497)
                    ·
                      refine ⟨1036569045518556517628623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1382092060691408690171497 1036569045518556517628623)
                      ·
                        rfl

theorem cell23_2018711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_2018711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018711 prefixEnd_2018711 := by exact prefixLift 2018711
  have htrace : WordTrace (prefixWord ++ tailWord_2018711) baseStart_2018711 baseEnd_2018711 := by
    simpa [prefixWord, tailWord_2018711, baseEnd_2018711] using wordTrace_append hprefix tailTrace_2018711
  have hstable : (prefixWord ++ tailWord_2018711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018711).length < 2 ^ (prefixWord ++ tailWord_2018711).sum := by decide
  have hdescent : baseEnd_2018711 < baseStart_2018711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018762 : List Nat := [3, 1, 2, 1, 2, 3, 2, 4, 1, 2, 2]
def baseStart_2018762 : Nat := 118140960795 + 2018762 * 2 ^ 59
def prefixEnd_2018762 : Nat := 4983230072969 + 3 ^ 40 * 2018762 * 2
def baseEnd_2018762 : Nat := 1036595233031935818090889

theorem tailTrace_2018762 : CollatzResearch.WordTrace tailWord_2018762 prefixEnd_2018762 1036595233031935818090889 := by
  unfold tailWord_2018762
  simp only [CollatzResearch.WordTrace]
  refine ⟨18407574778094381486400635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49086866074918350630401693 18407574778094381486400635)
  ·
    refine ⟨27611362167141572229600953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18407574778094381486400635 27611362167141572229600953)
    ·
      refine ⟨20708521625356179172200715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27611362167141572229600953 20708521625356179172200715)
      ·
        refine ⟨31062782438034268758301073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20708521625356179172200715 31062782438034268758301073)
        ·
          refine ⟨23297086828525701568725805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31062782438034268758301073 23297086828525701568725805)
          ·
            refine ⟨8736407560697138088272177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23297086828525701568725805 8736407560697138088272177)
            ·
              refine ⟨6552305670522853566204133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8736407560697138088272177 6552305670522853566204133)
              ·
                refine ⟨1228557313223035043663275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6552305670522853566204133 1228557313223035043663275)
                ·
                  refine ⟨1842835969834552565494913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1228557313223035043663275 1842835969834552565494913)
                  ·
                    refine ⟨1382126977375914424121185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1842835969834552565494913 1382126977375914424121185)
                    ·
                      refine ⟨1036595233031935818090889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1382126977375914424121185 1036595233031935818090889)
                      ·
                        rfl

theorem cell23_2018762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4, 1, 2, 2].length) (baseStart_2018762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018762 prefixEnd_2018762 := by exact prefixLift 2018762
  have htrace : WordTrace (prefixWord ++ tailWord_2018762) baseStart_2018762 baseEnd_2018762 := by
    simpa [prefixWord, tailWord_2018762, baseEnd_2018762] using wordTrace_append hprefix tailTrace_2018762
  have hstable : (prefixWord ++ tailWord_2018762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018762).length < 2 ^ (prefixWord ++ tailWord_2018762).sum := by decide
  have hdescent : baseEnd_2018762 < baseStart_2018762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018772 : List Nat := [2, 4, 1, 2, 3, 1, 3, 1, 2, 4]
def baseStart_2018772 : Nat := 118140960795 + 2018772 * 2 ^ 59
def prefixEnd_2018772 : Nat := 4983230072969 + 3 ^ 40 * 2018772 * 2
def baseEnd_2018772 : Nat := 345533455946160259655281

theorem tailTrace_2018772 : CollatzResearch.WordTrace tailWord_2018772 prefixEnd_2018772 345533455946160259655281 := by
  unfold tailWord_2018772
  simp only [CollatzResearch.WordTrace]
  refine ⟨36815331921170648826733285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49087109228227531768977713 36815331921170648826733285)
  ·
    refine ⟨6902874735219496655012491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36815331921170648826733285 6902874735219496655012491)
    ·
      refine ⟨10354312102829244982518737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6902874735219496655012491 10354312102829244982518737)
      ·
        refine ⟨7765734077121933736889053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10354312102829244982518737 7765734077121933736889053)
        ·
          refine ⟨2912150278920725151333395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7765734077121933736889053 2912150278920725151333395)
          ·
            refine ⟨4368225418381087727000093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2912150278920725151333395 4368225418381087727000093)
            ·
              refine ⟨1638084531892907897625035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4368225418381087727000093 1638084531892907897625035)
              ·
                refine ⟨2457126797839361846437553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1638084531892907897625035 2457126797839361846437553)
                ·
                  refine ⟨1842845098379521384828165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2457126797839361846437553 1842845098379521384828165)
                  ·
                    refine ⟨345533455946160259655281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1842845098379521384828165 345533455946160259655281)
                    ·
                      rfl

theorem cell23_2018772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_2018772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018772 prefixEnd_2018772 := by exact prefixLift 2018772
  have htrace : WordTrace (prefixWord ++ tailWord_2018772) baseStart_2018772 baseEnd_2018772 := by
    simpa [prefixWord, tailWord_2018772, baseEnd_2018772] using wordTrace_append hprefix tailTrace_2018772
  have hstable : (prefixWord ++ tailWord_2018772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018772).length < 2 ^ (prefixWord ++ tailWord_2018772).sum := by decide
  have hdescent : baseEnd_2018772 < baseStart_2018772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018778 : List Nat := [3, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3]
def baseStart_2018778 : Nat := 118140960795 + 2018778 * 2 ^ 59
def prefixEnd_2018778 : Nat := 4983230072969 + 3 ^ 40 * 2018778 * 2
def baseEnd_2018778 : Nat := 1036603448722407755490815

theorem tailTrace_2018778 : CollatzResearch.WordTrace tailWord_2018778 prefixEnd_2018778 1036603448722407755490815 := by
  unfold tailWord_2018778
  simp only [CollatzResearch.WordTrace]
  refine ⟨18407720670079890169546247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49087255120213040452123325 18407720670079890169546247)
  ·
    refine ⟨27611581005119835254319371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18407720670079890169546247 27611581005119835254319371)
    ·
      refine ⟨41417371507679752881479057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27611581005119835254319371 41417371507679752881479057)
      ·
        refine ⟨31063028630759814661109293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41417371507679752881479057 31063028630759814661109293)
        ·
          refine ⟨11648635736534930497915985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31063028630759814661109293 11648635736534930497915985)
          ·
            refine ⟨8736476802401197873436989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11648635736534930497915985 8736476802401197873436989)
            ·
              refine ⟨3276178800900449202538871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8736476802401197873436989 3276178800900449202538871)
              ·
                refine ⟨4914268201350673803808307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3276178800900449202538871 4914268201350673803808307)
                ·
                  refine ⟨7371402302026010705712461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4914268201350673803808307 7371402302026010705712461)
                  ·
                    refine ⟨2764275863259754014642173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7371402302026010705712461 2764275863259754014642173)
                    ·
                      refine ⟨1036603448722407755490815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2764275863259754014642173 1036603448722407755490815)
                      ·
                        rfl

theorem cell23_2018778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_2018778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018778 prefixEnd_2018778 := by exact prefixLift 2018778
  have htrace : WordTrace (prefixWord ++ tailWord_2018778) baseStart_2018778 baseEnd_2018778 := by
    simpa [prefixWord, tailWord_2018778, baseEnd_2018778] using wordTrace_append hprefix tailTrace_2018778
  have hstable : (prefixWord ++ tailWord_2018778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018778).length < 2 ^ (prefixWord ++ tailWord_2018778).sum := by decide
  have hdescent : baseEnd_2018778 < baseStart_2018778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018784 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 8]
def baseStart_2018784 : Nat := 118140960795 + 2018784 * 2 ^ 59
def prefixEnd_2018784 : Nat := 4983230072969 + 3 ^ 40 * 2018784 * 2
def baseEnd_2018784 : Nat := 1036606529606334732015787

theorem tailTrace_2018784 : CollatzResearch.WordTrace tailWord_2018784 prefixEnd_2018784 1036606529606334732015787 := by
  unfold tailWord_2018784
  simp only [CollatzResearch.WordTrace]
  refine ⟨36815550759148911851451703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49087401012198549135268937 36815550759148911851451703)
  ·
    refine ⟨55223326138723367777177555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36815550759148911851451703 55223326138723367777177555)
    ·
      refine ⟨82834989208085051665766333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55223326138723367777177555 82834989208085051665766333)
      ·
        refine ⟨31063120953031894374662375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82834989208085051665766333 31063120953031894374662375)
        ·
          refine ⟨46594681429547841561993563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31063120953031894374662375 46594681429547841561993563)
          ·
            refine ⟨69892022144321762342990345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46594681429547841561993563 69892022144321762342990345)
            ·
              refine ⟨52419016608241321757242759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69892022144321762342990345 52419016608241321757242759)
              ·
                refine ⟨78628524912361982635864139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52419016608241321757242759 78628524912361982635864139)
                ·
                  refine ⟨117942787368542973953796209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78628524912361982635864139 117942787368542973953796209)
                  ·
                    refine ⟨88457090526407230465347157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117942787368542973953796209 88457090526407230465347157)
                    ·
                      refine ⟨1036606529606334732015787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 88457090526407230465347157 1036606529606334732015787)
                      ·
                        rfl

theorem cell23_2018784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_2018784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018784 prefixEnd_2018784 := by exact prefixLift 2018784
  have htrace : WordTrace (prefixWord ++ tailWord_2018784) baseStart_2018784 baseEnd_2018784 := by
    simpa [prefixWord, tailWord_2018784, baseEnd_2018784] using wordTrace_append hprefix tailTrace_2018784
  have hstable : (prefixWord ++ tailWord_2018784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018784).length < 2 ^ (prefixWord ++ tailWord_2018784).sum := by decide
  have hdescent : baseEnd_2018784 < baseStart_2018784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018788 : List Nat := [2, 3, 1, 1, 1, 1, 1, 5, 3, 3, 2]
def baseStart_2018788 : Nat := 118140960795 + 2018788 * 2 ^ 59
def prefixEnd_2018788 : Nat := 4983230072969 + 3 ^ 40 * 2018788 * 2
def baseEnd_2018788 : Nat := 1036608583528952716365769

theorem tailTrace_2018788 : CollatzResearch.WordTrace tailWord_2018788 prefixEnd_2018788 1036608583528952716365769 := by
  unfold tailWord_2018788
  simp only [CollatzResearch.WordTrace]
  refine ⟨36815623705141666193024509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49087498273522221590699345 36815623705141666193024509)
  ·
    refine ⟨13805858889428124822384191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36815623705141666193024509 13805858889428124822384191)
    ·
      refine ⟨20708788334142187233576287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13805858889428124822384191 20708788334142187233576287)
      ·
        refine ⟨31063182501213280850364431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20708788334142187233576287 31063182501213280850364431)
        ·
          refine ⟨46594773751819921275546647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31063182501213280850364431 46594773751819921275546647)
          ·
            refine ⟨69892160627729881913319971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46594773751819921275546647 69892160627729881913319971)
            ·
              refine ⟨104838240941594822869979957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69892160627729881913319971 104838240941594822869979957)
              ·
                refine ⟨9828585088274514644060621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104838240941594822869979957 9828585088274514644060621)
                ·
                  refine ⟨3685719408102942991522733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9828585088274514644060621 3685719408102942991522733)
                  ·
                    refine ⟨1382144778038603621821025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3685719408102942991522733 1382144778038603621821025)
                    ·
                      refine ⟨1036608583528952716365769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1382144778038603621821025 1036608583528952716365769)
                      ·
                        rfl

theorem cell23_2018788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 3, 3, 2].length) (baseStart_2018788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018788 prefixEnd_2018788 := by exact prefixLift 2018788
  have htrace : WordTrace (prefixWord ++ tailWord_2018788) baseStart_2018788 baseEnd_2018788 := by
    simpa [prefixWord, tailWord_2018788, baseEnd_2018788] using wordTrace_append hprefix tailTrace_2018788
  have hstable : (prefixWord ++ tailWord_2018788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018788).length < 2 ^ (prefixWord ++ tailWord_2018788).sum := by decide
  have hdescent : baseEnd_2018788 < baseStart_2018788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018791 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_2018791 : Nat := 118140960795 + 2018791 * 2 ^ 59
def prefixEnd_2018791 : Nat := 4983230072969 + 3 ^ 40 * 2018791 * 2
def baseEnd_2018791 : Nat := 1036610123970916204628255

theorem tailTrace_2018791 : CollatzResearch.WordTrace tailWord_2018791 prefixEnd_2018791 1036610123970916204628255 := by
  unfold tailWord_2018791
  simp only [CollatzResearch.WordTrace]
  refine ⟨73631356829272463898408227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49087571219514975932272151 73631356829272463898408227)
  ·
    refine ⟨110447035243908695847612341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73631356829272463898408227 110447035243908695847612341)
    ·
      refine ⟨10354409554116440235713657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110447035243908695847612341 10354409554116440235713657)
      ·
        refine ⟨7765807165587330176785243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10354409554116440235713657 7765807165587330176785243)
        ·
          refine ⟨11648710748380995265177865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7765807165587330176785243 11648710748380995265177865)
          ·
            refine ⟨8736533061285746448883399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11648710748380995265177865 8736533061285746448883399)
            ·
              refine ⟨13104799591928619673325099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8736533061285746448883399 13104799591928619673325099)
              ·
                refine ⟨19657199387892929509987649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13104799591928619673325099 19657199387892929509987649)
                ·
                  refine ⟨14742899540919697132490737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19657199387892929509987649 14742899540919697132490737)
                  ·
                    refine ⟨11057174655689772849368053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14742899540919697132490737 11057174655689772849368053)
                    ·
                      refine ⟨1036610123970916204628255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11057174655689772849368053 1036610123970916204628255)
                      ·
                        rfl

theorem cell23_2018791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_2018791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018791 prefixEnd_2018791 := by exact prefixLift 2018791
  have htrace : WordTrace (prefixWord ++ tailWord_2018791) baseStart_2018791 baseEnd_2018791 := by
    simpa [prefixWord, tailWord_2018791, baseEnd_2018791] using wordTrace_append hprefix tailTrace_2018791
  have hstable : (prefixWord ++ tailWord_2018791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018791).length < 2 ^ (prefixWord ++ tailWord_2018791).sum := by decide
  have hdescent : baseEnd_2018791 < baseStart_2018791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018821 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 2, 4, 3]
def baseStart_2018821 : Nat := 118140960795 + 2018821 * 2 ^ 59
def prefixEnd_2018821 : Nat := 4983230072969 + 3 ^ 40 * 2018821 * 2
def baseEnd_2018821 : Nat := 1036625528390551087253117

theorem tailTrace_2018821 : CollatzResearch.WordTrace tailWord_2018821 prefixEnd_2018821 1036625528390551087253117 := by
  unfold tailWord_2018821
  simp only [CollatzResearch.WordTrace]
  refine ⟨73632451019163779022000317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49088300679442519348000211 73632451019163779022000317)
  ·
    refine ⟨27612169132186417133250119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73632451019163779022000317 27612169132186417133250119)
    ·
      refine ⟨41418253698279625699875179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27612169132186417133250119 41418253698279625699875179)
      ·
        refine ⟨62127380547419438549812769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41418253698279625699875179 62127380547419438549812769)
        ·
          refine ⟨46595535410564578912359577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62127380547419438549812769 46595535410564578912359577)
          ·
            refine ⟨34946651557923434184269683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46595535410564578912359577 34946651557923434184269683)
            ·
              refine ⟨52419977336885151276404525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34946651557923434184269683 52419977336885151276404525)
              ·
                refine ⟨19657491501331931728651697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52419977336885151276404525 19657491501331931728651697)
                ·
                  refine ⟨14743118625998948796488773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19657491501331931728651697 14743118625998948796488773)
                  ·
                    refine ⟨2764334742374802899341645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14743118625998948796488773 2764334742374802899341645)
                    ·
                      refine ⟨1036625528390551087253117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2764334742374802899341645 1036625528390551087253117)
                      ·
                        rfl

theorem cell23_2018821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 4, 3].length) (baseStart_2018821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018821 prefixEnd_2018821 := by exact prefixLift 2018821
  have htrace : WordTrace (prefixWord ++ tailWord_2018821) baseStart_2018821 baseEnd_2018821 := by
    simpa [prefixWord, tailWord_2018821, baseEnd_2018821] using wordTrace_append hprefix tailTrace_2018821
  have hstable : (prefixWord ++ tailWord_2018821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018821).length < 2 ^ (prefixWord ++ tailWord_2018821).sum := by decide
  have hdescent : baseEnd_2018821 < baseStart_2018821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018891 : List Nat := [1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 4]
def baseStart_2018891 : Nat := 118140960795 + 2018891 * 2 ^ 59
def prefixEnd_2018891 : Nat := 4983230072969 + 3 ^ 40 * 2018891 * 2
def baseEnd_2018891 : Nat := 1036661472036365813377795

theorem tailTrace_2018891 : CollatzResearch.WordTrace tailWord_2018891 prefixEnd_2018891 1036661472036365813377795 := by
  unfold tailWord_2018891
  simp only [CollatzResearch.WordTrace]
  refine ⟨73635004128910180977048527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49090002752606787318032351 73635004128910180977048527)
  ·
    refine ⟨110452506193365271465572791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73635004128910180977048527 110452506193365271465572791)
    ·
      refine ⟨165678759290047907198359187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110452506193365271465572791 165678759290047907198359187)
      ·
        refine ⟨248518138935071860797538781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165678759290047907198359187 248518138935071860797538781)
        ·
          refine ⟨93194302100651947799077043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248518138935071860797538781 93194302100651947799077043)
          ·
            refine ⟨139791453150977921698615565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93194302100651947799077043 139791453150977921698615565)
            ·
              refine ⟨52421794931616720636980837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139791453150977921698615565 52421794931616720636980837)
              ·
                refine ⟨9829086549678135119433907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52421794931616720636980837 9829086549678135119433907)
                ·
                  refine ⟨14743629824517202679150861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9829086549678135119433907 14743629824517202679150861)
                  ·
                    refine ⟨5528861184193951004681573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14743629824517202679150861 5528861184193951004681573)
                    ·
                      refine ⟨1036661472036365813377795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5528861184193951004681573 1036661472036365813377795)
                      ·
                        rfl

theorem cell23_2018891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 4].length) (baseStart_2018891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018891 prefixEnd_2018891 := by exact prefixLift 2018891
  have htrace : WordTrace (prefixWord ++ tailWord_2018891) baseStart_2018891 baseEnd_2018891 := by
    simpa [prefixWord, tailWord_2018891, baseEnd_2018891] using wordTrace_append hprefix tailTrace_2018891
  have hstable : (prefixWord ++ tailWord_2018891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018891).length < 2 ^ (prefixWord ++ tailWord_2018891).sum := by decide
  have hdescent : baseEnd_2018891 < baseStart_2018891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018909 : List Nat := [1, 4, 4, 2, 1, 1, 2, 3, 5]
def baseStart_2018909 : Nat := 118140960795 + 2018909 * 2 ^ 59
def prefixEnd_2018909 : Nat := 4983230072969 + 3 ^ 40 * 2018909 * 2
def baseEnd_2018909 : Nat := 115185634965349638105857

theorem tailTrace_2018909 : CollatzResearch.WordTrace tailWord_2018909 prefixEnd_2018909 115185634965349638105857 := by
  unfold tailWord_2018909
  simp only [CollatzResearch.WordTrace]
  refine ⟨73635660642844970051203781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49090440428563313367469187 73635660642844970051203781)
  ·
    refine ⟨13806686370533431884600709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73635660642844970051203781 13806686370533431884600709)
    ·
      refine ⟨2588753694475018478362633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13806686370533431884600709 2588753694475018478362633)
      ·
        refine ⟨1941565270856263858771975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2588753694475018478362633 1941565270856263858771975)
        ·
          refine ⟨2912347906284395788157963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1941565270856263858771975 2912347906284395788157963)
          ·
            refine ⟨4368521859426593682236945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2912347906284395788157963 4368521859426593682236945)
            ·
              refine ⟨3276391394569945261677709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4368521859426593682236945 3276391394569945261677709)
              ·
                refine ⟨1228646772963729473129141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3276391394569945261677709 1228646772963729473129141)
                ·
                  refine ⟨115185634965349638105857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1228646772963729473129141 115185634965349638105857)
                  ·
                    rfl

theorem cell23_2018909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3, 5].length) (baseStart_2018909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018909 prefixEnd_2018909 := by exact prefixLift 2018909
  have htrace : WordTrace (prefixWord ++ tailWord_2018909) baseStart_2018909 baseEnd_2018909 := by
    simpa [prefixWord, tailWord_2018909, baseEnd_2018909] using wordTrace_append hprefix tailTrace_2018909
  have hstable : (prefixWord ++ tailWord_2018909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018909).length < 2 ^ (prefixWord ++ tailWord_2018909).sum := by decide
  have hdescent : baseEnd_2018909 < baseStart_2018909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018921 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 2, 1, 6]
def baseStart_2018921 : Nat := 118140960795 + 2018921 * 2 ^ 59
def prefixEnd_2018921 : Nat := 4983230072969 + 3 ^ 40 * 2018921 * 2
def baseEnd_2018921 : Nat := 1036676876456000696002657

theorem tailTrace_2018921 : CollatzResearch.WordTrace tailWord_2018921 prefixEnd_2018921 1036676876456000696002657 := by
  unfold tailWord_2018921
  simp only [CollatzResearch.WordTrace]
  refine ⟨73636098318801496100640617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49090732212534330733760411 73636098318801496100640617)
  ·
    refine ⟨55227073739101122075480463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73636098318801496100640617 55227073739101122075480463)
    ·
      refine ⟨82840610608651683113220695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55227073739101122075480463 82840610608651683113220695)
      ·
        refine ⟨124260915912977524669831043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82840610608651683113220695 124260915912977524669831043)
        ·
          refine ⟨186391373869466287004746565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124260915912977524669831043 186391373869466287004746565)
          ·
            refine ⟨34948382600524928813389981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186391373869466287004746565 34948382600524928813389981)
            ·
              refine ⟨13105643475196848305021243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34948382600524928813389981 13105643475196848305021243)
              ·
                refine ⟨19658465212795272457531865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13105643475196848305021243 19658465212795272457531865)
                ·
                  refine ⟨14743848909596454343148899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19658465212795272457531865 14743848909596454343148899)
                  ·
                    refine ⟨22115773364394681514723349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14743848909596454343148899 22115773364394681514723349)
                    ·
                      refine ⟨1036676876456000696002657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22115773364394681514723349 1036676876456000696002657)
                      ·
                        rfl

theorem cell23_2018921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 1, 6].length) (baseStart_2018921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018921 prefixEnd_2018921 := by exact prefixLift 2018921
  have htrace : WordTrace (prefixWord ++ tailWord_2018921) baseStart_2018921 baseEnd_2018921 := by
    simpa [prefixWord, tailWord_2018921, baseEnd_2018921] using wordTrace_append hprefix tailTrace_2018921
  have hstable : (prefixWord ++ tailWord_2018921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018921).length < 2 ^ (prefixWord ++ tailWord_2018921).sum := by decide
  have hdescent : baseEnd_2018921 < baseStart_2018921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018992 : List Nat := [2, 1, 1, 1, 2, 1, 4, 6, 1, 1, 3]
def baseStart_2018992 : Nat := 118140960795 + 2018992 * 2 ^ 59
def prefixEnd_2018992 : Nat := 4983230072969 + 3 ^ 40 * 2018992 * 2
def baseEnd_2018992 : Nat := 1036713333582469918214831

theorem tailTrace_2018992 : CollatzResearch.WordTrace tailWord_2018992 prefixEnd_2018992 1036713333582469918214831 := by
  unfold tailWord_2018992
  simp only [CollatzResearch.WordTrace]
  refine ⟨36819343950772137613237615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49092458601029516817650153 36819343950772137613237615)
  ·
    refine ⟨55229015926158206419856423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36819343950772137613237615 55229015926158206419856423)
    ·
      refine ⟨82843523889237309629784635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55229015926158206419856423 82843523889237309629784635)
      ·
        refine ⟨124265285833855964444676953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82843523889237309629784635 124265285833855964444676953)
        ·
          refine ⟨93198964375391973333507715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124265285833855964444676953 93198964375391973333507715)
          ·
            refine ⟨139798446563087960000261573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93198964375391973333507715 139798446563087960000261573)
            ·
              refine ⟨26212208730578992500049045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139798446563087960000261573 26212208730578992500049045)
              ·
                refine ⟨1228697284245890273439799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26212208730578992500049045 1228697284245890273439799)
                ·
                  refine ⟨1843045926368835410159699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1228697284245890273439799 1843045926368835410159699)
                  ·
                    refine ⟨2764568889553253115239549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1843045926368835410159699 2764568889553253115239549)
                    ·
                      refine ⟨1036713333582469918214831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2764568889553253115239549 1036713333582469918214831)
                      ·
                        rfl

theorem cell23_2018992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6, 1, 1, 3].length) (baseStart_2018992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2018992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2018992 prefixEnd_2018992 := by exact prefixLift 2018992
  have htrace : WordTrace (prefixWord ++ tailWord_2018992) baseStart_2018992 baseEnd_2018992 := by
    simpa [prefixWord, tailWord_2018992, baseEnd_2018992] using wordTrace_append hprefix tailTrace_2018992
  have hstable : (prefixWord ++ tailWord_2018992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018992).length < 2 ^ (prefixWord ++ tailWord_2018992).sum := by decide
  have hdescent : baseEnd_2018992 < baseStart_2018992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019008 : List Nat := [2, 1, 1, 2, 4, 1, 2, 3, 1, 6]
def baseStart_2019008 : Nat := 118140960795 + 2019008 * 2 ^ 59
def prefixEnd_2019008 : Nat := 4983230072969 + 3 ^ 40 * 2019008 * 2
def baseEnd_2019008 : Nat := 345573849757647285204919

theorem tailTrace_2019008 : CollatzResearch.WordTrace tailWord_2019008 prefixEnd_2019008 345573849757647285204919 := by
  unfold tailWord_2019008
  simp only [CollatzResearch.WordTrace]
  refine ⟨36819635734743154979528839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49092847646324206639371785 36819635734743154979528839)
  ·
    refine ⟨55229453602114732469293259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36819635734743154979528839 55229453602114732469293259)
    ·
      refine ⟨82844180403172098703939889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55229453602114732469293259 82844180403172098703939889)
      ·
        refine ⟨62133135302379074027954917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82844180403172098703939889 62133135302379074027954917)
        ·
          refine ⟨11649962869196076380241547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62133135302379074027954917 11649962869196076380241547)
          ·
            refine ⟨17474944303794114570362321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11649962869196076380241547 17474944303794114570362321)
            ·
              refine ⟨13106208227845585927771741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17474944303794114570362321 13106208227845585927771741)
              ·
                refine ⟨4914828085442094722914403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13106208227845585927771741 4914828085442094722914403)
                ·
                  refine ⟨7372242128163142084371605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4914828085442094722914403 7372242128163142084371605)
                  ·
                    refine ⟨345573849757647285204919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7372242128163142084371605 345573849757647285204919)
                    ·
                      rfl

theorem cell23_2019008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 1, 6].length) (baseStart_2019008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019008 prefixEnd_2019008 := by exact prefixLift 2019008
  have htrace : WordTrace (prefixWord ++ tailWord_2019008) baseStart_2019008 baseEnd_2019008 := by
    simpa [prefixWord, tailWord_2019008, baseEnd_2019008] using wordTrace_append hprefix tailTrace_2019008
  have hstable : (prefixWord ++ tailWord_2019008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019008).length < 2 ^ (prefixWord ++ tailWord_2019008).sum := by decide
  have hdescent : baseEnd_2019008 < baseStart_2019008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019032 : List Nat := [2, 1, 2, 2, 3, 1, 5, 1, 1, 1, 4]
def baseStart_2019032 : Nat := 118140960795 + 2019032 * 2 ^ 59
def prefixEnd_2019032 : Nat := 4983230072969 + 3 ^ 40 * 2019032 * 2
def baseEnd_2019032 : Nat := 1036733872808649761714647

theorem tailTrace_2019032 : CollatzResearch.WordTrace tailWord_2019032 prefixEnd_2019032 1036733872808649761714647 := by
  unfold tailWord_2019032
  simp only [CollatzResearch.WordTrace]
  refine ⟨36820073410699681028965675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49093431214266241371954233 36820073410699681028965675)
  ·
    refine ⟨55230110116049521543448513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36820073410699681028965675 55230110116049521543448513)
    ·
      refine ⟨41422582587037141157586385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55230110116049521543448513 41422582587037141157586385)
      ·
        refine ⟨31066936940277855868189789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41422582587037141157586385 31066936940277855868189789)
        ·
          refine ⟨11650101352604195950571171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31066936940277855868189789 11650101352604195950571171)
          ·
            refine ⟨17475152028906293925856757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11650101352604195950571171 17475152028906293925856757)
            ·
              refine ⟨1638295502709965055549071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17475152028906293925856757 1638295502709965055549071)
              ·
                refine ⟨2457443254064947583323607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1638295502709965055549071 2457443254064947583323607)
                ·
                  refine ⟨3686164881097421374985411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2457443254064947583323607 3686164881097421374985411)
                  ·
                    refine ⟨5529247321646132062478117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3686164881097421374985411 5529247321646132062478117)
                    ·
                      refine ⟨1036733872808649761714647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5529247321646132062478117 1036733872808649761714647)
                      ·
                        rfl

theorem cell23_2019032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 1, 1, 4].length) (baseStart_2019032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019032 prefixEnd_2019032 := by exact prefixLift 2019032
  have htrace : WordTrace (prefixWord ++ tailWord_2019032) baseStart_2019032 baseEnd_2019032 := by
    simpa [prefixWord, tailWord_2019032, baseEnd_2019032] using wordTrace_append hprefix tailTrace_2019032
  have hstable : (prefixWord ++ tailWord_2019032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019032).length < 2 ^ (prefixWord ++ tailWord_2019032).sum := by decide
  have hdescent : baseEnd_2019032 < baseStart_2019032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019043 : List Nat := [1, 1, 1, 7, 2, 2, 2, 2, 1, 1, 3]
def baseStart_2019043 : Nat := 118140960795 + 2019043 * 2 ^ 59
def prefixEnd_2019043 : Nat := 4983230072969 + 3 ^ 40 * 2019043 * 2
def baseEnd_2019043 : Nat := 1036739521095849218677097

theorem tailTrace_2019043 : CollatzResearch.WordTrace tailWord_2019043 prefixEnd_2019043 1036739521095849218677097 := by
  unfold tailWord_2019043
  simp only [CollatzResearch.WordTrace]
  refine ⟨73640548024359510936581783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49093698682906340624387855 73640548024359510936581783)
  ·
    refine ⟨110460822036539266404872675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73640548024359510936581783 110460822036539266404872675)
    ·
      refine ⟨165691233054808899607309013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110460822036539266404872675 165691233054808899607309013)
      ·
        refine ⟨3883388274722083584546305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 165691233054808899607309013 3883388274722083584546305)
        ·
          refine ⟨2912541206041562688409729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3883388274722083584546305 2912541206041562688409729)
          ·
            refine ⟨2184405904531172016307297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2912541206041562688409729 2184405904531172016307297)
            ·
              refine ⟨1638304428398379012230473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2184405904531172016307297 1638304428398379012230473)
              ·
                refine ⟨1228728321298784259172855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1638304428398379012230473 1228728321298784259172855)
                ·
                  refine ⟨1843092481948176388759283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1228728321298784259172855 1843092481948176388759283)
                  ·
                    refine ⟨2764638722922264583138925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1843092481948176388759283 2764638722922264583138925)
                    ·
                      refine ⟨1036739521095849218677097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2764638722922264583138925 1036739521095849218677097)
                      ·
                        rfl

theorem cell23_2019043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_2019043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019043 prefixEnd_2019043 := by exact prefixLift 2019043
  have htrace : WordTrace (prefixWord ++ tailWord_2019043) baseStart_2019043 baseEnd_2019043 := by
    simpa [prefixWord, tailWord_2019043, baseEnd_2019043] using wordTrace_append hprefix tailTrace_2019043
  have hstable : (prefixWord ++ tailWord_2019043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019043).length < 2 ^ (prefixWord ++ tailWord_2019043).sum := by decide
  have hdescent : baseEnd_2019043 < baseStart_2019043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019062 : List Nat := [5, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4]
def baseStart_2019062 : Nat := 118140960795 + 2019062 * 2 ^ 59
def prefixEnd_2019062 : Nat := 4983230072969 + 3 ^ 40 * 2019062 * 2
def baseEnd_2019062 : Nat := 1036749277228284644339509

theorem tailTrace_2019062 : CollatzResearch.WordTrace tailWord_2019062 prefixEnd_2019062 1036749277228284644339509 := by
  unfold tailWord_2019062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4602577563205667323845215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49094160674193784787682293 4602577563205667323845215)
  ·
    refine ⟨6903866344808500985767823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4602577563205667323845215 6903866344808500985767823)
    ·
      refine ⟨10355799517212751478651735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6903866344808500985767823 10355799517212751478651735)
      ·
        refine ⟨15533699275819127217977603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10355799517212751478651735 15533699275819127217977603)
        ·
          refine ⟨23300548913728690826966405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15533699275819127217977603 23300548913728690826966405)
          ·
            refine ⟨4368852921324129530056201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23300548913728690826966405 4368852921324129530056201)
            ·
              refine ⟨3276639690993097147542151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4368852921324129530056201 3276639690993097147542151)
              ·
                refine ⟨4914959536489645721313227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3276639690993097147542151 4914959536489645721313227)
                ·
                  refine ⟨7372439304734468581969841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4914959536489645721313227 7372439304734468581969841)
                  ·
                    refine ⟨5529329478550851436477381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7372439304734468581969841 5529329478550851436477381)
                    ·
                      refine ⟨1036749277228284644339509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5529329478550851436477381 1036749277228284644339509)
                      ·
                        rfl

theorem cell23_2019062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_2019062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019062 prefixEnd_2019062 := by exact prefixLift 2019062
  have htrace : WordTrace (prefixWord ++ tailWord_2019062) baseStart_2019062 baseEnd_2019062 := by
    simpa [prefixWord, tailWord_2019062, baseEnd_2019062] using wordTrace_append hprefix tailTrace_2019062
  have hstable : (prefixWord ++ tailWord_2019062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019062).length < 2 ^ (prefixWord ++ tailWord_2019062).sum := by decide
  have hdescent : baseEnd_2019062 < baseStart_2019062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019065 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 8, 1, 3]
def baseStart_2019065 : Nat := 118140960795 + 2019065 * 2 ^ 59
def prefixEnd_2019065 : Nat := 4983230072969 + 3 ^ 40 * 2019065 * 2
def baseEnd_2019065 : Nat := 1036750817670248132601995

theorem tailTrace_2019065 : CollatzResearch.WordTrace tailWord_2019065 prefixEnd_2019065 1036750817670248132601995 := by
  unfold tailWord_2019065
  simp only [CollatzResearch.WordTrace]
  refine ⟨73641350430279808693882649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49094233620186539129255099 73641350430279808693882649)
  ·
    refine ⟨55231012822709856520411987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73641350430279808693882649 55231012822709856520411987)
    ·
      refine ⟨82846519234064784780617981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55231012822709856520411987 82846519234064784780617981)
      ·
        refine ⟨31067444712774294292731743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82846519234064784780617981 31067444712774294292731743)
        ·
          refine ⟨46601167069161441439097615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31067444712774294292731743 46601167069161441439097615)
          ·
            refine ⟨69901750603742162158646423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46601167069161441439097615 69901750603742162158646423)
            ·
              refine ⟨104852625905613243237969635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69901750603742162158646423 104852625905613243237969635)
              ·
                refine ⟨157278938858419864856954453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104852625905613243237969635 157278938858419864856954453)
                ·
                  refine ⟨1843112564747107791292435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 157278938858419864856954453 1843112564747107791292435)
                  ·
                    refine ⟨2764668847120661686938653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1843112564747107791292435 2764668847120661686938653)
                    ·
                      refine ⟨1036750817670248132601995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2764668847120661686938653 1036750817670248132601995)
                      ·
                        rfl

theorem cell23_2019065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_2019065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019065 prefixEnd_2019065 := by exact prefixLift 2019065
  have htrace : WordTrace (prefixWord ++ tailWord_2019065) baseStart_2019065 baseEnd_2019065 := by
    simpa [prefixWord, tailWord_2019065, baseEnd_2019065] using wordTrace_append hprefix tailTrace_2019065
  have hstable : (prefixWord ++ tailWord_2019065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019065).length < 2 ^ (prefixWord ++ tailWord_2019065).sum := by decide
  have hdescent : baseEnd_2019065 < baseStart_2019065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019068 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 2, 7]
def baseStart_2019068 : Nat := 118140960795 + 2019068 * 2 ^ 59
def prefixEnd_2019068 : Nat := 4983230072969 + 3 ^ 40 * 2019068 * 2
def baseEnd_2019068 : Nat := 345584119370737206954827

theorem tailTrace_2019068 : CollatzResearch.WordTrace tailWord_2019068 prefixEnd_2019068 345584119370737206954827 := by
  unfold tailWord_2019068
  simp only [CollatzResearch.WordTrace]
  refine ⟨36820729924634470103120929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49094306566179293470827905 36820729924634470103120929)
  ·
    refine ⟨27615547443475852577340697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36820729924634470103120929 27615547443475852577340697)
    ·
      refine ⟨20711660582606889433005523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27615547443475852577340697 20711660582606889433005523)
      ·
        refine ⟨31067490873910334149508285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20711660582606889433005523 31067490873910334149508285)
        ·
          refine ⟨11650309077716375306065607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31067490873910334149508285 11650309077716375306065607)
          ·
            refine ⟨17475463616574562959098411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11650309077716375306065607 17475463616574562959098411)
            ·
              refine ⟨26213195424861844438647617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17475463616574562959098411 26213195424861844438647617)
              ·
                refine ⟨19659896568646383328985713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26213195424861844438647617 19659896568646383328985713)
                ·
                  refine ⟨14744922426484787496739285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19659896568646383328985713 14744922426484787496739285)
                  ·
                    refine ⟨345584119370737206954827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14744922426484787496739285 345584119370737206954827)
                    ·
                      rfl

theorem cell23_2019068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_2019068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019068 prefixEnd_2019068 := by exact prefixLift 2019068
  have htrace : WordTrace (prefixWord ++ tailWord_2019068) baseStart_2019068 baseEnd_2019068 := by
    simpa [prefixWord, tailWord_2019068, baseEnd_2019068] using wordTrace_append hprefix tailTrace_2019068
  have hstable : (prefixWord ++ tailWord_2019068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019068).length < 2 ^ (prefixWord ++ tailWord_2019068).sum := by decide
  have hdescent : baseEnd_2019068 < baseStart_2019068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019126 : List Nat := [5, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2]
def baseStart_2019126 : Nat := 118140960795 + 2019126 * 2 ^ 59
def prefixEnd_2019126 : Nat := 4983230072969 + 3 ^ 40 * 2019126 * 2
def baseEnd_2019126 : Nat := 1036782139990172393939215

theorem tailTrace_2019126 : CollatzResearch.WordTrace tailWord_2019126 prefixEnd_2019126 1036782139990172393939215 := by
  unfold tailWord_2019126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4602723455191176006990827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49095716855372544074568821 4602723455191176006990827)
  ·
    refine ⟨6904085182786764010486241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4602723455191176006990827 6904085182786764010486241)
    ·
      refine ⟨5178063887090073007864681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6904085182786764010486241 5178063887090073007864681)
      ·
        refine ⟨3883547915317554755898511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5178063887090073007864681 3883547915317554755898511)
        ·
          refine ⟨5825321872976332133847767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3883547915317554755898511 5825321872976332133847767)
          ·
            refine ⟨8737982809464498200771651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5825321872976332133847767 8737982809464498200771651)
            ·
              refine ⟨13106974214196747301157477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8737982809464498200771651 13106974214196747301157477)
              ·
                refine ⟨2457557665161890118967027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13106974214196747301157477 2457557665161890118967027)
                ·
                  refine ⟨3686336497742835178450541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2457557665161890118967027 3686336497742835178450541)
                  ·
                    refine ⟨1382376186653563191918953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3686336497742835178450541 1382376186653563191918953)
                    ·
                      refine ⟨1036782139990172393939215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1382376186653563191918953 1036782139990172393939215)
                      ·
                        rfl

theorem cell23_2019126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_2019126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019126 prefixEnd_2019126 := by exact prefixLift 2019126
  have htrace : WordTrace (prefixWord ++ tailWord_2019126) baseStart_2019126 baseEnd_2019126 := by
    simpa [prefixWord, tailWord_2019126, baseEnd_2019126] using wordTrace_append hprefix tailTrace_2019126
  have hstable : (prefixWord ++ tailWord_2019126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019126).length < 2 ^ (prefixWord ++ tailWord_2019126).sum := by decide
  have hdescent : baseEnd_2019126 < baseStart_2019126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019175 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 4, 5]
def baseStart_2019175 : Nat := 118140960795 + 2019175 * 2 ^ 59
def prefixEnd_2019175 : Nat := 4983230072969 + 3 ^ 40 * 2019175 * 2
def baseEnd_2019175 : Nat := 345602433514080900742163

theorem tailTrace_2019175 : CollatzResearch.WordTrace tailWord_2019175 prefixEnd_2019175 345602433514080900742163 := by
  unfold tailWord_2019175
  simp only [CollatzResearch.WordTrace]
  refine ⟨73645362459881297480386979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49096908306587531653591319 73645362459881297480386979)
  ·
    refine ⟨110468043689821946220580469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73645362459881297480386979 110468043689821946220580469)
    ·
      refine ⟨10356379095920807458179419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110468043689821946220580469 10356379095920807458179419)
      ·
        refine ⟨15534568643881211187269129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10356379095920807458179419 15534568643881211187269129)
        ·
          refine ⟨11650926482910908390451847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15534568643881211187269129 11650926482910908390451847)
          ·
            refine ⟨17476389724366362585677771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11650926482910908390451847 17476389724366362585677771)
            ·
              refine ⟨26214584586549543878516657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17476389724366362585677771 26214584586549543878516657)
              ·
                refine ⟨19660938439912157908887493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26214584586549543878516657 19660938439912157908887493)
                ·
                  refine ⟨3686425957483529607916405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19660938439912157908887493 3686425957483529607916405)
                  ·
                    refine ⟨345602433514080900742163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3686425957483529607916405 345602433514080900742163)
                    ·
                      rfl

theorem cell23_2019175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_2019175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019175 prefixEnd_2019175 := by exact prefixLift 2019175
  have htrace : WordTrace (prefixWord ++ tailWord_2019175) baseStart_2019175 baseEnd_2019175 := by
    simpa [prefixWord, tailWord_2019175, baseEnd_2019175] using wordTrace_append hprefix tailTrace_2019175
  have hstable : (prefixWord ++ tailWord_2019175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019175).length < 2 ^ (prefixWord ++ tailWord_2019175).sum := by decide
  have hdescent : baseEnd_2019175 < baseStart_2019175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019212 : List Nat := [2, 2, 1, 2, 1, 2, 1, 4, 2, 4, 2]
def baseStart_2019212 : Nat := 118140960795 + 2019212 * 2 ^ 59
def prefixEnd_2019212 : Nat := 4983230072969 + 3 ^ 40 * 2019212 * 2
def baseEnd_2019212 : Nat := 1036826299326459057463819

theorem tailTrace_2019212 : CollatzResearch.WordTrace tailWord_2019212 prefixEnd_2019212 1036826299326459057463819 := by
  unfold tailWord_2019212
  simp only [CollatzResearch.WordTrace]
  refine ⟨36823355980373626399741945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49097807973831501866322593 36823355980373626399741945)
  ·
    refine ⟨27617516985280219799806459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36823355980373626399741945 27617516985280219799806459)
    ·
      refine ⟨41426275477920329699709689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27617516985280219799806459 41426275477920329699709689)
      ·
        refine ⟨31069706608440247274782267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41426275477920329699709689 31069706608440247274782267)
        ·
          refine ⟨46604559912660370912173401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31069706608440247274782267 46604559912660370912173401)
          ·
            refine ⟨34953419934495278184130051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46604559912660370912173401 34953419934495278184130051)
            ·
              refine ⟨52430129901742917276195077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34953419934495278184130051 52430129901742917276195077)
              ·
                refine ⟨9830649356576796989286577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52430129901742917276195077 9830649356576796989286577)
                ·
                  refine ⟨7372987017432597741964933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9830649356576796989286577 7372987017432597741964933)
                  ·
                    refine ⟨1382435065768612076618425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7372987017432597741964933 1382435065768612076618425)
                    ·
                      refine ⟨1036826299326459057463819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1382435065768612076618425 1036826299326459057463819)
                      ·
                        rfl

theorem cell23_2019212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 2, 4, 2].length) (baseStart_2019212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019212 prefixEnd_2019212 := by exact prefixLift 2019212
  have htrace : WordTrace (prefixWord ++ tailWord_2019212) baseStart_2019212 baseEnd_2019212 := by
    simpa [prefixWord, tailWord_2019212, baseEnd_2019212] using wordTrace_append hprefix tailTrace_2019212
  have hstable : (prefixWord ++ tailWord_2019212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019212).length < 2 ^ (prefixWord ++ tailWord_2019212).sum := by decide
  have hdescent : baseEnd_2019212 < baseStart_2019212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019229 : List Nat := [1, 4, 2, 1, 2, 3, 1, 1, 2, 4, 2]
def baseStart_2019229 : Nat := 118140960795 + 2019229 * 2 ^ 59
def prefixEnd_2019229 : Nat := 4983230072969 + 3 ^ 40 * 2019229 * 2
def baseEnd_2019229 : Nat := 1036835028497585490951241

theorem tailTrace_2019229 : CollatzResearch.WordTrace tailWord_2019229 prefixEnd_2019229 1036835028497585490951241 := by
  unfold tailWord_2019229
  simp only [CollatzResearch.WordTrace]
  refine ⟨73647332001685664702852741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49098221334457109801901827 73647332001685664702852741)
  ·
    refine ⟨13808874750316062131784889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73647332001685664702852741 13808874750316062131784889)
    ·
      refine ⟨10356656062737046598838667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13808874750316062131784889 10356656062737046598838667)
      ·
        refine ⟨15534984094105569898258001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10356656062737046598838667 15534984094105569898258001)
        ·
          refine ⟨11651238070579177423693501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15534984094105569898258001 11651238070579177423693501)
          ·
            refine ⟨4369214276467191533885063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11651238070579177423693501 4369214276467191533885063)
            ·
              refine ⟨6553821414700787300827595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4369214276467191533885063 6553821414700787300827595)
              ·
                refine ⟨9830732122051180951241393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6553821414700787300827595 9830732122051180951241393)
                ·
                  refine ⟨7373049091538385713431045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9830732122051180951241393 7373049091538385713431045)
                  ·
                    refine ⟨1382446704663447321268321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7373049091538385713431045 1382446704663447321268321)
                    ·
                      refine ⟨1036835028497585490951241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1382446704663447321268321 1036835028497585490951241)
                      ·
                        rfl

theorem cell23_2019229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_2019229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019229 prefixEnd_2019229 := by exact prefixLift 2019229
  have htrace : WordTrace (prefixWord ++ tailWord_2019229) baseStart_2019229 baseEnd_2019229 := by
    simpa [prefixWord, tailWord_2019229, baseEnd_2019229] using wordTrace_append hprefix tailTrace_2019229
  have hstable : (prefixWord ++ tailWord_2019229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019229).length < 2 ^ (prefixWord ++ tailWord_2019229).sum := by decide
  have hdescent : baseEnd_2019229 < baseStart_2019229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019239 : List Nat := [1, 1, 6, 1, 2, 2, 1, 2, 3, 4]
def baseStart_2019239 : Nat := 118140960795 + 2019239 * 2 ^ 59
def prefixEnd_2019239 : Nat := 4983230072969 + 3 ^ 40 * 2019239 * 2
def baseEnd_2019239 : Nat := 345613387768043483942065

theorem tailTrace_2019239 : CollatzResearch.WordTrace tailWord_2019239 prefixEnd_2019239 345613387768043483942065 := by
  unfold tailWord_2019239
  simp only [CollatzResearch.WordTrace]
  refine ⟨73647696731649436410716771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49098464487766290940477847 73647696731649436410716771)
  ·
    refine ⟨110471545097474154616075157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73647696731649436410716771 110471545097474154616075157)
    ·
      refine ⟨5178353676444100997628523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 110471545097474154616075157 5178353676444100997628523)
      ·
        refine ⟨7767530514666151496442785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5178353676444100997628523 7767530514666151496442785)
        ·
          refine ⟨5825647885999613622332089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7767530514666151496442785 5825647885999613622332089)
          ·
            refine ⟨4369235914499710216749067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5825647885999613622332089 4369235914499710216749067)
            ·
              refine ⟨6553853871749565325123601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4369235914499710216749067 6553853871749565325123601)
              ·
                refine ⟨4915390403812173993842701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6553853871749565325123601 4915390403812173993842701)
                ·
                  refine ⟨1843271401429565247691013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4915390403812173993842701 1843271401429565247691013)
                  ·
                    refine ⟨345613387768043483942065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1843271401429565247691013 345613387768043483942065)
                    ·
                      rfl

theorem cell23_2019239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_2019239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019239 prefixEnd_2019239 := by exact prefixLift 2019239
  have htrace : WordTrace (prefixWord ++ tailWord_2019239) baseStart_2019239 baseEnd_2019239 := by
    simpa [prefixWord, tailWord_2019239, baseEnd_2019239] using wordTrace_append hprefix tailTrace_2019239
  have hstable : (prefixWord ++ tailWord_2019239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019239).length < 2 ^ (prefixWord ++ tailWord_2019239).sum := by decide
  have hdescent : baseEnd_2019239 < baseStart_2019239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019249 : List Nat := [1, 2, 2, 4, 2, 1, 3, 1, 2, 2, 3]
def baseStart_2019249 : Nat := 118140960795 + 2019249 * 2 ^ 59
def prefixEnd_2019249 : Nat := 4983230072969 + 3 ^ 40 * 2019249 * 2
def baseEnd_2019249 : Nat := 1036845298110675412701149

theorem tailTrace_2019249 : CollatzResearch.WordTrace tailWord_2019249 prefixEnd_2019249 1036845298110675412701149 := by
  unfold tailWord_2019249
  simp only [CollatzResearch.WordTrace]
  refine ⟨73648061461613208118580801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49098707641075472079053867 73648061461613208118580801)
  ·
    refine ⟨55236046096209906088935601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73648061461613208118580801 55236046096209906088935601)
    ·
      refine ⟨41427034572157429566701701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55236046096209906088935601 41427034572157429566701701)
      ·
        refine ⟨7767568982279518043756569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41427034572157429566701701 7767568982279518043756569)
        ·
          refine ⟨5825676736709638532817427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7767568982279518043756569 5825676736709638532817427)
          ·
            refine ⟨8738515105064457799226141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5825676736709638532817427 8738515105064457799226141)
            ·
              refine ⟨3276943164399171674709803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8738515105064457799226141 3276943164399171674709803)
              ·
                refine ⟨4915414746598757512064705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3276943164399171674709803 4915414746598757512064705)
                ·
                  refine ⟨3686561059949068134048529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4915414746598757512064705 3686561059949068134048529)
                  ·
                    refine ⟨2764920794961801100536397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3686561059949068134048529 2764920794961801100536397)
                    ·
                      refine ⟨1036845298110675412701149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2764920794961801100536397 1036845298110675412701149)
                      ·
                        rfl

theorem cell23_2019249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_2019249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019249 prefixEnd_2019249 := by exact prefixLift 2019249
  have htrace : WordTrace (prefixWord ++ tailWord_2019249) baseStart_2019249 baseEnd_2019249 := by
    simpa [prefixWord, tailWord_2019249, baseEnd_2019249] using wordTrace_append hprefix tailTrace_2019249
  have hstable : (prefixWord ++ tailWord_2019249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019249).length < 2 ^ (prefixWord ++ tailWord_2019249).sum := by decide
  have hdescent : baseEnd_2019249 < baseStart_2019249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019279 : List Nat := [1, 1, 2, 1, 1, 5, 4, 1, 3, 1, 3]
def baseStart_2019279 : Nat := 118140960795 + 2019279 * 2 ^ 59
def prefixEnd_2019279 : Nat := 4983230072969 + 3 ^ 40 * 2019279 * 2
def baseEnd_2019279 : Nat := 1036860702530310295326011

theorem tailTrace_2019279 : CollatzResearch.WordTrace tailWord_2019279 prefixEnd_2019279 1036860702530310295326011 := by
  unfold tailWord_2019279
  simp only [CollatzResearch.WordTrace]
  refine ⟨73649155651504523242172891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49099437101003015494781927 73649155651504523242172891)
  ·
    refine ⟨110473733477256784863259337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73649155651504523242172891 110473733477256784863259337)
    ·
      refine ⟨82855300107942588647444503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110473733477256784863259337 82855300107942588647444503)
      ·
        refine ⟨124282950161913882971166755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82855300107942588647444503 124282950161913882971166755)
        ·
          refine ⟨186424425242870824456750133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124282950161913882971166755 186424425242870824456750133)
          ·
            refine ⟨17477289866519139792820325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186424425242870824456750133 17477289866519139792820325)
            ·
              refine ⟨3276991849972338711153811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17477289866519139792820325 3276991849972338711153811)
              ·
                refine ⟨4915487774958508066730717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3276991849972338711153811 4915487774958508066730717)
                ·
                  refine ⟨1843307915609440525024019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4915487774958508066730717 1843307915609440525024019)
                  ·
                    refine ⟨2764961873414160787536029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1843307915609440525024019 2764961873414160787536029)
                    ·
                      refine ⟨1036860702530310295326011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2764961873414160787536029 1036860702530310295326011)
                      ·
                        rfl

theorem cell23_2019279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3, 1, 3].length) (baseStart_2019279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019279 prefixEnd_2019279 := by exact prefixLift 2019279
  have htrace : WordTrace (prefixWord ++ tailWord_2019279) baseStart_2019279 baseEnd_2019279 := by
    simpa [prefixWord, tailWord_2019279, baseEnd_2019279] using wordTrace_append hprefix tailTrace_2019279
  have hstable : (prefixWord ++ tailWord_2019279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019279).length < 2 ^ (prefixWord ++ tailWord_2019279).sum := by decide
  have hdescent : baseEnd_2019279 < baseStart_2019279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019299 : List Nat := [1, 1, 1, 6, 1, 3, 2, 2, 1, 5]
def baseStart_2019299 : Nat := 118140960795 + 2019299 * 2 ^ 59
def prefixEnd_2019299 : Nat := 4983230072969 + 3 ^ 40 * 2019299 * 2
def baseEnd_2019299 : Nat := 345623657381133405691973

theorem tailTrace_2019299 : CollatzResearch.WordTrace tailWord_2019299 prefixEnd_2019299 345623657381133405691973 := by
  unfold tailWord_2019299
  simp only [CollatzResearch.WordTrace]
  refine ⟨73649885111432066657900951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49099923407621377771933967 73649885111432066657900951)
  ·
    refine ⟨110474827667148099986851427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73649885111432066657900951 110474827667148099986851427)
    ·
      refine ⟨165712241500722149980277141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110474827667148099986851427 165712241500722149980277141)
      ·
        refine ⟨7767761320346350780325491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 165712241500722149980277141 7767761320346350780325491)
        ·
          refine ⟨11651641980519526170488237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7767761320346350780325491 11651641980519526170488237)
          ·
            refine ⟨4369365742694822313933089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11651641980519526170488237 4369365742694822313933089)
            ·
              refine ⟨3277024307021116735449817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4369365742694822313933089 3277024307021116735449817)
              ·
                refine ⟨2457768230265837551587363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3277024307021116735449817 2457768230265837551587363)
                ·
                  refine ⟨3686652345398756327381045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2457768230265837551587363 3686652345398756327381045)
                  ·
                    refine ⟨345623657381133405691973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3686652345398756327381045 345623657381133405691973)
                    ·
                      rfl

theorem cell23_2019299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 5].length) (baseStart_2019299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019299 prefixEnd_2019299 := by exact prefixLift 2019299
  have htrace : WordTrace (prefixWord ++ tailWord_2019299) baseStart_2019299 baseEnd_2019299 := by
    simpa [prefixWord, tailWord_2019299, baseEnd_2019299] using wordTrace_append hprefix tailTrace_2019299
  have hstable : (prefixWord ++ tailWord_2019299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019299).length < 2 ^ (prefixWord ++ tailWord_2019299).sum := by decide
  have hdescent : baseEnd_2019299 < baseStart_2019299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019312 : List Nat := [2, 1, 1, 1, 3, 2, 3, 2, 4, 4]
def baseStart_2019312 : Nat := 118140960795 + 2019312 * 2 ^ 59
def prefixEnd_2019312 : Nat := 4983230072969 + 3 ^ 40 * 2019312 * 2
def baseEnd_2019312 : Nat := 345625882463969555404453

theorem tailTrace_2019312 : CollatzResearch.WordTrace tailWord_2019312 prefixEnd_2019312 345625882463969555404453 := by
  unfold tailWord_2019312
  simp only [CollatzResearch.WordTrace]
  refine ⟨36825179630192484939062095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49100239506923313252082793 36825179630192484939062095)
  ·
    refine ⟨55237769445288727408593143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36825179630192484939062095 55237769445288727408593143)
    ·
      refine ⟨82856654167933091112889715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55237769445288727408593143 82856654167933091112889715)
      ·
        refine ⟨124284981251899636669334573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82856654167933091112889715 124284981251899636669334573)
        ·
          refine ⟨46606867969462363751000465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124284981251899636669334573 46606867969462363751000465)
          ·
            refine ⟨34955150977096772813250349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46606867969462363751000465 34955150977096772813250349)
            ·
              refine ⟨13108181616411289804968881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34955150977096772813250349 13108181616411289804968881)
              ·
                refine ⟨9831136212308467353726661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13108181616411289804968881 9831136212308467353726661)
                ·
                  refine ⟨1843338039807837628823749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9831136212308467353726661 1843338039807837628823749)
                  ·
                    refine ⟨345625882463969555404453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1843338039807837628823749 345625882463969555404453)
                    ·
                      rfl

theorem cell23_2019312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 4, 4].length) (baseStart_2019312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019312 prefixEnd_2019312 := by exact prefixLift 2019312
  have htrace : WordTrace (prefixWord ++ tailWord_2019312) baseStart_2019312 baseEnd_2019312 := by
    simpa [prefixWord, tailWord_2019312, baseEnd_2019312] using wordTrace_append hprefix tailTrace_2019312
  have hstable : (prefixWord ++ tailWord_2019312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019312).length < 2 ^ (prefixWord ++ tailWord_2019312).sum := by decide
  have hdescent : baseEnd_2019312 < baseStart_2019312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019322 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3]
def baseStart_2019322 : Nat := 118140960795 + 2019322 * 2 ^ 59
def prefixEnd_2019322 : Nat := 4983230072969 + 3 ^ 40 * 2019322 * 2
def baseEnd_2019322 : Nat := 1036882782198453627088313

theorem tailTrace_2019322 : CollatzResearch.WordTrace tailWord_2019322 prefixEnd_2019322 1036882782198453627088313 := by
  unfold tailWord_2019322
  simp only [CollatzResearch.WordTrace]
  refine ⟨18412680997587185396497055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49100482660232494390658813 18412680997587185396497055)
  ·
    refine ⟨27619021496380778094745583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18412680997587185396497055 27619021496380778094745583)
    ·
      refine ⟨41428532244571167142118375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27619021496380778094745583 41428532244571167142118375)
      ·
        refine ⟨62142798366856750713177563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41428532244571167142118375 62142798366856750713177563)
        ·
          refine ⟨93214197550285126069766345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62142798366856750713177563 93214197550285126069766345)
          ·
            refine ⟨69910648162713844552324759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93214197550285126069766345 69910648162713844552324759)
            ·
              refine ⟨104865972244070766828487139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69910648162713844552324759 104865972244070766828487139)
              ·
                refine ⟨157298958366106150242730709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104865972244070766828487139 157298958366106150242730709)
                ·
                  refine ⟨3686694336705612896314001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 157298958366106150242730709 3686694336705612896314001)
                  ·
                    refine ⟨2765020752529209672235501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3686694336705612896314001 2765020752529209672235501)
                    ·
                      refine ⟨1036882782198453627088313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2765020752529209672235501 1036882782198453627088313)
                      ·
                        rfl

theorem cell23_2019322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3].length) (baseStart_2019322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019322 prefixEnd_2019322 := by exact prefixLift 2019322
  have htrace : WordTrace (prefixWord ++ tailWord_2019322) baseStart_2019322 baseEnd_2019322 := by
    simpa [prefixWord, tailWord_2019322, baseEnd_2019322] using wordTrace_append hprefix tailTrace_2019322
  have hstable : (prefixWord ++ tailWord_2019322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019322).length < 2 ^ (prefixWord ++ tailWord_2019322).sum := by decide
  have hdescent : baseEnd_2019322 < baseStart_2019322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019325 : List Nat := [1, 4, 1, 1, 1, 2, 13]
def baseStart_2019325 : Nat := 118140960795 + 2019325 * 2 ^ 59
def prefixEnd_2019325 : Nat := 4983230072969 + 3 ^ 40 * 2019325 * 2
def baseEnd_2019325 : Nat := 12801041020252063152479

theorem tailTrace_2019325 : CollatzResearch.WordTrace tailWord_2019325 prefixEnd_2019325 12801041020252063152479 := by
  unfold tailWord_2019325
  simp only [CollatzResearch.WordTrace]
  refine ⟨73650833409337873098347429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49100555606225248732231619 73650833409337873098347429)
  ·
    refine ⟨13809531264250851205940143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73650833409337873098347429 13809531264250851205940143)
    ·
      refine ⟨20714296896376276808910215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13809531264250851205940143 20714296896376276808910215)
      ·
        refine ⟨31071445344564415213365323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20714296896376276808910215 31071445344564415213365323)
        ·
          refine ⟨46607168016846622820047985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31071445344564415213365323 46607168016846622820047985)
          ·
            refine ⟨34955376012634967115035989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46607168016846622820047985 34955376012634967115035989)
            ·
              refine ⟨12801041020252063152479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 34955376012634967115035989 12801041020252063152479)
              ·
                rfl

theorem cell23_2019325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 13].length) (baseStart_2019325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019325 prefixEnd_2019325 := by exact prefixLift 2019325
  have htrace : WordTrace (prefixWord ++ tailWord_2019325) baseStart_2019325 baseEnd_2019325 := by
    simpa [prefixWord, tailWord_2019325, baseEnd_2019325] using wordTrace_append hprefix tailTrace_2019325
  have hstable : (prefixWord ++ tailWord_2019325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019325).length < 2 ^ (prefixWord ++ tailWord_2019325).sum := by decide
  have hdescent : baseEnd_2019325 < baseStart_2019325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019329 : List Nat := [1, 2, 4, 1, 2, 1, 2, 4, 2, 4]
def baseStart_2019329 : Nat := 118140960795 + 2019329 * 2 ^ 59
def prefixEnd_2019329 : Nat := 4983230072969 + 3 ^ 40 * 2019329 * 2
def baseEnd_2019329 : Nat := 345628792187678366566927

theorem tailTrace_2019329 : CollatzResearch.WordTrace tailWord_2019329 prefixEnd_2019329 345628792187678366566927 := by
  unfold tailWord_2019329
  simp only [CollatzResearch.WordTrace]
  refine ⟨73650979301323381781493041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49100652867548921187662027 73650979301323381781493041)
  ·
    refine ⟨55238234475992536336119781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73650979301323381781493041 55238234475992536336119781)
    ·
      refine ⟨10357168964248600563022459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55238234475992536336119781 10357168964248600563022459)
      ·
        refine ⟨15535753446372900844533689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10357168964248600563022459 15535753446372900844533689)
        ·
          refine ⟨11651815084779675633400267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15535753446372900844533689 11651815084779675633400267)
          ·
            refine ⟨17477722627169513450100401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11651815084779675633400267 17477722627169513450100401)
            ·
              refine ⟨13108291970377135087575301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17477722627169513450100401 13108291970377135087575301)
              ·
                refine ⟨2457804744445712828920369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13108291970377135087575301 2457804744445712828920369)
                ·
                  refine ⟨1843353558334284621690277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2457804744445712828920369 1843353558334284621690277)
                  ·
                    refine ⟨345628792187678366566927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1843353558334284621690277 345628792187678366566927)
                    ·
                      rfl

theorem cell23_2019329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_2019329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019329 prefixEnd_2019329 := by exact prefixLift 2019329
  have htrace : WordTrace (prefixWord ++ tailWord_2019329) baseStart_2019329 baseEnd_2019329 := by
    simpa [prefixWord, tailWord_2019329, baseEnd_2019329] using wordTrace_append hprefix tailTrace_2019329
  have hstable : (prefixWord ++ tailWord_2019329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019329).length < 2 ^ (prefixWord ++ tailWord_2019329).sum := by decide
  have hdescent : baseEnd_2019329 < baseStart_2019329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019342 : List Nat := [4, 1, 1, 2, 2, 1, 4, 8]
def baseStart_2019342 : Nat := 118140960795 + 2019342 * 2 ^ 59
def prefixEnd_2019342 : Nat := 4983230072969 + 3 ^ 40 * 2019342 * 2
def baseEnd_2019342 : Nat := 38403446363390501808823

theorem tailTrace_2019342 : CollatzResearch.WordTrace tailWord_2019342 prefixEnd_2019342 38403446363390501808823 := by
  unfold tailWord_2019342
  simp only [CollatzResearch.WordTrace]
  refine ⟨9206431681284535625214535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49100968966850856667810853 9206431681284535625214535)
  ·
    refine ⟨13809647521926803437821803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9206431681284535625214535 13809647521926803437821803)
    ·
      refine ⟨20714471282890205156732705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13809647521926803437821803 20714471282890205156732705)
      ·
        refine ⟨15535853462167653867549529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20714471282890205156732705 15535853462167653867549529)
        ·
          refine ⟨11651890096625740400662147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15535853462167653867549529 11651890096625740400662147)
          ·
            refine ⟨17477835144938610600993221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11651890096625740400662147 17477835144938610600993221)
            ·
              refine ⟨3277094089675989487686229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17477835144938610600993221 3277094089675989487686229)
              ·
                refine ⟨38403446363390501808823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3277094089675989487686229 38403446363390501808823)
                ·
                  rfl

theorem cell23_2019342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 8].length) (baseStart_2019342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019342 prefixEnd_2019342 := by exact prefixLift 2019342
  have htrace : WordTrace (prefixWord ++ tailWord_2019342) baseStart_2019342 baseEnd_2019342 := by
    simpa [prefixWord, tailWord_2019342, baseEnd_2019342] using wordTrace_append hprefix tailTrace_2019342
  have hstable : (prefixWord ++ tailWord_2019342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019342).length < 2 ^ (prefixWord ++ tailWord_2019342).sum := by decide
  have hdescent : baseEnd_2019342 < baseStart_2019342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019355 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 4, 7]
def baseStart_2019355 : Nat := 118140960795 + 2019355 * 2 ^ 59
def prefixEnd_2019355 : Nat := 4983230072969 + 3 ^ 40 * 2019355 * 2
def baseEnd_2019355 : Nat := 345633242353350665991887

theorem tailTrace_2019355 : CollatzResearch.WordTrace tailWord_2019355 prefixEnd_2019355 345633242353350665991887 := by
  unfold tailWord_2019355
  simp only [CollatzResearch.WordTrace]
  refine ⟨73651927599229188221939519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49101285066152792147959679 73651927599229188221939519)
  ·
    refine ⟨110477891398843782332909279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73651927599229188221939519 110477891398843782332909279)
    ·
      refine ⟨165716837098265673499363919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110477891398843782332909279 165716837098265673499363919)
      ·
        refine ⟨248575255647398510249045879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165716837098265673499363919 248575255647398510249045879)
        ·
          refine ⟨372862883471097765373568819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248575255647398510249045879 372862883471097765373568819)
          ·
            refine ⟨559294325206646648060353229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372862883471097765373568819 559294325206646648060353229)
            ·
              refine ⟨209735371952492493022632461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 559294325206646648060353229 209735371952492493022632461)
              ·
                refine ⟨78650764482184684883487173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209735371952492493022632461 78650764482184684883487173)
                ·
                  refine ⟨14747018340409628415653845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78650764482184684883487173 14747018340409628415653845)
                  ·
                    refine ⟨345633242353350665991887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14747018340409628415653845 345633242353350665991887)
                    ·
                      rfl

theorem cell23_2019355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 7].length) (baseStart_2019355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019355 prefixEnd_2019355 := by exact prefixLift 2019355
  have htrace : WordTrace (prefixWord ++ tailWord_2019355) baseStart_2019355 baseEnd_2019355 := by
    simpa [prefixWord, tailWord_2019355, baseEnd_2019355] using wordTrace_append hprefix tailTrace_2019355
  have hstable : (prefixWord ++ tailWord_2019355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019355).length < 2 ^ (prefixWord ++ tailWord_2019355).sum := by decide
  have hdescent : baseEnd_2019355 < baseStart_2019355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019356 : List Nat := [2, 2, 3, 1, 3, 1, 3, 2, 1, 2, 3]
def baseStart_2019356 : Nat := 118140960795 + 2019356 * 2 ^ 59
def prefixEnd_2019356 : Nat := 4983230072969 + 3 ^ 40 * 2019356 * 2
def baseEnd_2019356 : Nat := 1036900240540706494063157

theorem tailTrace_2019356 : CollatzResearch.WordTrace tailWord_2019356 prefixEnd_2019356 1036900240540706494063157 := by
  unfold tailWord_2019356
  simp only [CollatzResearch.WordTrace]
  refine ⟨36825982036112782696362961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49101309381483710261817281 36825982036112782696362961)
  ·
    refine ⟨27619486527084587022272221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36825982036112782696362961 27619486527084587022272221)
    ·
      refine ⟨10357307447656720133352083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27619486527084587022272221 10357307447656720133352083)
      ·
        refine ⟨15535961171485080200028125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10357307447656720133352083 15535961171485080200028125)
        ·
          refine ⟨5825985439306905075010547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15535961171485080200028125 5825985439306905075010547)
          ·
            refine ⟨8738978158960357612515821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5825985439306905075010547 8738978158960357612515821)
            ·
              refine ⟨3277116809610134104693433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8738978158960357612515821 3277116809610134104693433)
              ·
                refine ⟨2457837607207600578520075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3277116809610134104693433 2457837607207600578520075)
                ·
                  refine ⟨3686756410811400867780113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2457837607207600578520075 3686756410811400867780113)
                  ·
                    refine ⟨2765067308108550650835085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3686756410811400867780113 2765067308108550650835085)
                    ·
                      refine ⟨1036900240540706494063157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2765067308108550650835085 1036900240540706494063157)
                      ·
                        rfl

theorem cell23_2019356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_2019356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019356 prefixEnd_2019356 := by exact prefixLift 2019356
  have htrace : WordTrace (prefixWord ++ tailWord_2019356) baseStart_2019356 baseEnd_2019356 := by
    simpa [prefixWord, tailWord_2019356, baseEnd_2019356] using wordTrace_append hprefix tailTrace_2019356
  have hstable : (prefixWord ++ tailWord_2019356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019356).length < 2 ^ (prefixWord ++ tailWord_2019356).sum := by decide
  have hdescent : baseEnd_2019356 < baseStart_2019356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019392 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 4]
def baseStart_2019392 : Nat := 118140960795 + 2019392 * 2 ^ 59
def prefixEnd_2019392 : Nat := 4983230072969 + 3 ^ 40 * 2019392 * 2
def baseEnd_2019392 : Nat := 1036918725844268353212991

theorem tailTrace_2019392 : CollatzResearch.WordTrace tailWord_2019392 prefixEnd_2019392 1036918725844268353212991 := by
  unfold tailWord_2019392
  simp only [CollatzResearch.WordTrace]
  refine ⟨36826638550047571770518215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49102184733396762360690953 36826638550047571770518215)
  ·
    refine ⟨55239957825071357655777323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36826638550047571770518215 55239957825071357655777323)
    ·
      refine ⟨82859936737607036483665985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55239957825071357655777323 82859936737607036483665985)
      ·
        refine ⟨62144952553205277362749489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82859936737607036483665985 62144952553205277362749489)
        ·
          refine ⟨46608714414903958022062117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62144952553205277362749489 46608714414903958022062117)
          ·
            refine ⟨8739133952794492129136647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46608714414903958022062117 8739133952794492129136647)
            ·
              refine ⟨13108700929191738193704971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8739133952794492129136647 13108700929191738193704971)
              ·
                refine ⟨19663051393787607290557457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13108700929191738193704971 19663051393787607290557457)
                ·
                  refine ⟨14747288545340705467918093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19663051393787607290557457 14747288545340705467918093)
                  ·
                    refine ⟨5530233204502764550469285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14747288545340705467918093 5530233204502764550469285)
                    ·
                      refine ⟨1036918725844268353212991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5530233204502764550469285 1036918725844268353212991)
                      ·
                        rfl

theorem cell23_2019392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_2019392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019392 prefixEnd_2019392 := by exact prefixLift 2019392
  have htrace : WordTrace (prefixWord ++ tailWord_2019392) baseStart_2019392 baseEnd_2019392 := by
    simpa [prefixWord, tailWord_2019392, baseEnd_2019392] using wordTrace_append hprefix tailTrace_2019392
  have hstable : (prefixWord ++ tailWord_2019392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019392).length < 2 ^ (prefixWord ++ tailWord_2019392).sum := by decide
  have hdescent : baseEnd_2019392 < baseStart_2019392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019449 : List Nat := [1, 2, 1, 3, 4, 2, 2, 1, 7]
def baseStart_2019449 : Nat := 118140960795 + 2019449 * 2 ^ 59
def prefixEnd_2019449 : Nat := 4983230072969 + 3 ^ 40 * 2019449 * 2
def baseEnd_2019449 : Nat := 115216443804619403355581

theorem tailTrace_2019449 : CollatzResearch.WordTrace tailWord_2019449 prefixEnd_2019449 115216443804619403355581 := by
  unfold tailWord_2019449
  simp only [CollatzResearch.WordTrace]
  refine ⟨73655356060888642275861401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49103570707259094850574267 73655356060888642275861401)
  ·
    refine ⟨55241517045666481706896051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73655356060888642275861401 55241517045666481706896051)
    ·
      refine ⟨82862275568499722560344077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55241517045666481706896051 82862275568499722560344077)
      ·
        refine ⟨31073353338187395960129029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82862275568499722560344077 31073353338187395960129029)
        ·
          refine ⟨5826253750910136742524193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31073353338187395960129029 5826253750910136742524193)
          ·
            refine ⟨4369690313182602556893145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5826253750910136742524193 4369690313182602556893145)
            ·
              refine ⟨3277267734886951917669859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4369690313182602556893145 3277267734886951917669859)
              ·
                refine ⟨4915901602330427876504789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3277267734886951917669859 4915901602330427876504789)
                ·
                  refine ⟨115216443804619403355581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4915901602330427876504789 115216443804619403355581)
                  ·
                    rfl

theorem cell23_2019449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 7].length) (baseStart_2019449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019449 prefixEnd_2019449 := by exact prefixLift 2019449
  have htrace : WordTrace (prefixWord ++ tailWord_2019449) baseStart_2019449 baseEnd_2019449 := by
    simpa [prefixWord, tailWord_2019449, baseEnd_2019449] using wordTrace_append hprefix tailTrace_2019449
  have hstable : (prefixWord ++ tailWord_2019449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019449).length < 2 ^ (prefixWord ++ tailWord_2019449).sum := by decide
  have hdescent : baseEnd_2019449 < baseStart_2019449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019459 : List Nat := [1, 1, 1, 3, 3, 3, 2, 1, 2, 3, 3]
def baseStart_2019459 : Nat := 118140960795 + 2019459 * 2 ^ 59
def prefixEnd_2019459 : Nat := 4983230072969 + 3 ^ 40 * 2019459 * 2
def baseEnd_2019459 : Nat := 1036953129048119591075183

theorem tailTrace_2019459 : CollatzResearch.WordTrace tailWord_2019459 prefixEnd_2019459 1036953129048119591075183 := by
  unfold tailWord_2019459
  simp only [CollatzResearch.WordTrace]
  refine ⟨73655720790852413983725431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49103813860568275989150287 73655720790852413983725431)
  ·
    refine ⟨110483581186278620975588147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73655720790852413983725431 110483581186278620975588147)
    ·
      refine ⟨165725371779417931463382221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110483581186278620975588147 165725371779417931463382221)
      ·
        refine ⟨62147014417281724298768333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165725371779417931463382221 62147014417281724298768333)
        ·
          refine ⟨23305130406480646612038125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62147014417281724298768333 23305130406480646612038125)
          ·
            refine ⟨8739423902430242479514297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23305130406480646612038125 8739423902430242479514297)
            ·
              refine ⟨6554567926822681859635723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8739423902430242479514297 6554567926822681859635723)
              ·
                refine ⟨9831851890234022789453585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6554567926822681859635723 9831851890234022789453585)
                ·
                  refine ⟨7373888917675517092090189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9831851890234022789453585 7373888917675517092090189)
                  ·
                    refine ⟨2765208344128318909533821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7373888917675517092090189 2765208344128318909533821)
                    ·
                      refine ⟨1036953129048119591075183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2765208344128318909533821 1036953129048119591075183)
                      ·
                        rfl

theorem cell23_2019459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3, 3].length) (baseStart_2019459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019459 prefixEnd_2019459 := by exact prefixLift 2019459
  have htrace : WordTrace (prefixWord ++ tailWord_2019459) baseStart_2019459 baseEnd_2019459 := by
    simpa [prefixWord, tailWord_2019459, baseEnd_2019459] using wordTrace_append hprefix tailTrace_2019459
  have hstable : (prefixWord ++ tailWord_2019459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019459).length < 2 ^ (prefixWord ++ tailWord_2019459).sum := by decide
  have hdescent : baseEnd_2019459 < baseStart_2019459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019460 : List Nat := [2, 3, 2, 1, 2, 1, 5, 1, 2, 2, 2]
def baseStart_2019460 : Nat := 118140960795 + 2019460 * 2 ^ 59
def prefixEnd_2019460 : Nat := 4983230072969 + 3 ^ 40 * 2019460 * 2
def baseEnd_2019460 : Nat := 1036953642528774087162679

theorem tailTrace_2019460 : CollatzResearch.WordTrace tailWord_2019460 prefixEnd_2019460 1036953642528774087162679 := by
  unfold tailWord_2019460
  simp only [CollatzResearch.WordTrace]
  refine ⟨36827878631924395577255917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49103838175899194103007889 36827878631924395577255917)
  ·
    refine ⟨13810454486971648341470969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36827878631924395577255917 13810454486971648341470969)
    ·
      refine ⟨10357840865228736256103227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13810454486971648341470969 10357840865228736256103227)
      ·
        refine ⟨15536761297843104384154841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10357840865228736256103227 15536761297843104384154841)
        ·
          refine ⟨11652570973382328288116131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15536761297843104384154841 11652570973382328288116131)
          ·
            refine ⟨17478856460073492432174197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11652570973382328288116131 17478856460073492432174197)
            ·
              refine ⟨1638642793131889915516331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17478856460073492432174197 1638642793131889915516331)
              ·
                refine ⟨2457964189697834873274497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1638642793131889915516331 2457964189697834873274497)
                ·
                  refine ⟨1843473142273376154955873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2457964189697834873274497 1843473142273376154955873)
                  ·
                    refine ⟨1382604856705032116216905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1843473142273376154955873 1382604856705032116216905)
                    ·
                      refine ⟨1036953642528774087162679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1382604856705032116216905 1036953642528774087162679)
                      ·
                        rfl

theorem cell23_2019460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_2019460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019460 prefixEnd_2019460 := by exact prefixLift 2019460
  have htrace : WordTrace (prefixWord ++ tailWord_2019460) baseStart_2019460 baseEnd_2019460 := by
    simpa [prefixWord, tailWord_2019460, baseEnd_2019460] using wordTrace_append hprefix tailTrace_2019460
  have hstable : (prefixWord ++ tailWord_2019460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019460).length < 2 ^ (prefixWord ++ tailWord_2019460).sum := by decide
  have hdescent : baseEnd_2019460 < baseStart_2019460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019519 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 6, 2, 3]
def baseStart_2019519 : Nat := 118140960795 + 2019519 * 2 ^ 59
def prefixEnd_2019519 : Nat := 4983230072969 + 3 ^ 40 * 2019519 * 2
def baseEnd_2019519 : Nat := 1036983937887389356324907

theorem tailTrace_2019519 : CollatzResearch.WordTrace tailWord_2019519 prefixEnd_2019519 1036983937887389356324907 := by
  unfold tailWord_2019519
  simp only [CollatzResearch.WordTrace]
  refine ⟨73657909170635044230909611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49105272780423362820606407 73657909170635044230909611)
  ·
    refine ⟨110486863755952566346364417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73657909170635044230909611 110486863755952566346364417)
    ·
      refine ⟨82865147816964424759773313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110486863755952566346364417 82865147816964424759773313)
      ·
        refine ⟨62148860862723318569829985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82865147816964424759773313 62148860862723318569829985)
        ·
          refine ⟨46611645647042488927372489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62148860862723318569829985 46611645647042488927372489)
          ·
            refine ⟨34958734235281866695529367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46611645647042488927372489 34958734235281866695529367)
            ·
              refine ⟨52438101352922800043294051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34958734235281866695529367 52438101352922800043294051)
              ·
                refine ⟨78657152029384200064941077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52438101352922800043294051 78657152029384200064941077)
                ·
                  refine ⟨3687054001377384378044113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78657152029384200064941077 3687054001377384378044113)
                  ·
                    refine ⟨2765290501033038283533085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3687054001377384378044113 2765290501033038283533085)
                    ·
                      refine ⟨1036983937887389356324907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2765290501033038283533085 1036983937887389356324907)
                      ·
                        rfl

theorem cell23_2019519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2, 3].length) (baseStart_2019519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019519 prefixEnd_2019519 := by exact prefixLift 2019519
  have htrace : WordTrace (prefixWord ++ tailWord_2019519) baseStart_2019519 baseEnd_2019519 := by
    simpa [prefixWord, tailWord_2019519, baseEnd_2019519] using wordTrace_append hprefix tailTrace_2019519
  have hstable : (prefixWord ++ tailWord_2019519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019519).length < 2 ^ (prefixWord ++ tailWord_2019519).sum := by decide
  have hdescent : baseEnd_2019519 < baseStart_2019519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019560 : List Nat := [2, 1, 4, 1, 2, 2, 4, 2, 1, 4]
def baseStart_2019560 : Nat := 118140960795 + 2019560 * 2 ^ 59
def prefixEnd_2019560 : Nat := 4983230072969 + 3 ^ 40 * 2019560 * 2
def baseEnd_2019560 : Nat := 345668330198074565304073

theorem tailTrace_2019560 : CollatzResearch.WordTrace tailWord_2019560 prefixEnd_2019560 345668330198074565304073 := by
  unfold tailWord_2019560
  simp only [CollatzResearch.WordTrace]
  refine ⟨36829702281743254116576067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49106269708991005488768089 36829702281743254116576067)
  ·
    refine ⟨55244553422614881174864101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36829702281743254116576067 55244553422614881174864101)
    ·
      refine ⟨10358353766740290220287019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55244553422614881174864101 10358353766740290220287019)
      ·
        refine ⟨15537530650110435330430529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10358353766740290220287019 15537530650110435330430529)
        ·
          refine ⟨11653147987582826497822897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15537530650110435330430529 11653147987582826497822897)
          ·
            refine ⟨8739860990687119873367173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11653147987582826497822897 8739860990687119873367173)
            ·
              refine ⟨1638723935753834976256345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8739860990687119873367173 1638723935753834976256345)
              ·
                refine ⟨1229042951815376232192259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1638723935753834976256345 1229042951815376232192259)
                ·
                  refine ⟨1843564427723064348288389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1229042951815376232192259 1843564427723064348288389)
                  ·
                    refine ⟨345668330198074565304073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1843564427723064348288389 345668330198074565304073)
                    ·
                      rfl

theorem cell23_2019560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_2019560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019560 prefixEnd_2019560 := by exact prefixLift 2019560
  have htrace : WordTrace (prefixWord ++ tailWord_2019560) baseStart_2019560 baseEnd_2019560 := by
    simpa [prefixWord, tailWord_2019560, baseEnd_2019560] using wordTrace_append hprefix tailTrace_2019560
  have hstable : (prefixWord ++ tailWord_2019560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019560).length < 2 ^ (prefixWord ++ tailWord_2019560).sum := by decide
  have hdescent : baseEnd_2019560 < baseStart_2019560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019569 : List Nat := [1, 2, 2, 2, 2, 1, 3, 2, 3, 5]
def baseStart_2019569 : Nat := 118140960795 + 2019569 * 2 ^ 59
def prefixEnd_2019569 : Nat := 4983230072969 + 3 ^ 40 * 2019569 * 2
def baseEnd_2019569 : Nat := 345669870640038053566559

theorem tailTrace_2019569 : CollatzResearch.WordTrace tailWord_2019569 prefixEnd_2019569 345669870640038053566559 := by
  unfold tailWord_2019569
  simp only [CollatzResearch.WordTrace]
  refine ⟨73659732820453902770229761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49106488546969268513486507 73659732820453902770229761)
  ·
    refine ⟨55244799615340427077672321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73659732820453902770229761 55244799615340427077672321)
    ·
      refine ⟨41433599711505320308254241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55244799615340427077672321 41433599711505320308254241)
      ·
        refine ⟨31075199783628990231190681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41433599711505320308254241 31075199783628990231190681)
        ·
          refine ⟨23306399837721742673393011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31075199783628990231190681 23306399837721742673393011)
          ·
            refine ⟨34959599756582614010089517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23306399837721742673393011 34959599756582614010089517)
            ·
              refine ⟨13109849908718480253783569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34959599756582614010089517 13109849908718480253783569)
              ·
                refine ⟨9832387431538860190337677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13109849908718480253783569 9832387431538860190337677)
                ·
                  refine ⟨3687145286827072571376629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9832387431538860190337677 3687145286827072571376629)
                  ·
                    refine ⟨345669870640038053566559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3687145286827072571376629 345669870640038053566559)
                    ·
                      rfl

theorem cell23_2019569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 5].length) (baseStart_2019569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019569 prefixEnd_2019569 := by exact prefixLift 2019569
  have htrace : WordTrace (prefixWord ++ tailWord_2019569) baseStart_2019569 baseEnd_2019569 := by
    simpa [prefixWord, tailWord_2019569, baseEnd_2019569] using wordTrace_append hprefix tailTrace_2019569
  have hstable : (prefixWord ++ tailWord_2019569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019569).length < 2 ^ (prefixWord ++ tailWord_2019569).sum := by decide
  have hdescent : baseEnd_2019569 < baseStart_2019569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019576 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 4, 3, 2]
def baseStart_2019576 : Nat := 118140960795 + 2019576 * 2 ^ 59
def prefixEnd_2019576 : Nat := 4983230072969 + 3 ^ 40 * 2019576 * 2
def baseEnd_2019576 : Nat := 1037013206284695633312145

theorem tailTrace_2019576 : CollatzResearch.WordTrace tailWord_2019576 prefixEnd_2019576 1037013206284695633312145 := by
  unfold tailWord_2019576
  simp only [CollatzResearch.WordTrace]
  refine ⟨36829994065714271482867291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49106658754285695310489721 36829994065714271482867291)
  ·
    refine ⟨55244991098571407224300937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36829994065714271482867291 55244991098571407224300937)
    ·
      refine ⟨41433743323928555418225703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55244991098571407224300937 41433743323928555418225703)
      ·
        refine ⟨62150614985892833127338555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41433743323928555418225703 62150614985892833127338555)
        ·
          refine ⟨93225922478839249691007833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62150614985892833127338555 93225922478839249691007833)
          ·
            refine ⟨69919441859129437268255875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93225922478839249691007833 69919441859129437268255875)
            ·
              refine ⟨104879162788694155902383813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69919441859129437268255875 104879162788694155902383813)
              ·
                refine ⟨19664843022880154231696965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104879162788694155902383813 19664843022880154231696965)
                ·
                  refine ⟨3687158066790028918443181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19664843022880154231696965 3687158066790028918443181)
                  ·
                    refine ⟨1382684275046260844416193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3687158066790028918443181 1382684275046260844416193)
                    ·
                      refine ⟨1037013206284695633312145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1382684275046260844416193 1037013206284695633312145)
                      ·
                        rfl

theorem cell23_2019576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 4, 3, 2].length) (baseStart_2019576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019576 prefixEnd_2019576 := by exact prefixLift 2019576
  have htrace : WordTrace (prefixWord ++ tailWord_2019576) baseStart_2019576 baseEnd_2019576 := by
    simpa [prefixWord, tailWord_2019576, baseEnd_2019576] using wordTrace_append hprefix tailTrace_2019576
  have hstable : (prefixWord ++ tailWord_2019576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019576).length < 2 ^ (prefixWord ++ tailWord_2019576).sum := by decide
  have hdescent : baseEnd_2019576 < baseStart_2019576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019593 : List Nat := [1, 2, 1, 1, 3, 4, 3, 1, 2, 3, 2]
def baseStart_2019593 : Nat := 118140960795 + 2019593 * 2 ^ 59
def prefixEnd_2019593 : Nat := 4983230072969 + 3 ^ 40 * 2019593 * 2
def baseEnd_2019593 : Nat := 1037021935455822066799567

theorem tailTrace_2019593 : CollatzResearch.WordTrace tailWord_2019593 prefixEnd_2019593 1037021935455822066799567 := by
  unfold tailWord_2019593
  simp only [CollatzResearch.WordTrace]
  refine ⟨73660608172366954869103433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49107072114911303246068955 73660608172366954869103433)
  ·
    refine ⟨55245456129275216151827575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73660608172366954869103433 55245456129275216151827575)
    ·
      refine ⟨82868184193912824227741363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55245456129275216151827575 82868184193912824227741363)
      ·
        refine ⟨124302276290869236341612045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82868184193912824227741363 124302276290869236341612045)
        ·
          refine ⟨46613353609075963628104517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124302276290869236341612045 46613353609075963628104517)
          ·
            refine ⟨8740003801701743180269597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46613353609075963628104517 8740003801701743180269597)
            ·
              refine ⟨3277501425638153692601099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8740003801701743180269597 3277501425638153692601099)
              ·
                refine ⟨4916252138457230538901649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3277501425638153692601099 4916252138457230538901649)
                ·
                  refine ⟨3687189103842922904176237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4916252138457230538901649 3687189103842922904176237)
                  ·
                    refine ⟨1382695913941096089066089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3687189103842922904176237 1382695913941096089066089)
                    ·
                      refine ⟨1037021935455822066799567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1382695913941096089066089 1037021935455822066799567)
                      ·
                        rfl

theorem cell23_2019593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 3, 2].length) (baseStart_2019593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019593 prefixEnd_2019593 := by exact prefixLift 2019593
  have htrace : WordTrace (prefixWord ++ tailWord_2019593) baseStart_2019593 baseEnd_2019593 := by
    simpa [prefixWord, tailWord_2019593, baseEnd_2019593] using wordTrace_append hprefix tailTrace_2019593
  have hstable : (prefixWord ++ tailWord_2019593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019593).length < 2 ^ (prefixWord ++ tailWord_2019593).sum := by decide
  have hdescent : baseEnd_2019593 < baseStart_2019593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019619 : List Nat := [1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 6]
def baseStart_2019619 : Nat := 118140960795 + 2019619 * 2 ^ 59
def prefixEnd_2019619 : Nat := 4983230072969 + 3 ^ 40 * 2019619 * 2
def baseEnd_2019619 : Nat := 1037035285952838965074447

theorem tailTrace_2019619 : CollatzResearch.WordTrace tailWord_2019619 prefixEnd_2019619 1037035285952838965074447 := by
  unfold tailWord_2019619
  simp only [CollatzResearch.WordTrace]
  refine ⟨73661556470272761309549911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49107704313515174206366607 73661556470272761309549911)
  ·
    refine ⟨110492334705409141964324867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73661556470272761309549911 110492334705409141964324867)
    ·
      refine ⟨165738502058113712946487301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110492334705409141964324867 165738502058113712946487301)
      ·
        refine ⟨31075969135896321177466369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165738502058113712946487301 31075969135896321177466369)
        ·
          refine ⟨23306976851922240883099777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31075969135896321177466369 23306976851922240883099777)
          ·
            refine ⟨17480232638941680662324833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23306976851922240883099777 17480232638941680662324833)
            ·
              refine ⟨13110174479206260496743625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17480232638941680662324833 13110174479206260496743625)
              ·
                refine ⟨9832630859404695372557719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13110174479206260496743625 9832630859404695372557719)
                ·
                  refine ⟨14748946289107043058836579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9832630859404695372557719 14748946289107043058836579)
                  ·
                    refine ⟨22123419433660564588254869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14748946289107043058836579 22123419433660564588254869)
                    ·
                      refine ⟨1037035285952838965074447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22123419433660564588254869 1037035285952838965074447)
                      ·
                        rfl

theorem cell23_2019619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_2019619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019619 prefixEnd_2019619 := by exact prefixLift 2019619
  have htrace : WordTrace (prefixWord ++ tailWord_2019619) baseStart_2019619 baseEnd_2019619 := by
    simpa [prefixWord, tailWord_2019619, baseEnd_2019619] using wordTrace_append hprefix tailTrace_2019619
  have hstable : (prefixWord ++ tailWord_2019619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019619).length < 2 ^ (prefixWord ++ tailWord_2019619).sum := by decide
  have hdescent : baseEnd_2019619 < baseStart_2019619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019633 : List Nat := [1, 2, 2, 3, 4, 2, 1, 1, 1, 6]
def baseStart_2019633 : Nat := 118140960795 + 2019633 * 2 ^ 59
def prefixEnd_2019633 : Nat := 4983230072969 + 3 ^ 40 * 2019633 * 2
def baseEnd_2019633 : Nat := 345680824894000636766461

theorem tailTrace_2019633 : CollatzResearch.WordTrace tailWord_2019633 prefixEnd_2019633 345680824894000636766461 := by
  unfold tailWord_2019633
  simp only [CollatzResearch.WordTrace]
  refine ⟨73662067092222041700559553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49108044728148027800373035 73662067092222041700559553)
  ·
    refine ⟨55246550319166531275419665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73662067092222041700559553 55246550319166531275419665)
    ·
      refine ⟨41434912739374898456564749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55246550319166531275419665 41434912739374898456564749)
      ·
        refine ⟨15538092277265586921211781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41434912739374898456564749 15538092277265586921211781)
        ·
          refine ⟨2913392301987297547727209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15538092277265586921211781 2913392301987297547727209)
          ·
            refine ⟨2185044226490473160795407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2913392301987297547727209 2185044226490473160795407)
            ·
              refine ⟨3277566339735709741193111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2185044226490473160795407 3277566339735709741193111)
              ·
                refine ⟨4916349509603564611789667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3277566339735709741193111 4916349509603564611789667)
                ·
                  refine ⟨7374524264405346917684501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4916349509603564611789667 7374524264405346917684501)
                  ·
                    refine ⟨345680824894000636766461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7374524264405346917684501 345680824894000636766461)
                    ·
                      rfl

theorem cell23_2019633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 6].length) (baseStart_2019633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019633 prefixEnd_2019633 := by exact prefixLift 2019633
  have htrace : WordTrace (prefixWord ++ tailWord_2019633) baseStart_2019633 baseEnd_2019633 := by
    simpa [prefixWord, tailWord_2019633, baseEnd_2019633] using wordTrace_append hprefix tailTrace_2019633
  have hstable : (prefixWord ++ tailWord_2019633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019633).length < 2 ^ (prefixWord ++ tailWord_2019633).sum := by decide
  have hdescent : baseEnd_2019633 < baseStart_2019633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019646 : List Nat := [4, 2, 1, 2, 1, 3, 1, 9]
def baseStart_2019646 : Nat := 118140960795 + 2019646 * 2 ^ 59
def prefixEnd_2019646 : Nat := 4983230072969 + 3 ^ 40 * 2019646 * 2
def baseEnd_2019646 : Nat := 38409227775204087386549

theorem tailTrace_2019646 : CollatzResearch.WordTrace tailWord_2019646 prefixEnd_2019646 38409227775204087386549 := by
  unfold tailWord_2019646
  simp only [CollatzResearch.WordTrace]
  refine ⟨9207817655146868115097849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49108360827449963280521861 9207817655146868115097849)
  ·
    refine ⟨6905863241360151086323387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9207817655146868115097849 6905863241360151086323387)
    ·
      refine ⟨10358794862040226629485081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6905863241360151086323387 10358794862040226629485081)
      ·
        refine ⟨7769096146530169972113811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10358794862040226629485081 7769096146530169972113811)
        ·
          refine ⟨11653644219795254958170717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7769096146530169972113811 11653644219795254958170717)
          ·
            refine ⟨4370116582423220609314019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11653644219795254958170717 4370116582423220609314019)
            ·
              refine ⟨6555174873634830913971029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4370116582423220609314019 6555174873634830913971029)
              ·
                refine ⟨38409227775204087386549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6555174873634830913971029 38409227775204087386549)
                ·
                  rfl

theorem cell23_2019646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 9].length) (baseStart_2019646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019646 prefixEnd_2019646 := by exact prefixLift 2019646
  have htrace : WordTrace (prefixWord ++ tailWord_2019646) baseStart_2019646 baseEnd_2019646 := by
    simpa [prefixWord, tailWord_2019646, baseEnd_2019646] using wordTrace_append hprefix tailTrace_2019646
  have hstable : (prefixWord ++ tailWord_2019646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019646).length < 2 ^ (prefixWord ++ tailWord_2019646).sum := by decide
  have hdescent : baseEnd_2019646 < baseStart_2019646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019656 : List Nat := [2, 1, 3, 1, 1, 2, 2, 4, 1, 3, 3]
def baseStart_2019656 : Nat := 118140960795 + 2019656 * 2 ^ 59
def prefixEnd_2019656 : Nat := 4983230072969 + 3 ^ 40 * 2019656 * 2
def baseEnd_2019656 : Nat := 1037054284737055320311777

theorem tailTrace_2019656 : CollatzResearch.WordTrace tailWord_2019656 prefixEnd_2019656 1037054284737055320311777 := by
  unfold tailWord_2019656
  simp only [CollatzResearch.WordTrace]
  refine ⟨36831452985569358314323411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49108603980759144419097881 36831452985569358314323411)
  ·
    refine ⟨55247179478354037471485117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36831452985569358314323411 55247179478354037471485117)
    ·
      refine ⟨20717692304382764051806919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55247179478354037471485117 20717692304382764051806919)
      ·
        refine ⟨31076538456574146077710379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20717692304382764051806919 31076538456574146077710379)
        ·
          refine ⟨46614807684861219116565569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31076538456574146077710379 46614807684861219116565569)
          ·
            refine ⟨34961105763645914337424177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46614807684861219116565569 34961105763645914337424177)
            ·
              refine ⟨26220829322734435753068133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34961105763645914337424177 26220829322734435753068133)
              ·
                refine ⟨4916405498012706703700275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26220829322734435753068133 4916405498012706703700275)
                ·
                  refine ⟨7374608247019060055550413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4916405498012706703700275 7374608247019060055550413)
                  ·
                    refine ⟨2765478092632147520831405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7374608247019060055550413 2765478092632147520831405)
                    ·
                      refine ⟨1037054284737055320311777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2765478092632147520831405 1037054284737055320311777)
                      ·
                        rfl

theorem cell23_2019656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_2019656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019656 prefixEnd_2019656 := by exact prefixLift 2019656
  have htrace : WordTrace (prefixWord ++ tailWord_2019656) baseStart_2019656 baseEnd_2019656 := by
    simpa [prefixWord, tailWord_2019656, baseEnd_2019656] using wordTrace_append hprefix tailTrace_2019656
  have hstable : (prefixWord ++ tailWord_2019656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019656).length < 2 ^ (prefixWord ++ tailWord_2019656).sum := by decide
  have hdescent : baseEnd_2019656 < baseStart_2019656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019673 : List Nat := [1, 2, 1, 2, 2, 2, 1, 6, 2, 1, 3]
def baseStart_2019673 : Nat := 118140960795 + 2019673 * 2 ^ 59
def prefixEnd_2019673 : Nat := 4983230072969 + 3 ^ 40 * 2019673 * 2
def baseEnd_2019673 : Nat := 1037063013908181753799199

theorem tailTrace_2019673 : CollatzResearch.WordTrace tailWord_2019673 prefixEnd_2019673 1037063013908181753799199 := by
  unfold tailWord_2019673
  simp only [CollatzResearch.WordTrace]
  refine ⟨73663526012077128532015673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49109017341384752354677115 73663526012077128532015673)
  ·
    refine ⟨55247644509057846399011755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73663526012077128532015673 55247644509057846399011755)
    ·
      refine ⟨82871466763586769598517633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55247644509057846399011755 82871466763586769598517633)
      ·
        refine ⟨62153600072690077198888225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82871466763586769598517633 62153600072690077198888225)
        ·
          refine ⟨46615200054517557899166169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62153600072690077198888225 46615200054517557899166169)
          ·
            refine ⟨34961400040888168424374627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46615200054517557899166169 34961400040888168424374627)
            ·
              refine ⟨52442100061332252636561941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34961400040888168424374627 52442100061332252636561941)
              ·
                refine ⟨2458223440374949342338841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52442100061332252636561941 2458223440374949342338841)
                ·
                  refine ⟨1843667580281212006754131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2458223440374949342338841 1843667580281212006754131)
                  ·
                    refine ⟨2765501370421818010131197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1843667580281212006754131 2765501370421818010131197)
                    ·
                      refine ⟨1037063013908181753799199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2765501370421818010131197 1037063013908181753799199)
                      ·
                        rfl

theorem cell23_2019673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2, 1, 3].length) (baseStart_2019673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019673 prefixEnd_2019673 := by exact prefixLift 2019673
  have htrace : WordTrace (prefixWord ++ tailWord_2019673) baseStart_2019673 baseEnd_2019673 := by
    simpa [prefixWord, tailWord_2019673, baseEnd_2019673] using wordTrace_append hprefix tailTrace_2019673
  have hstable : (prefixWord ++ tailWord_2019673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019673).length < 2 ^ (prefixWord ++ tailWord_2019673).sum := by decide
  have hdescent : baseEnd_2019673 < baseStart_2019673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019683 : List Nat := [1, 1, 1, 5, 2, 1, 2, 2, 3, 3, 2]
def baseStart_2019683 : Nat := 118140960795 + 2019683 * 2 ^ 59
def prefixEnd_2019683 : Nat := 4983230072969 + 3 ^ 40 * 2019683 * 2
def baseEnd_2019683 : Nat := 1037068148714726714674153

theorem tailTrace_2019683 : CollatzResearch.WordTrace tailWord_2019683 prefixEnd_2019683 1037068148714726714674153 := by
  unfold tailWord_2019683
  simp only [CollatzResearch.WordTrace]
  refine ⟨73663890742040900239879703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49109260494693933493253135 73663890742040900239879703)
  ·
    refine ⟨110495836113061350359819555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73663890742040900239879703 110495836113061350359819555)
    ·
      refine ⟨165743754169592025539729333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110495836113061350359819555 165743754169592025539729333)
      ·
        refine ⟨15538476953399252394349625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165743754169592025539729333 15538476953399252394349625)
        ·
          refine ⟨11653857715049439295762219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15538476953399252394349625 11653857715049439295762219)
          ·
            refine ⟨17480786572574158943643329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11653857715049439295762219 17480786572574158943643329)
            ·
              refine ⟨13110589929430619207732497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17480786572574158943643329 13110589929430619207732497)
              ·
                refine ⟨9832942447072964405799373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13110589929430619207732497 9832942447072964405799373)
                ·
                  refine ⟨3687353417652361652174765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9832942447072964405799373 3687353417652361652174765)
                  ·
                    refine ⟨1382757531619635619565537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3687353417652361652174765 1382757531619635619565537)
                    ·
                      refine ⟨1037068148714726714674153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1382757531619635619565537 1037068148714726714674153)
                      ·
                        rfl

theorem cell23_2019683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_2019683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019683 prefixEnd_2019683 := by exact prefixLift 2019683
  have htrace : WordTrace (prefixWord ++ tailWord_2019683) baseStart_2019683 baseEnd_2019683 := by
    simpa [prefixWord, tailWord_2019683, baseEnd_2019683] using wordTrace_append hprefix tailTrace_2019683
  have hstable : (prefixWord ++ tailWord_2019683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019683).length < 2 ^ (prefixWord ++ tailWord_2019683).sum := by decide
  have hdescent : baseEnd_2019683 < baseStart_2019683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019689 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 1, 8]
def baseStart_2019689 : Nat := 118140960795 + 2019689 * 2 ^ 59
def prefixEnd_2019689 : Nat := 4983230072969 + 3 ^ 40 * 2019689 * 2
def baseEnd_2019689 : Nat := 345690409866217897066375

theorem tailTrace_2019689 : CollatzResearch.WordTrace tailWord_2019689 prefixEnd_2019689 345690409866217897066375 := by
  unfold tailWord_2019689
  simp only [CollatzResearch.WordTrace]
  refine ⟨73664109580019163264598121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49109406386679442176398747 73664109580019163264598121)
  ·
    refine ⟨55248082185014372448448591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73664109580019163264598121 55248082185014372448448591)
    ·
      refine ⟨82872123277521558672672887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55248082185014372448448591 82872123277521558672672887)
      ·
        refine ⟨124308184916282338009009331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82872123277521558672672887 124308184916282338009009331)
        ·
          refine ⟨186462277374423507013513997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124308184916282338009009331 186462277374423507013513997)
          ·
            refine ⟨69923354015408815130067749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186462277374423507013513997 69923354015408815130067749)
            ·
              refine ⟨13110628877889152836887703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69923354015408815130067749 13110628877889152836887703)
              ·
                refine ⟨19665943316833729255331555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13110628877889152836887703 19665943316833729255331555)
                ·
                  refine ⟨29498914975250593882997333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19665943316833729255331555 29498914975250593882997333)
                  ·
                    refine ⟨345690409866217897066375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29498914975250593882997333 345690409866217897066375)
                    ·
                      rfl

theorem cell23_2019689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 8].length) (baseStart_2019689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019689 prefixEnd_2019689 := by exact prefixLift 2019689
  have htrace : WordTrace (prefixWord ++ tailWord_2019689) baseStart_2019689 baseEnd_2019689 := by
    simpa [prefixWord, tailWord_2019689, baseEnd_2019689] using wordTrace_append hprefix tailTrace_2019689
  have hstable : (prefixWord ++ tailWord_2019689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019689).length < 2 ^ (prefixWord ++ tailWord_2019689).sum := by decide
  have hdescent : baseEnd_2019689 < baseStart_2019689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019699 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 5]
def baseStart_2019699 : Nat := 118140960795 + 2019699 * 2 ^ 59
def prefixEnd_2019699 : Nat := 4983230072969 + 3 ^ 40 * 2019699 * 2
def baseEnd_2019699 : Nat := 1037076364405198652074079

theorem tailTrace_2019699 : CollatzResearch.WordTrace tailWord_2019699 prefixEnd_2019699 1037076364405198652074079 := by
  unfold tailWord_2019699
  simp only [CollatzResearch.WordTrace]
  refine ⟨73664474309982934972462151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49109649539988623314974767 73664474309982934972462151)
  ·
    refine ⟨110496711464974402458693227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73664474309982934972462151 110496711464974402458693227)
    ·
      refine ⟨165745067197461603688039841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110496711464974402458693227 165745067197461603688039841)
      ·
        refine ⟨124308800398096202766029881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165745067197461603688039841 124308800398096202766029881)
        ·
          refine ⟨93231600298572152074522411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124308800398096202766029881 93231600298572152074522411)
          ·
            refine ⟨139847400447858228111783617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93231600298572152074522411 139847400447858228111783617)
            ·
              refine ⟨104885550335893671083837713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139847400447858228111783617 104885550335893671083837713)
              ·
                refine ⟨78664162751920253312878285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104885550335893671083837713 78664162751920253312878285)
                ·
                  refine ⟨29499061031970094992329357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78664162751920253312878285 29499061031970094992329357)
                  ·
                    refine ⟨11062147886988785622123509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29499061031970094992329357 11062147886988785622123509)
                    ·
                      refine ⟨1037076364405198652074079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11062147886988785622123509 1037076364405198652074079)
                      ·
                        rfl

theorem cell23_2019699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 5].length) (baseStart_2019699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019699 prefixEnd_2019699 := by exact prefixLift 2019699
  have htrace : WordTrace (prefixWord ++ tailWord_2019699) baseStart_2019699 baseEnd_2019699 := by
    simpa [prefixWord, tailWord_2019699, baseEnd_2019699] using wordTrace_append hprefix tailTrace_2019699
  have hstable : (prefixWord ++ tailWord_2019699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019699).length < 2 ^ (prefixWord ++ tailWord_2019699).sum := by decide
  have hdescent : baseEnd_2019699 < baseStart_2019699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019716 : List Nat := [2, 3, 2, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_2019716 : Nat := 118140960795 + 2019716 * 2 ^ 59
def prefixEnd_2019716 : Nat := 4983230072969 + 3 ^ 40 * 2019716 * 2
def baseEnd_2019716 : Nat := 1037085093576325085561501

theorem tailTrace_2019716 : CollatzResearch.WordTrace tailWord_2019716 prefixEnd_2019716 1037085093576325085561501 := by
  unfold tailWord_2019716
  simp only [CollatzResearch.WordTrace]
  refine ⟨36832547175460673437915501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49110062900614231250554001 36832547175460673437915501)
  ·
    refine ⟨13812205190797752539218313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36832547175460673437915501 13812205190797752539218313)
    ·
      refine ⟨10359153893098314404413735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13812205190797752539218313 10359153893098314404413735)
      ·
        refine ⟨15538730839647471606620603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10359153893098314404413735 15538730839647471606620603)
        ·
          refine ⟨23308096259471207409930905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15538730839647471606620603 23308096259471207409930905)
          ·
            refine ⟨17481072194603405557448179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23308096259471207409930905 17481072194603405557448179)
            ·
              refine ⟨26221608291905108336172269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17481072194603405557448179 26221608291905108336172269)
              ·
                refine ⟨9833103109464415626064601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26221608291905108336172269 9833103109464415626064601)
                ·
                  refine ⟨7374827332098311719548451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9833103109464415626064601 7374827332098311719548451)
                  ·
                    refine ⟨11062240998147467579322677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7374827332098311719548451 11062240998147467579322677)
                    ·
                      refine ⟨1037085093576325085561501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11062240998147467579322677 1037085093576325085561501)
                      ·
                        rfl

theorem cell23_2019716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_2019716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019716 prefixEnd_2019716 := by exact prefixLift 2019716
  have htrace : WordTrace (prefixWord ++ tailWord_2019716) baseStart_2019716 baseEnd_2019716 := by
    simpa [prefixWord, tailWord_2019716, baseEnd_2019716] using wordTrace_append hprefix tailTrace_2019716
  have hstable : (prefixWord ++ tailWord_2019716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019716).length < 2 ^ (prefixWord ++ tailWord_2019716).sum := by decide
  have hdescent : baseEnd_2019716 < baseStart_2019716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019823 : List Nat := [1, 1, 2, 1, 4, 1, 1, 5, 2, 2, 3]
def baseStart_2019823 : Nat := 118140960795 + 2019823 * 2 ^ 59
def prefixEnd_2019823 : Nat := 4983230072969 + 3 ^ 40 * 2019823 * 2
def baseEnd_2019823 : Nat := 1037140036006356166923509

theorem tailTrace_2019823 : CollatzResearch.WordTrace tailWord_2019823 prefixEnd_2019823 1037140036006356166923509 := by
  unfold tailWord_2019823
  simp only [CollatzResearch.WordTrace]
  refine ⟨73668996961533704149976123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49112664641022469433317415 73668996961533704149976123)
  ·
    refine ⟨110503495442300556224964185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73668996961533704149976123 110503495442300556224964185)
    ·
      refine ⟨82877621581725417168723139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110503495442300556224964185 82877621581725417168723139)
      ·
        refine ⟨124316432372588125753084709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82877621581725417168723139 124316432372588125753084709)
        ·
          refine ⟨23309331069860273578703383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124316432372588125753084709 23309331069860273578703383)
          ·
            refine ⟨34963996604790410368055075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23309331069860273578703383 34963996604790410368055075)
            ·
              refine ⟨52445994907185615552082613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34963996604790410368055075 52445994907185615552082613)
              ·
                refine ⟨4916812022548651458007745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52445994907185615552082613 4916812022548651458007745)
                ·
                  refine ⟨3687609016911488593505809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4916812022548651458007745 3687609016911488593505809)
                  ·
                    refine ⟨2765706762683616445129357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3687609016911488593505809 2765706762683616445129357)
                    ·
                      refine ⟨1037140036006356166923509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2765706762683616445129357 1037140036006356166923509)
                      ·
                        rfl

theorem cell23_2019823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2, 3].length) (baseStart_2019823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019823 prefixEnd_2019823 := by exact prefixLift 2019823
  have htrace : WordTrace (prefixWord ++ tailWord_2019823) baseStart_2019823 baseEnd_2019823 := by
    simpa [prefixWord, tailWord_2019823, baseEnd_2019823] using wordTrace_append hprefix tailTrace_2019823
  have hstable : (prefixWord ++ tailWord_2019823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019823).length < 2 ^ (prefixWord ++ tailWord_2019823).sum := by decide
  have hdescent : baseEnd_2019823 < baseStart_2019823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019847 : List Nat := [1, 1, 4, 3, 3, 2, 1, 1, 3, 4]
def baseStart_2019847 : Nat := 118140960795 + 2019847 * 2 ^ 59
def prefixEnd_2019847 : Nat := 4983230072969 + 3 ^ 40 * 2019847 * 2
def baseEnd_2019847 : Nat := 345717453180688024341133

theorem tailTrace_2019847 : CollatzResearch.WordTrace tailWord_2019847 prefixEnd_2019847 345717453180688024341133 := by
  unfold tailWord_2019847
  simp only [CollatzResearch.WordTrace]
  refine ⟨73669872313446756248849795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49113248208964504165899863 73669872313446756248849795)
  ·
    refine ⟨110504808470170134373274693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73669872313446756248849795 110504808470170134373274693)
    ·
      refine ⟨20719651588156900194989005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110504808470170134373274693 20719651588156900194989005)
      ·
        refine ⟨7769869345558837573120877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20719651588156900194989005 7769869345558837573120877)
        ·
          refine ⟨2913701004584564089920329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7769869345558837573120877 2913701004584564089920329)
          ·
            refine ⟨2185275753438423067440247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2913701004584564089920329 2185275753438423067440247)
            ·
              refine ⟨3277913630157634601160371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2185275753438423067440247 3277913630157634601160371)
              ·
                refine ⟨4916870445236451901740557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3277913630157634601160371 4916870445236451901740557)
                ·
                  refine ⟨1843826416963669463152709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4916870445236451901740557 1843826416963669463152709)
                  ·
                    refine ⟨345717453180688024341133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1843826416963669463152709 345717453180688024341133)
                    ·
                      rfl

theorem cell23_2019847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_2019847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019847 prefixEnd_2019847 := by exact prefixLift 2019847
  have htrace : WordTrace (prefixWord ++ tailWord_2019847) baseStart_2019847 baseEnd_2019847 := by
    simpa [prefixWord, tailWord_2019847, baseEnd_2019847] using wordTrace_append hprefix tailTrace_2019847
  have hstable : (prefixWord ++ tailWord_2019847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019847).length < 2 ^ (prefixWord ++ tailWord_2019847).sum := by decide
  have hdescent : baseEnd_2019847 < baseStart_2019847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019873 : List Nat := [1, 2, 3, 2, 2, 1, 3, 1, 3, 5]
def baseStart_2019873 : Nat := 118140960795 + 2019873 * 2 ^ 59
def prefixEnd_2019873 : Nat := 4983230072969 + 3 ^ 40 * 2019873 * 2
def baseEnd_2019873 : Nat := 345721903346360323766093

theorem tailTrace_2019873 : CollatzResearch.WordTrace tailWord_2019873 prefixEnd_2019873 345721903346360323766093 := by
  unfold tailWord_2019873
  simp only [CollatzResearch.WordTrace]
  refine ⟨73670820611352562689296273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49113880407568375126197515 73670820611352562689296273)
  ·
    refine ⟨55253115458514422016972205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73670820611352562689296273 55253115458514422016972205)
    ·
      refine ⟨20719918296942908256364577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55253115458514422016972205 20719918296942908256364577)
      ·
        refine ⟨15539938722707181192273433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20719918296942908256364577 15539938722707181192273433)
        ·
          refine ⟨11654954042030385894205075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15539938722707181192273433 11654954042030385894205075)
          ·
            refine ⟨17482431063045578841307613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11654954042030385894205075 17482431063045578841307613)
            ·
              refine ⟨6555911648642092065490355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17482431063045578841307613 6555911648642092065490355)
              ·
                refine ⟨9833867472963138098235533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6555911648642092065490355 9833867472963138098235533)
                ·
                  refine ⟨3687700302361176786838325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9833867472963138098235533 3687700302361176786838325)
                  ·
                    refine ⟨345721903346360323766093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3687700302361176786838325 345721903346360323766093)
                    ·
                      rfl

theorem cell23_2019873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_2019873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019873 prefixEnd_2019873 := by exact prefixLift 2019873
  have htrace : WordTrace (prefixWord ++ tailWord_2019873) baseStart_2019873 baseEnd_2019873 := by
    simpa [prefixWord, tailWord_2019873, baseEnd_2019873] using wordTrace_append hprefix tailTrace_2019873
  have hstable : (prefixWord ++ tailWord_2019873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019873).length < 2 ^ (prefixWord ++ tailWord_2019873).sum := by decide
  have hdescent : baseEnd_2019873 < baseStart_2019873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019904 : List Nat := [2, 1, 1, 2, 2, 2, 6, 2, 1, 1, 3]
def baseStart_2019904 : Nat := 118140960795 + 2019904 * 2 ^ 59
def prefixEnd_2019904 : Nat := 4983230072969 + 3 ^ 40 * 2019904 * 2
def baseEnd_2019904 : Nat := 1037181627939370350010637

theorem tailTrace_2019904 : CollatzResearch.WordTrace tailWord_2019904 prefixEnd_2019904 1037181627939370350010637 := by
  unfold tailWord_2019904
  simp only [CollatzResearch.WordTrace]
  refine ⟨36835975637120127491837383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49114634182826836655783177 36835975637120127491837383)
  ·
    refine ⟨55253963455680191237756075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36835975637120127491837383 55253963455680191237756075)
    ·
      refine ⟨82880945183520286856634113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55253963455680191237756075 82880945183520286856634113)
      ·
        refine ⟨62160708887640215142475585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82880945183520286856634113 62160708887640215142475585)
        ·
          refine ⟨46620531665730161356856689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62160708887640215142475585 46620531665730161356856689)
          ·
            refine ⟨34965398749297621017642517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46620531665730161356856689 34965398749297621017642517)
            ·
              refine ⟨1639003066373325985201993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34965398749297621017642517 1639003066373325985201993)
              ·
                refine ⟨1229252299779994488901495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1639003066373325985201993 1229252299779994488901495)
                ·
                  refine ⟨1843878449669991733352243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1229252299779994488901495 1843878449669991733352243)
                  ·
                    refine ⟨2765817674504987600028365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1843878449669991733352243 2765817674504987600028365)
                    ·
                      refine ⟨1037181627939370350010637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2765817674504987600028365 1037181627939370350010637)
                      ·
                        rfl

theorem cell23_2019904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2, 1, 1, 3].length) (baseStart_2019904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019904 prefixEnd_2019904 := by exact prefixLift 2019904
  have htrace : WordTrace (prefixWord ++ tailWord_2019904) baseStart_2019904 baseEnd_2019904 := by
    simpa [prefixWord, tailWord_2019904, baseEnd_2019904] using wordTrace_append hprefix tailTrace_2019904
  have hstable : (prefixWord ++ tailWord_2019904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019904).length < 2 ^ (prefixWord ++ tailWord_2019904).sum := by decide
  have hdescent : baseEnd_2019904 < baseStart_2019904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019927 : List Nat := [1, 1, 3, 2, 2, 2, 3, 2, 3, 2, 2]
def baseStart_2019927 : Nat := 118140960795 + 2019927 * 2 ^ 59
def prefixEnd_2019927 : Nat := 4983230072969 + 3 ^ 40 * 2019927 * 2
def baseEnd_2019927 : Nat := 1037193437994423760023031

theorem tailTrace_2019927 : CollatzResearch.WordTrace tailWord_2019927 prefixEnd_2019927 1037193437994423760023031 := by
  unfold tailWord_2019927
  simp only [CollatzResearch.WordTrace]
  refine ⟨73672790153156929911762035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49115193435437953274508023 73672790153156929911762035)
  ·
    refine ⟨110509185229735394867643053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73672790153156929911762035 110509185229735394867643053)
    ·
      refine ⟨41440944461150773075366145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110509185229735394867643053 41440944461150773075366145)
      ·
        refine ⟨31080708345863079806524609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41440944461150773075366145 31080708345863079806524609)
        ·
          refine ⟨23310531259397309854893457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31080708345863079806524609 23310531259397309854893457)
          ·
            refine ⟨17482898444547982391170093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23310531259397309854893457 17482898444547982391170093)
            ·
              refine ⟨6556086916705493396688785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17482898444547982391170093 6556086916705493396688785)
              ·
                refine ⟨4917065187529120047516589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6556086916705493396688785 4917065187529120047516589)
                ·
                  refine ⟨1843899445323420017818721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4917065187529120047516589 1843899445323420017818721)
                  ·
                    refine ⟨1382924583992565013364041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1843899445323420017818721 1382924583992565013364041)
                    ·
                      refine ⟨1037193437994423760023031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1382924583992565013364041 1037193437994423760023031)
                      ·
                        rfl

theorem cell23_2019927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3, 2, 2].length) (baseStart_2019927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019927 prefixEnd_2019927 := by exact prefixLift 2019927
  have htrace : WordTrace (prefixWord ++ tailWord_2019927) baseStart_2019927 baseEnd_2019927 := by
    simpa [prefixWord, tailWord_2019927, baseEnd_2019927] using wordTrace_append hprefix tailTrace_2019927
  have hstable : (prefixWord ++ tailWord_2019927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019927).length < 2 ^ (prefixWord ++ tailWord_2019927).sum := by decide
  have hdescent : baseEnd_2019927 < baseStart_2019927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019938 : List Nat := [3, 3, 2, 3, 1, 1, 2, 3, 1, 1, 3]
def baseStart_2019938 : Nat := 118140960795 + 2019938 * 2 ^ 59
def prefixEnd_2019938 : Nat := 4983230072969 + 3 ^ 40 * 2019938 * 2
def baseEnd_2019938 : Nat := 1037199086281623216985481

theorem tailTrace_2019938 : CollatzResearch.WordTrace tailWord_2019938 prefixEnd_2019938 1037199086281623216985481 := by
  unfold tailWord_2019938
  simp only [CollatzResearch.WordTrace]
  refine ⟨18418297839029269697603117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49115460904078052526941645 18418297839029269697603117)
  ·
    refine ⟨6906861689635976136601169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18418297839029269697603117 6906861689635976136601169)
    ·
      refine ⟨5180146267226982102450877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6906861689635976136601169 5180146267226982102450877)
      ·
        refine ⟨1942554850210118288419079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5180146267226982102450877 1942554850210118288419079)
        ·
          refine ⟨2913832275315177432628619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1942554850210118288419079 2913832275315177432628619)
          ·
            refine ⟨4370748412972766148942929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2913832275315177432628619 4370748412972766148942929)
            ·
              refine ⟨3278061309729574611707197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4370748412972766148942929 3278061309729574611707197)
              ·
                refine ⟨1229272991148590479390199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3278061309729574611707197 1229272991148590479390199)
                ·
                  refine ⟨1843909486722885719085299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1229272991148590479390199 1843909486722885719085299)
                  ·
                    refine ⟨2765864230084328578627949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1843909486722885719085299 2765864230084328578627949)
                    ·
                      refine ⟨1037199086281623216985481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2765864230084328578627949 1037199086281623216985481)
                      ·
                        rfl

theorem cell23_2019938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_2019938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019938 prefixEnd_2019938 := by exact prefixLift 2019938
  have htrace : WordTrace (prefixWord ++ tailWord_2019938) baseStart_2019938 baseEnd_2019938 := by
    simpa [prefixWord, tailWord_2019938, baseEnd_2019938] using wordTrace_append hprefix tailTrace_2019938
  have hstable : (prefixWord ++ tailWord_2019938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019938).length < 2 ^ (prefixWord ++ tailWord_2019938).sum := by decide
  have hdescent : baseEnd_2019938 < baseStart_2019938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019954 : List Nat := [3, 2, 1, 2, 4, 2, 1, 2, 2, 4]
def baseStart_2019954 : Nat := 118140960795 + 2019954 * 2 ^ 59
def prefixEnd_2019954 : Nat := 4983230072969 + 3 ^ 40 * 2019954 * 2
def baseEnd_2019954 : Nat := 345735767324031718128469

theorem tailTrace_2019954 : CollatzResearch.WordTrace tailWord_2019954 prefixEnd_2019954 345735767324031718128469 := by
  unfold tailWord_2019954
  simp only [CollatzResearch.WordTrace]
  refine ⟨18418443731014778380748729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49115849949372742348663277 18418443731014778380748729)
  ·
    refine ⟨13813832798261083785561547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18418443731014778380748729 13813832798261083785561547)
    ·
      refine ⟨20720749197391625678342321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13813832798261083785561547 20720749197391625678342321)
      ·
        refine ⟨15540561898043719258756741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20720749197391625678342321 15540561898043719258756741)
        ·
          refine ⟨2913855355883197361016889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15540561898043719258756741 2913855355883197361016889)
          ·
            refine ⟨2185391516912398020762667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2913855355883197361016889 2185391516912398020762667)
            ·
              refine ⟨3278087275368597031144001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2185391516912398020762667 3278087275368597031144001)
              ·
                refine ⟨2458565456526447773358001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3278087275368597031144001 2458565456526447773358001)
                ·
                  refine ⟨1843924092394835830018501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2458565456526447773358001 1843924092394835830018501)
                  ·
                    refine ⟨345735767324031718128469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1843924092394835830018501 345735767324031718128469)
                    ·
                      rfl

theorem cell23_2019954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_2019954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019954 prefixEnd_2019954 := by exact prefixLift 2019954
  have htrace : WordTrace (prefixWord ++ tailWord_2019954) baseStart_2019954 baseEnd_2019954 := by
    simpa [prefixWord, tailWord_2019954, baseEnd_2019954] using wordTrace_append hprefix tailTrace_2019954
  have hstable : (prefixWord ++ tailWord_2019954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019954).length < 2 ^ (prefixWord ++ tailWord_2019954).sum := by decide
  have hdescent : baseEnd_2019954 < baseStart_2019954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019960 : List Nat := [2, 1, 2, 1, 1, 1, 2, 5, 4, 1, 3]
def baseStart_2019960 : Nat := 118140960795 + 2019960 * 2 ^ 59
def prefixEnd_2019960 : Nat := 4983230072969 + 3 ^ 40 * 2019960 * 2
def baseEnd_2019960 : Nat := 1037210382856022130910379

theorem tailTrace_2019960 : CollatzResearch.WordTrace tailWord_2019960 prefixEnd_2019960 1037210382856022130910379 := by
  unfold tailWord_2019960
  simp only [CollatzResearch.WordTrace]
  refine ⟨36836996881018688273856667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49115995841358251031808889 36836996881018688273856667)
  ·
    refine ⟨55255495321528032410785001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36836996881018688273856667 55255495321528032410785001)
    ·
      refine ⟨41441621491146024308088751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55255495321528032410785001 41441621491146024308088751)
      ·
        refine ⟨62162432236719036462133127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41441621491146024308088751 62162432236719036462133127)
        ·
          refine ⟨93243648355078554693199691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62162432236719036462133127 93243648355078554693199691)
          ·
            refine ⟨139865472532617832039799537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93243648355078554693199691 139865472532617832039799537)
            ·
              refine ⟨104899104399463374029849653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139865472532617832039799537 104899104399463374029849653)
              ·
                refine ⟨9834291037449691315298405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104899104399463374029849653 9834291037449691315298405)
                ·
                  refine ⟨1843929569521817121618451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9834291037449691315298405 1843929569521817121618451)
                  ·
                    refine ⟨2765894354282725682427677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1843929569521817121618451 2765894354282725682427677)
                    ·
                      refine ⟨1037210382856022130910379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2765894354282725682427677 1037210382856022130910379)
                      ·
                        rfl

theorem cell23_2019960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 4, 1, 3].length) (baseStart_2019960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2019960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2019960 prefixEnd_2019960 := by exact prefixLift 2019960
  have htrace : WordTrace (prefixWord ++ tailWord_2019960) baseStart_2019960 baseEnd_2019960 := by
    simpa [prefixWord, tailWord_2019960, baseEnd_2019960] using wordTrace_append hprefix tailTrace_2019960
  have hstable : (prefixWord ++ tailWord_2019960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019960).length < 2 ^ (prefixWord ++ tailWord_2019960).sum := by decide
  have hdescent : baseEnd_2019960 < baseStart_2019960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020030 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_2020030 : Nat := 118140960795 + 2020030 * 2 ^ 59
def prefixEnd_2020030 : Nat := 4983230072969 + 3 ^ 40 * 2020030 * 2
def baseEnd_2020030 : Nat := 1037246326501836857035057

theorem tailTrace_2020030 : CollatzResearch.WordTrace tailWord_2020030 prefixEnd_2020030 1037246326501836857035057 := by
  unfold tailWord_2020030
  simp only [CollatzResearch.WordTrace]
  refine ⟨9209568358972972312845193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49117697914522519001841029 9209568358972972312845193)
  ·
    refine ⟨6907176269229729234633895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9209568358972972312845193 6907176269229729234633895)
    ·
      refine ⟨10360764403844593851950843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6907176269229729234633895 10360764403844593851950843)
      ·
        refine ⟨15541146605766890777926265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10360764403844593851950843 15541146605766890777926265)
        ·
          refine ⟨11655859954325168083444699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15541146605766890777926265 11655859954325168083444699)
          ·
            refine ⟨17483789931487752125167049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11655859954325168083444699 17483789931487752125167049)
            ·
              refine ⟨13112842448615814093875287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17483789931487752125167049 13112842448615814093875287)
              ·
                refine ⟨19669263672923721140812931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13112842448615814093875287 19669263672923721140812931)
                ·
                  refine ⟨29503895509385581711219397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19669263672923721140812931 29503895509385581711219397)
                  ·
                    refine ⟨5531980408009796570853637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29503895509385581711219397 5531980408009796570853637)
                    ·
                      refine ⟨1037246326501836857035057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5531980408009796570853637 1037246326501836857035057)
                      ·
                        rfl

theorem cell23_2020030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_2020030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020030 prefixEnd_2020030 := by exact prefixLift 2020030
  have htrace : WordTrace (prefixWord ++ tailWord_2020030) baseStart_2020030 baseEnd_2020030 := by
    simpa [prefixWord, tailWord_2020030, baseEnd_2020030] using wordTrace_append hprefix tailTrace_2020030
  have hstable : (prefixWord ++ tailWord_2020030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020030).length < 2 ^ (prefixWord ++ tailWord_2020030).sum := by decide
  have hdescent : baseEnd_2020030 < baseStart_2020030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020038 : List Nat := [6, 1, 2, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_2020038 : Nat := 118140960795 + 2020038 * 2 ^ 59
def prefixEnd_2020038 : Nat := 4983230072969 + 3 ^ 40 * 2020038 * 2
def baseEnd_2020038 : Nat := 1037250434347072825735021

theorem tailTrace_2020038 : CollatzResearch.WordTrace tailWord_2020038 prefixEnd_2020038 1037250434347072825735021 := by
  unfold tailWord_2020038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2302401207992337370907899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49117892437169863912701845 2302401207992337370907899)
  ·
    refine ⟨3453601811988506056361849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2302401207992337370907899 3453601811988506056361849)
    ·
      refine ⟨2590201358991379542271387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3453601811988506056361849 2590201358991379542271387)
      ·
        refine ⟨3885302038487069313407081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2590201358991379542271387 3885302038487069313407081)
        ·
          refine ⟨2913976528865301985055311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3885302038487069313407081 2913976528865301985055311)
          ·
            refine ⟨4370964793297952977582967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2913976528865301985055311 4370964793297952977582967)
            ·
              refine ⟨6556447189946929466374451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4370964793297952977582967 6556447189946929466374451)
              ·
                refine ⟨9834670784920394199561677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6556447189946929466374451 9834670784920394199561677)
                ·
                  refine ⟨3688001544345147824835629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9834670784920394199561677 3688001544345147824835629)
                  ·
                    refine ⟨1383000579129430434313361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3688001544345147824835629 1383000579129430434313361)
                    ·
                      refine ⟨1037250434347072825735021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1383000579129430434313361 1037250434347072825735021)
                      ·
                        rfl

theorem cell23_2020038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_2020038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020038 prefixEnd_2020038 := by exact prefixLift 2020038
  have htrace : WordTrace (prefixWord ++ tailWord_2020038) baseStart_2020038 baseEnd_2020038 := by
    simpa [prefixWord, tailWord_2020038, baseEnd_2020038] using wordTrace_append hprefix tailTrace_2020038
  have hstable : (prefixWord ++ tailWord_2020038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020038).length < 2 ^ (prefixWord ++ tailWord_2020038).sum := by decide
  have hdescent : baseEnd_2020038 < baseStart_2020038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020077 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 1, 7, 2]
def baseStart_2020077 : Nat := 118140960795 + 2020077 * 2 ^ 59
def prefixEnd_2020077 : Nat := 4983230072969 + 3 ^ 40 * 2020077 * 2
def baseEnd_2020077 : Nat := 1037270460092598173147341

theorem tailTrace_2020077 : CollatzResearch.WordTrace tailWord_2020077 prefixEnd_2020077 1037270460092598173147341 := by
  unfold tailWord_2020077
  simp only [CollatzResearch.WordTrace]
  refine ⟨73678261102613505529722485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49118840735075670353148323 73678261102613505529722485)
  ·
    refine ⟨6907336978370016143411483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73678261102613505529722485 6907336978370016143411483)
    ·
      refine ⟨10361005467555024215117225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6907336978370016143411483 10361005467555024215117225)
      ·
        refine ⟨7770754100666268161337919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10361005467555024215117225 7770754100666268161337919)
        ·
          refine ⟨11656131150999402242006879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7770754100666268161337919 11656131150999402242006879)
          ·
            refine ⟨17484196726499103363010319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11656131150999402242006879 17484196726499103363010319)
            ·
              refine ⟨26226295089748655044515479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17484196726499103363010319 26226295089748655044515479)
              ·
                refine ⟨39339442634622982566773219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26226295089748655044515479 39339442634622982566773219)
                ·
                  refine ⟨59009163951934473850159829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39339442634622982566773219 59009163951934473850159829)
                  ·
                    refine ⟨1383027280123464230863121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59009163951934473850159829 1383027280123464230863121)
                    ·
                      refine ⟨1037270460092598173147341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1383027280123464230863121 1037270460092598173147341)
                      ·
                        rfl

theorem cell23_2020077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_2020077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020077 prefixEnd_2020077 := by exact prefixLift 2020077
  have htrace : WordTrace (prefixWord ++ tailWord_2020077) baseStart_2020077 baseEnd_2020077 := by
    simpa [prefixWord, tailWord_2020077, baseEnd_2020077] using wordTrace_append hprefix tailTrace_2020077
  have hstable : (prefixWord ++ tailWord_2020077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020077).length < 2 ^ (prefixWord ++ tailWord_2020077).sum := by decide
  have hdescent : baseEnd_2020077 < baseStart_2020077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020083 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 2, 8]
def baseStart_2020083 : Nat := 118140960795 + 2020083 * 2 ^ 59
def prefixEnd_2020083 : Nat := 4983230072969 + 3 ^ 40 * 2020083 * 2
def baseEnd_2020083 : Nat := 345757846992175049890771

theorem tailTrace_2020083 : CollatzResearch.WordTrace tailWord_2020083 prefixEnd_2020083 345757846992175049890771 := by
  unfold tailWord_2020083
  simp only [CollatzResearch.WordTrace]
  refine ⟨73678479940591768554440903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49118986627061179036293935 73678479940591768554440903)
  ·
    refine ⟨110517719910887652831661355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73678479940591768554440903 110517719910887652831661355)
    ·
      refine ⟨165776579866331479247492033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110517719910887652831661355 165776579866331479247492033)
      ·
        refine ⟨124332434899748609435619025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165776579866331479247492033 124332434899748609435619025)
        ·
          refine ⟨93249326174811457076714269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124332434899748609435619025 93249326174811457076714269)
          ·
            refine ⟨34968497315554296403767851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93249326174811457076714269 34968497315554296403767851)
            ·
              refine ⟨52452745973331444605651777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34968497315554296403767851 52452745973331444605651777)
              ·
                refine ⟨39339559479998583454238833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52452745973331444605651777 39339559479998583454238833)
                ·
                  refine ⟨29504669609998937590679125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39339559479998583454238833 29504669609998937590679125)
                  ·
                    refine ⟨345757846992175049890771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29504669609998937590679125 345757846992175049890771)
                    ·
                      rfl

theorem cell23_2020083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 8].length) (baseStart_2020083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020083 prefixEnd_2020083 := by exact prefixLift 2020083
  have htrace : WordTrace (prefixWord ++ tailWord_2020083) baseStart_2020083 baseEnd_2020083 := by
    simpa [prefixWord, tailWord_2020083, baseEnd_2020083] using wordTrace_append hprefix tailTrace_2020083
  have hstable : (prefixWord ++ tailWord_2020083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020083).length < 2 ^ (prefixWord ++ tailWord_2020083).sum := by decide
  have hdescent : baseEnd_2020083 < baseStart_2020083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020090 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4]
def baseStart_2020090 : Nat := 118140960795 + 2020090 * 2 ^ 59
def prefixEnd_2020090 : Nat := 4983230072969 + 3 ^ 40 * 2020090 * 2
def baseEnd_2020090 : Nat := 1037277135341106622284781

theorem tailTrace_2020090 : CollatzResearch.WordTrace tailWord_2020090 prefixEnd_2020090 1037277135341106622284781 := by
  unfold tailWord_2020090
  simp only [CollatzResearch.WordTrace]
  refine ⟨18419683812891602187486431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49119156834377605833297149 18419683812891602187486431)
  ·
    refine ⟨27629525719337403281229647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18419683812891602187486431 27629525719337403281229647)
    ·
      refine ⟨41444288579006104921844471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27629525719337403281229647 41444288579006104921844471)
      ·
        refine ⟨62166432868509157382766707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41444288579006104921844471 62166432868509157382766707)
        ·
          refine ⟨93249649302763736074150061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62166432868509157382766707 93249649302763736074150061)
          ·
            refine ⟨34968618488536401027806273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93249649302763736074150061 34968618488536401027806273)
            ·
              refine ⟨26226463866402300770854705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34968618488536401027806273 26226463866402300770854705)
              ·
                refine ⟨19669847899801725578141029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26226463866402300770854705 19669847899801725578141029)
                ·
                  refine ⟨3688096481212823545901443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19669847899801725578141029 3688096481212823545901443)
                  ·
                    refine ⟨5532144721819235318852165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3688096481212823545901443 5532144721819235318852165)
                    ·
                      refine ⟨1037277135341106622284781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5532144721819235318852165 1037277135341106622284781)
                      ·
                        rfl

theorem cell23_2020090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_2020090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020090 prefixEnd_2020090 := by exact prefixLift 2020090
  have htrace : WordTrace (prefixWord ++ tailWord_2020090) baseStart_2020090 baseEnd_2020090 := by
    simpa [prefixWord, tailWord_2020090, baseEnd_2020090] using wordTrace_append hprefix tailTrace_2020090
  have hstable : (prefixWord ++ tailWord_2020090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020090).length < 2 ^ (prefixWord ++ tailWord_2020090).sum := by decide
  have hdescent : baseEnd_2020090 < baseStart_2020090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020160 : List Nat := [2, 1, 1, 2, 2, 1, 1, 5, 3, 5]
def baseStart_2020160 : Nat := 118140960795 + 2020160 * 2 ^ 59
def prefixEnd_2020160 : Nat := 4983230072969 + 3 ^ 40 * 2020160 * 2
def baseEnd_2020160 : Nat := 345771026328973782803153

theorem tailTrace_2020160 : CollatzResearch.WordTrace tailWord_2020160 prefixEnd_2020160 345771026328973782803153 := by
  unfold tailWord_2020160
  simp only [CollatzResearch.WordTrace]
  refine ⟨36840644180656405352496967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49120858907541873803329289 36840644180656405352496967)
  ·
    refine ⟨55260966270984608028745451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36840644180656405352496967 55260966270984608028745451)
    ·
      refine ⟨82891449406476912043118177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55260966270984608028745451 82891449406476912043118177)
      ·
        refine ⟨62168587054857684032338633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82891449406476912043118177 62168587054857684032338633)
        ·
          refine ⟨46626440291143263024253975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62168587054857684032338633 46626440291143263024253975)
          ·
            refine ⟨69939660436714894536380963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46626440291143263024253975 69939660436714894536380963)
            ·
              refine ⟨104909490655072341804571445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69939660436714894536380963 104909490655072341804571445)
              ·
                refine ⟨9835264748913032044178573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104909490655072341804571445 9835264748913032044178573)
                ·
                  refine ⟨3688224280842387016566965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9835264748913032044178573 3688224280842387016566965)
                  ·
                    refine ⟨345771026328973782803153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3688224280842387016566965 345771026328973782803153)
                    ·
                      rfl

theorem cell23_2020160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 3, 5].length) (baseStart_2020160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020160 prefixEnd_2020160 := by exact prefixLift 2020160
  have htrace : WordTrace (prefixWord ++ tailWord_2020160) baseStart_2020160 baseEnd_2020160 := by
    simpa [prefixWord, tailWord_2020160, baseEnd_2020160] using wordTrace_append hprefix tailTrace_2020160
  have hstable : (prefixWord ++ tailWord_2020160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020160).length < 2 ^ (prefixWord ++ tailWord_2020160).sum := by decide
  have hdescent : baseEnd_2020160 < baseStart_2020160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020227 : List Nat := [1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 4]
def baseStart_2020227 : Nat := 118140960795 + 2020227 * 2 ^ 59
def prefixEnd_2020227 : Nat := 4983230072969 + 3 ^ 40 * 2020227 * 2
def baseEnd_2020227 : Nat := 1037347482190772586271651

theorem tailTrace_2020227 : CollatzResearch.WordTrace tailWord_2020227 prefixEnd_2020227 1037347482190772586271651 := by
  unfold tailWord_2020227
  simp only [CollatzResearch.WordTrace]
  refine ⟨73683732052070081147682935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49122488034713387431788623 73683732052070081147682935)
  ·
    refine ⟨110525598078105121721524403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73683732052070081147682935 110525598078105121721524403)
    ·
      refine ⟨165788397117157682582286605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110525598078105121721524403 165788397117157682582286605)
      ·
        refine ⟨62170648918934130968357477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165788397117157682582286605 62170648918934130968357477)
        ·
          refine ⟨11656996672300149556567027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62170648918934130968357477 11656996672300149556567027)
          ·
            refine ⟨17485495008450224334850541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11656996672300149556567027 17485495008450224334850541)
            ·
              refine ⟨6557060628168834125568953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17485495008450224334850541 6557060628168834125568953)
              ·
                refine ⟨4917795471126625594176715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6557060628168834125568953 4917795471126625594176715)
                ·
                  refine ⟨7376693206689938391265073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4917795471126625594176715 7376693206689938391265073)
                  ·
                    refine ⟨5532519905017453793448805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7376693206689938391265073 5532519905017453793448805)
                    ·
                      refine ⟨1037347482190772586271651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5532519905017453793448805 1037347482190772586271651)
                      ·
                        rfl

theorem cell23_2020227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_2020227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020227 prefixEnd_2020227 := by exact prefixLift 2020227
  have htrace : WordTrace (prefixWord ++ tailWord_2020227) baseStart_2020227 baseEnd_2020227 := by
    simpa [prefixWord, tailWord_2020227, baseEnd_2020227] using wordTrace_append hprefix tailTrace_2020227
  have hstable : (prefixWord ++ tailWord_2020227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020227).length < 2 ^ (prefixWord ++ tailWord_2020227).sum := by decide
  have hdescent : baseEnd_2020227 < baseStart_2020227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020231 : List Nat := [1, 1, 4, 2, 3, 2, 3, 1, 1, 1, 4]
def baseStart_2020231 : Nat := 118140960795 + 2020231 * 2 ^ 59
def prefixEnd_2020231 : Nat := 4983230072969 + 3 ^ 40 * 2020231 * 2
def baseEnd_2020231 : Nat := 1037349536113390570621633

theorem tailTrace_2020231 : CollatzResearch.WordTrace tailWord_2020231 prefixEnd_2020231 1037349536113390570621633 := by
  unfold tailWord_2020231
  simp only [CollatzResearch.WordTrace]
  refine ⟨73683877944055589830828547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49122585296037059887219031 73683877944055589830828547)
  ·
    refine ⟨110525816916083384746242821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73683877944055589830828547 110525816916083384746242821)
    ·
      refine ⟨20723590671765634639920529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110525816916083384746242821 20723590671765634639920529)
      ·
        refine ⟨15542693003824225979940397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20723590671765634639920529 15542693003824225979940397)
        ·
          refine ⟨5828509876434084742477649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15542693003824225979940397 5828509876434084742477649)
          ·
            refine ⟨4371382407325563556858237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5828509876434084742477649 4371382407325563556858237)
            ·
              refine ⟨1639268402747086333821839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4371382407325563556858237 1639268402747086333821839)
              ·
                refine ⟨2458902604120629500732759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1639268402747086333821839 2458902604120629500732759)
                ·
                  refine ⟨3688353906180944251099139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2458902604120629500732759 3688353906180944251099139)
                  ·
                    refine ⟨5532530859271416376648709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3688353906180944251099139 5532530859271416376648709)
                    ·
                      refine ⟨1037349536113390570621633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5532530859271416376648709 1037349536113390570621633)
                      ·
                        rfl

theorem cell23_2020231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_2020231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020231 prefixEnd_2020231 := by exact prefixLift 2020231
  have htrace : WordTrace (prefixWord ++ tailWord_2020231) baseStart_2020231 baseEnd_2020231 := by
    simpa [prefixWord, tailWord_2020231, baseEnd_2020231] using wordTrace_append hprefix tailTrace_2020231
  have hstable : (prefixWord ++ tailWord_2020231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020231).length < 2 ^ (prefixWord ++ tailWord_2020231).sum := by decide
  have hdescent : baseEnd_2020231 < baseStart_2020231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020234 : List Nat := [3, 1, 2, 4, 1, 1, 3, 1, 1, 1, 5]
def baseStart_2020234 : Nat := 118140960795 + 2020234 * 2 ^ 59
def prefixEnd_2020234 : Nat := 4983230072969 + 3 ^ 40 * 2020234 * 2
def baseEnd_2020234 : Nat := 1037351076555354058884119

theorem tailTrace_2020234 : CollatzResearch.WordTrace tailWord_2020234 prefixEnd_2020234 1037351076555354058884119 := by
  unfold tailWord_2020234
  simp only [CollatzResearch.WordTrace]
  refine ⟨18420996840761180335796939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49122658242029814228791837 18420996840761180335796939)
  ·
    refine ⟨27631495261141770503695409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18420996840761180335796939 27631495261141770503695409)
    ·
      refine ⟨20723621445856327877771557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27631495261141770503695409 20723621445856327877771557)
      ·
        refine ⟨3885679021098061477082167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20723621445856327877771557 3885679021098061477082167)
        ·
          refine ⟨5828518531647092215623251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3885679021098061477082167 5828518531647092215623251)
          ·
            refine ⟨8742777797470638323434877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5828518531647092215623251 8742777797470638323434877)
            ·
              refine ⟨3278541674051489371288079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8742777797470638323434877 3278541674051489371288079)
              ·
                refine ⟨4917812511077234056932119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3278541674051489371288079 4917812511077234056932119)
                ·
                  refine ⟨7376718766615851085398179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4917812511077234056932119 7376718766615851085398179)
                  ·
                    refine ⟨11065078149923776628097269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7376718766615851085398179 11065078149923776628097269)
                    ·
                      refine ⟨1037351076555354058884119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11065078149923776628097269 1037351076555354058884119)
                      ·
                        rfl

theorem cell23_2020234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_2020234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020234 prefixEnd_2020234 := by exact prefixLift 2020234
  have htrace : WordTrace (prefixWord ++ tailWord_2020234) baseStart_2020234 baseEnd_2020234 := by
    simpa [prefixWord, tailWord_2020234, baseEnd_2020234] using wordTrace_append hprefix tailTrace_2020234
  have hstable : (prefixWord ++ tailWord_2020234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020234).length < 2 ^ (prefixWord ++ tailWord_2020234).sum := by decide
  have hdescent : baseEnd_2020234 < baseStart_2020234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020242 : List Nat := [3, 2, 3, 2, 2, 2, 2, 2, 1, 1, 3]
def baseStart_2020242 : Nat := 118140960795 + 2020242 * 2 ^ 59
def prefixEnd_2020242 : Nat := 4983230072969 + 3 ^ 40 * 2020242 * 2
def baseEnd_2020242 : Nat := 1037355184400590027584083

theorem tailTrace_2020242 : CollatzResearch.WordTrace tailWord_2020242 prefixEnd_2020242 1037355184400590027584083 := by
  unfold tailWord_2020242
  simp only [CollatzResearch.WordTrace]
  refine ⟨18421069786753934677369745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49122852764677159139652653 18421069786753934677369745)
  ·
    refine ⟨13815802340065451008027309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18421069786753934677369745 13815802340065451008027309)
    ·
      refine ⟨5180925877524544128010241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13815802340065451008027309 5180925877524544128010241)
      ·
        refine ⟨3885694408143408096007681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5180925877524544128010241 3885694408143408096007681)
        ·
          refine ⟨2914270806107556072005761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3885694408143408096007681 2914270806107556072005761)
          ·
            refine ⟨2185703104580667054004321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2914270806107556072005761 2185703104580667054004321)
            ·
              refine ⟨1639277328435500290503241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2185703104580667054004321 1639277328435500290503241)
              ·
                refine ⟨1229457996326625217877431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1639277328435500290503241 1229457996326625217877431)
                ·
                  refine ⟨1844186994489937826816147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1229457996326625217877431 1844186994489937826816147)
                  ·
                    refine ⟨2766280491734906740224221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1844186994489937826816147 2766280491734906740224221)
                    ·
                      refine ⟨1037355184400590027584083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2766280491734906740224221 1037355184400590027584083)
                      ·
                        rfl

theorem cell23_2020242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_2020242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020242 prefixEnd_2020242 := by exact prefixLift 2020242
  have htrace : WordTrace (prefixWord ++ tailWord_2020242) baseStart_2020242 baseEnd_2020242 := by
    simpa [prefixWord, tailWord_2020242, baseEnd_2020242] using wordTrace_append hprefix tailTrace_2020242
  have hstable : (prefixWord ++ tailWord_2020242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020242).length < 2 ^ (prefixWord ++ tailWord_2020242).sum := by decide
  have hdescent : baseEnd_2020242 < baseStart_2020242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020247 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 3]
def baseStart_2020247 : Nat := 118140960795 + 2020247 * 2 ^ 59
def prefixEnd_2020247 : Nat := 4983230072969 + 3 ^ 40 * 2020247 * 2
def baseEnd_2020247 : Nat := 1037357751803862508021559

theorem tailTrace_2020247 : CollatzResearch.WordTrace tailWord_2020247 prefixEnd_2020247 1037357751803862508021559 := by
  unfold tailWord_2020247
  simp only [CollatzResearch.WordTrace]
  refine ⟨73684461511997624563410995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49122974341331749708940663 73684461511997624563410995)
  ·
    refine ⟨110526692267996436845116493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73684461511997624563410995 110526692267996436845116493)
    ·
      refine ⟨41447509600498663816918685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110526692267996436845116493 41447509600498663816918685)
      ·
        refine ⟨15542816100186998931344507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41447509600498663816918685 15542816100186998931344507)
        ·
          refine ⟨23314224150280498397016761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15542816100186998931344507 23314224150280498397016761)
          ·
            refine ⟨17485668112710373797762571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23314224150280498397016761 17485668112710373797762571)
            ·
              refine ⟨26228502169065560696643857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17485668112710373797762571 26228502169065560696643857)
              ·
                refine ⟨19671376626799170522482893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26228502169065560696643857 19671376626799170522482893)
                ·
                  refine ⟨7376766235049688945931085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19671376626799170522482893 7376766235049688945931085)
                  ·
                    refine ⟨2766287338143633354724157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7376766235049688945931085 2766287338143633354724157)
                    ·
                      refine ⟨1037357751803862508021559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2766287338143633354724157 1037357751803862508021559)
                      ·
                        rfl

theorem cell23_2020247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_2020247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020247 prefixEnd_2020247 := by exact prefixLift 2020247
  have htrace : WordTrace (prefixWord ++ tailWord_2020247) baseStart_2020247 baseEnd_2020247 := by
    simpa [prefixWord, tailWord_2020247, baseEnd_2020247] using wordTrace_append hprefix tailTrace_2020247
  have hstable : (prefixWord ++ tailWord_2020247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020247).length < 2 ^ (prefixWord ++ tailWord_2020247).sum := by decide
  have hdescent : baseEnd_2020247 < baseStart_2020247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020277 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_2020277 : Nat := 118140960795 + 2020277 * 2 ^ 59
def prefixEnd_2020277 : Nat := 4983230072969 + 3 ^ 40 * 2020277 * 2
def baseEnd_2020277 : Nat := 1037373156223497390646421

theorem tailTrace_2020277 : CollatzResearch.WordTrace tailWord_2020277 prefixEnd_2020277 1037373156223497390646421 := by
  unfold tailWord_2020277
  simp only [CollatzResearch.WordTrace]
  refine ⟨73685555701888939687003085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49123703801259293124668723 73685555701888939687003085)
  ·
    refine ⟨27632083388208352382626157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73685555701888939687003085 27632083388208352382626157)
    ·
      refine ⟨10362031270578132143484809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27632083388208352382626157 10362031270578132143484809)
      ·
        refine ⟨7771523452933599107613607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10362031270578132143484809 7771523452933599107613607)
        ·
          refine ⟨11657285179400398661420411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7771523452933599107613607 11657285179400398661420411)
          ·
            refine ⟨17485927769100597992130617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11657285179400398661420411 17485927769100597992130617)
            ·
              refine ⟨13114445826825448494097963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17485927769100597992130617 13114445826825448494097963)
              ·
                refine ⟨19671668740238172741146945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13114445826825448494097963 19671668740238172741146945)
                ·
                  refine ⟨14753751555178629555860209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19671668740238172741146945 14753751555178629555860209)
                  ·
                    refine ⟨11065313666383972166895157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14753751555178629555860209 11065313666383972166895157)
                    ·
                      refine ⟨1037373156223497390646421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11065313666383972166895157 1037373156223497390646421)
                      ·
                        rfl

theorem cell23_2020277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_2020277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020277 prefixEnd_2020277 := by exact prefixLift 2020277
  have htrace : WordTrace (prefixWord ++ tailWord_2020277) baseStart_2020277 baseEnd_2020277 := by
    simpa [prefixWord, tailWord_2020277, baseEnd_2020277] using wordTrace_append hprefix tailTrace_2020277
  have hstable : (prefixWord ++ tailWord_2020277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020277).length < 2 ^ (prefixWord ++ tailWord_2020277).sum := by decide
  have hdescent : baseEnd_2020277 < baseStart_2020277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020285 : List Nat := [1, 4, 1, 2, 5, 1, 2, 1, 1, 2, 3]
def baseStart_2020285 : Nat := 118140960795 + 2020285 * 2 ^ 59
def prefixEnd_2020285 : Nat := 4983230072969 + 3 ^ 40 * 2020285 * 2
def baseEnd_2020285 : Nat := 1037377264068733359346385

theorem tailTrace_2020285 : CollatzResearch.WordTrace tailWord_2020285 prefixEnd_2020285 1037377264068733359346385 := by
  unfold tailWord_2020285
  simp only [CollatzResearch.WordTrace]
  refine ⟨73685847485859957053294309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49123898323906638035529539 73685847485859957053294309)
  ·
    refine ⟨13816096403598741947492683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73685847485859957053294309 13816096403598741947492683)
    ·
      refine ⟨20724144605398112921239025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13816096403598741947492683 20724144605398112921239025)
      ·
        refine ⟨15543108454048584690929269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20724144605398112921239025 15543108454048584690929269)
        ·
          refine ⟨1457166417567054814774619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15543108454048584690929269 1457166417567054814774619)
          ·
            refine ⟨2185749626350582222161929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1457166417567054814774619 2185749626350582222161929)
            ·
              refine ⟨1639312219762936666621447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2185749626350582222161929 1639312219762936666621447)
              ·
                refine ⟨2458968329644404999932171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1639312219762936666621447 2458968329644404999932171)
                ·
                  refine ⟨3688452494466607499898257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2458968329644404999932171 3688452494466607499898257)
                  ·
                    refine ⟨2766339370849955624923693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3688452494466607499898257 2766339370849955624923693)
                    ·
                      refine ⟨1037377264068733359346385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2766339370849955624923693 1037377264068733359346385)
                      ·
                        rfl

theorem cell23_2020285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_2020285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020285 prefixEnd_2020285 := by exact prefixLift 2020285
  have htrace : WordTrace (prefixWord ++ tailWord_2020285) baseStart_2020285 baseEnd_2020285 := by
    simpa [prefixWord, tailWord_2020285, baseEnd_2020285] using wordTrace_append hprefix tailTrace_2020285
  have hstable : (prefixWord ++ tailWord_2020285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020285).length < 2 ^ (prefixWord ++ tailWord_2020285).sum := by decide
  have hdescent : baseEnd_2020285 < baseStart_2020285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020325 : List Nat := [1, 3, 1, 6, 1, 1, 2, 2, 1, 3, 2]
def baseStart_2020325 : Nat := 118140960795 + 2020325 * 2 ^ 59
def prefixEnd_2020325 : Nat := 4983230072969 + 3 ^ 40 * 2020325 * 2
def baseEnd_2020325 : Nat := 1037397803294913202846201

theorem tailTrace_2020325 : CollatzResearch.WordTrace tailWord_2020325 prefixEnd_2020325 1037397803294913202846201 := by
  unfold tailWord_2020325
  simp only [CollatzResearch.WordTrace]
  refine ⟨73687306405715043884750429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49124870937143362589833619 73687306405715043884750429)
  ·
    refine ⟨27632739902143141456781411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73687306405715043884750429 27632739902143141456781411)
    ·
      refine ⟨41449109853214712185172117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27632739902143141456781411 41449109853214712185172117)
      ·
        refine ⟨1942927024369439633679943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41449109853214712185172117 1942927024369439633679943)
        ·
          refine ⟨2914390536554159450519915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1942927024369439633679943 2914390536554159450519915)
          ·
            refine ⟨4371585804831239175779873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2914390536554159450519915 4371585804831239175779873)
            ·
              refine ⟨3278689353623429381834905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4371585804831239175779873 3278689353623429381834905)
              ·
                refine ⟨2459017015217572036376179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3278689353623429381834905 2459017015217572036376179)
                ·
                  refine ⟨3688525522826358054564269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2459017015217572036376179 3688525522826358054564269)
                  ·
                    refine ⟨1383197071059884270461601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3688525522826358054564269 1383197071059884270461601)
                    ·
                      refine ⟨1037397803294913202846201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1383197071059884270461601 1037397803294913202846201)
                      ·
                        rfl

theorem cell23_2020325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_2020325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020325 prefixEnd_2020325 := by exact prefixLift 2020325
  have htrace : WordTrace (prefixWord ++ tailWord_2020325) baseStart_2020325 baseEnd_2020325 := by
    simpa [prefixWord, tailWord_2020325, baseEnd_2020325] using wordTrace_append hprefix tailTrace_2020325
  have hstable : (prefixWord ++ tailWord_2020325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020325).length < 2 ^ (prefixWord ++ tailWord_2020325).sum := by decide
  have hdescent : baseEnd_2020325 < baseStart_2020325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020377 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 3, 3, 4]
def baseStart_2020377 : Nat := 118140960795 + 2020377 * 2 ^ 59
def prefixEnd_2020377 : Nat := 4983230072969 + 3 ^ 40 * 2020377 * 2
def baseEnd_2020377 : Nat := 1037424504288946999395961

theorem tailTrace_2020377 : CollatzResearch.WordTrace tailWord_2020377 prefixEnd_2020377 1037424504288946999395961 := by
  unfold tailWord_2020377
  simp only [CollatzResearch.WordTrace]
  refine ⟨73689203001526656765643385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49126135334351104510428923 73689203001526656765643385)
  ·
    refine ⟨55266902251144992574232539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73689203001526656765643385 55266902251144992574232539)
    ·
      refine ⟨82900353376717488861348809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55266902251144992574232539 82900353376717488861348809)
      ·
        refine ⟨62175265032538116646011607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82900353376717488861348809 62175265032538116646011607)
        ·
          refine ⟨93262897548807174969017411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62175265032538116646011607 93262897548807174969017411)
          ·
            refine ⟨139894346323210762453526117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93262897548807174969017411 139894346323210762453526117)
            ·
              refine ⟨26230189935602017960036147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139894346323210762453526117 26230189935602017960036147)
              ·
                refine ⟨39345284903403026940054221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26230189935602017960036147 39345284903403026940054221)
                ·
                  refine ⟨14754481838776135102520333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39345284903403026940054221 14754481838776135102520333)
                  ·
                    refine ⟨5532930689541050663445125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14754481838776135102520333 5532930689541050663445125)
                    ·
                      refine ⟨1037424504288946999395961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5532930689541050663445125 1037424504288946999395961)
                      ·
                        rfl

theorem cell23_2020377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_2020377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020377 prefixEnd_2020377 := by exact prefixLift 2020377
  have htrace : WordTrace (prefixWord ++ tailWord_2020377) baseStart_2020377 baseEnd_2020377 := by
    simpa [prefixWord, tailWord_2020377, baseEnd_2020377] using wordTrace_append hprefix tailTrace_2020377
  have hstable : (prefixWord ++ tailWord_2020377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020377).length < 2 ^ (prefixWord ++ tailWord_2020377).sum := by decide
  have hdescent : baseEnd_2020377 < baseStart_2020377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020391 : List Nat := [1, 1, 7, 1, 1, 1, 1, 3, 2, 5]
def baseStart_2020391 : Nat := 118140960795 + 2020391 * 2 ^ 59
def prefixEnd_2020391 : Nat := 4983230072969 + 3 ^ 40 * 2020391 * 2
def baseEnd_2020391 : Nat := 345810564339369981540299

theorem tailTrace_2020391 : CollatzResearch.WordTrace tailWord_2020391 prefixEnd_2020391 345810564339369981540299 := by
  unfold tailWord_2020391
  simp only [CollatzResearch.WordTrace]
  refine ⟨73689713623475937156653027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49126475748983958104435351 73689713623475937156653027)
  ·
    refine ⟨110534570435213905734979541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73689713623475937156653027 110534570435213905734979541)
    ·
      refine ⟨2590653994575325915663583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 110534570435213905734979541 2590653994575325915663583)
      ·
        refine ⟨3885980991862988873495375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2590653994575325915663583 3885980991862988873495375)
        ·
          refine ⟨5828971487794483310243063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3885980991862988873495375 5828971487794483310243063)
          ·
            refine ⟨8743457231691724965364595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5828971487794483310243063 8743457231691724965364595)
            ·
              refine ⟨13115185847537587448046893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8743457231691724965364595 13115185847537587448046893)
              ·
                refine ⟨4918194692826595293017585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13115185847537587448046893 4918194692826595293017585)
                ·
                  refine ⟨3688646019619946469763189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4918194692826595293017585 3688646019619946469763189)
                  ·
                    refine ⟨345810564339369981540299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3688646019619946469763189 345810564339369981540299)
                    ·
                      rfl

theorem cell23_2020391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_2020391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020391 prefixEnd_2020391 := by exact prefixLift 2020391
  have htrace : WordTrace (prefixWord ++ tailWord_2020391) baseStart_2020391 baseEnd_2020391 := by
    simpa [prefixWord, tailWord_2020391, baseEnd_2020391] using wordTrace_append hprefix tailTrace_2020391
  have hstable : (prefixWord ++ tailWord_2020391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020391).length < 2 ^ (prefixWord ++ tailWord_2020391).sum := by decide
  have hdescent : baseEnd_2020391 < baseStart_2020391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020407 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 6]
def baseStart_2020407 : Nat := 118140960795 + 2020407 * 2 ^ 59
def prefixEnd_2020407 : Nat := 4983230072969 + 3 ^ 40 * 2020407 * 2
def baseEnd_2020407 : Nat := 1037439908708581882020823

theorem tailTrace_2020407 : CollatzResearch.WordTrace tailWord_2020407 prefixEnd_2020407 1037439908708581882020823 := by
  unfold tailWord_2020407
  simp only [CollatzResearch.WordTrace]
  refine ⟨73690297191417971889235475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49126864794278647926156983 73690297191417971889235475)
  ·
    refine ⟨110535445787126957833853213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73690297191417971889235475 110535445787126957833853213)
    ·
      refine ⟨41450792170172609187694955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110535445787126957833853213 41450792170172609187694955)
      ·
        refine ⟨62176188255258913781542433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41450792170172609187694955 62176188255258913781542433)
        ·
          refine ⟨46632141191444185336156825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62176188255258913781542433 46632141191444185336156825)
          ·
            refine ⟨34974105893583139002117619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46632141191444185336156825 34974105893583139002117619)
            ·
              refine ⟨52461158840374708503176429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34974105893583139002117619 52461158840374708503176429)
              ·
                refine ⟨19672934565140515688691161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52461158840374708503176429 19672934565140515688691161)
                ·
                  refine ⟨14754700923855386766518371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19672934565140515688691161 14754700923855386766518371)
                  ·
                    refine ⟨22132051385783080149777557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14754700923855386766518371 22132051385783080149777557)
                    ·
                      refine ⟨1037439908708581882020823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22132051385783080149777557 1037439908708581882020823)
                      ·
                        rfl

theorem cell23_2020407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_2020407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020407 prefixEnd_2020407 := by exact prefixLift 2020407
  have htrace : WordTrace (prefixWord ++ tailWord_2020407) baseStart_2020407 baseEnd_2020407 := by
    simpa [prefixWord, tailWord_2020407, baseEnd_2020407] using wordTrace_append hprefix tailTrace_2020407
  have hstable : (prefixWord ++ tailWord_2020407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020407).length < 2 ^ (prefixWord ++ tailWord_2020407).sum := by decide
  have hdescent : baseEnd_2020407 < baseStart_2020407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020445 : List Nat := [1, 4, 4, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_2020445 : Nat := 118140960795 + 2020445 * 2 ^ 59
def prefixEnd_2020445 : Nat := 4983230072969 + 3 ^ 40 * 2020445 * 2
def baseEnd_2020445 : Nat := 1037459420973452733345649

theorem tailTrace_2020445 : CollatzResearch.WordTrace tailWord_2020445 prefixEnd_2020445 1037459420973452733345649 := by
  unfold tailWord_2020445
  simp only [CollatzResearch.WordTrace]
  refine ⟨73691683165280304379118789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49127788776853536252745859 73691683165280304379118789)
  ·
    refine ⟨13817190593490057071084773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73691683165280304379118789 13817190593490057071084773)
    ·
      refine ⟨2590723236279385700828395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13817190593490057071084773 2590723236279385700828395)
      ·
        refine ⟨3886084854419078551242593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2590723236279385700828395 3886084854419078551242593)
        ·
          refine ⟨2914563640814308913431945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3886084854419078551242593 2914563640814308913431945)
          ·
            refine ⟨2185922730610731685073959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2914563640814308913431945 2185922730610731685073959)
            ·
              refine ⟨3278884095916097527610939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2185922730610731685073959 3278884095916097527610939)
              ·
                refine ⟨4918326143874146291416409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3278884095916097527610939 4918326143874146291416409)
                ·
                  refine ⟨3688744607905609718562307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4918326143874146291416409 3688744607905609718562307)
                  ·
                    refine ⟨5533116911858414577843461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3688744607905609718562307 5533116911858414577843461)
                    ·
                      refine ⟨1037459420973452733345649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5533116911858414577843461 1037459420973452733345649)
                      ·
                        rfl

theorem cell23_2020445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_2020445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020445 prefixEnd_2020445 := by exact prefixLift 2020445
  have htrace : WordTrace (prefixWord ++ tailWord_2020445) baseStart_2020445 baseEnd_2020445 := by
    simpa [prefixWord, tailWord_2020445, baseEnd_2020445] using wordTrace_append hprefix tailTrace_2020445
  have hstable : (prefixWord ++ tailWord_2020445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020445).length < 2 ^ (prefixWord ++ tailWord_2020445).sum := by decide
  have hdescent : baseEnd_2020445 < baseStart_2020445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020471 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 4, 3, 2]
def baseStart_2020471 : Nat := 118140960795 + 2020471 * 2 ^ 59
def prefixEnd_2020471 : Nat := 4983230072969 + 3 ^ 40 * 2020471 * 2
def baseEnd_2020471 : Nat := 1037472771470469631620529

theorem tailTrace_2020471 : CollatzResearch.WordTrace tailWord_2020471 prefixEnd_2020471 1037472771470469631620529 := by
  unfold tailWord_2020471
  simp only [CollatzResearch.WordTrace]
  refine ⟨73692631463186110819565267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49128420975457407213043511 73692631463186110819565267)
  ·
    refine ⟨110538947194779166229347901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73692631463186110819565267 110538947194779166229347901)
    ·
      refine ⟨41452105198042187336005463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110538947194779166229347901 41452105198042187336005463)
      ·
        refine ⟨62178157797063281004008195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41452105198042187336005463 62178157797063281004008195)
        ·
          refine ⟨93267236695594921506012293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62178157797063281004008195 93267236695594921506012293)
          ·
            refine ⟨17487606880424047782377305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93267236695594921506012293 17487606880424047782377305)
            ·
              refine ⟨13115705160318035836782979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17487606880424047782377305 13115705160318035836782979)
              ·
                refine ⟨19673557740477053755174469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13115705160318035836782979 19673557740477053755174469)
                ·
                  refine ⟨3688792076339447579095213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19673557740477053755174469 3688792076339447579095213)
                  ·
                    refine ⟨1383297028627292842160705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3688792076339447579095213 1383297028627292842160705)
                    ·
                      refine ⟨1037472771470469631620529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1383297028627292842160705 1037472771470469631620529)
                      ·
                        rfl

theorem cell23_2020471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 3, 2].length) (baseStart_2020471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020471 prefixEnd_2020471 := by exact prefixLift 2020471
  have htrace : WordTrace (prefixWord ++ tailWord_2020471) baseStart_2020471 baseEnd_2020471 := by
    simpa [prefixWord, tailWord_2020471, baseEnd_2020471] using wordTrace_append hprefix tailTrace_2020471
  have hstable : (prefixWord ++ tailWord_2020471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020471).length < 2 ^ (prefixWord ++ tailWord_2020471).sum := by decide
  have hdescent : baseEnd_2020471 < baseStart_2020471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020498 : List Nat := [3, 2, 3, 1, 1, 3, 2, 2, 1, 5]
def baseStart_2020498 : Nat := 118140960795 + 2020498 * 2 ^ 59
def prefixEnd_2020498 : Nat := 4983230072969 + 3 ^ 40 * 2020498 * 2
def baseEnd_2020498 : Nat := 345828878482713675327635

theorem tailTrace_2020498 : CollatzResearch.WordTrace tailWord_2020498 prefixEnd_2020498 345828878482713675327635 := by
  unfold tailWord_2020498
  simp only [CollatzResearch.WordTrace]
  refine ⟨18423404058522073607699537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49129077489392196287198765 18423404058522073607699537)
  ·
    refine ⟨13817553043891555205774653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18423404058522073607699537 13817553043891555205774653)
    ·
      refine ⟨5181582391459333202165495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13817553043891555205774653 5181582391459333202165495)
      ·
        refine ⟨7772373587188999803248243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5181582391459333202165495 7772373587188999803248243)
        ·
          refine ⟨11658560380783499704872365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7772373587188999803248243 11658560380783499704872365)
          ·
            refine ⟨4371960142793812389327137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11658560380783499704872365 4371960142793812389327137)
            ·
              refine ⟨3278970107095359291995353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4371960142793812389327137 3278970107095359291995353)
              ·
                refine ⟨2459227580321519468996515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3278970107095359291995353 2459227580321519468996515)
                ·
                  refine ⟨3688841370482279203494773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2459227580321519468996515 3688841370482279203494773)
                  ·
                    refine ⟨345828878482713675327635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3688841370482279203494773 345828878482713675327635)
                    ·
                      rfl

theorem cell23_2020498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_2020498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020498 prefixEnd_2020498 := by exact prefixLift 2020498
  have htrace : WordTrace (prefixWord ++ tailWord_2020498) baseStart_2020498 baseEnd_2020498 := by
    simpa [prefixWord, tailWord_2020498, baseEnd_2020498] using wordTrace_append hprefix tailTrace_2020498
  have hstable : (prefixWord ++ tailWord_2020498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020498).length < 2 ^ (prefixWord ++ tailWord_2020498).sum := by decide
  have hdescent : baseEnd_2020498 < baseStart_2020498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020545 : List Nat := [1, 2, 6, 1, 1, 2, 1, 3, 2, 4]
def baseStart_2020545 : Nat := 118140960795 + 2020545 * 2 ^ 59
def prefixEnd_2020545 : Nat := 4983230072969 + 3 ^ 40 * 2020545 * 2
def baseEnd_2020545 : Nat := 345836923012967447365063

theorem tailTrace_2020545 : CollatzResearch.WordTrace tailWord_2020545 prefixEnd_2020545 345836923012967447365063 := by
  unfold tailWord_2020545
  simp only [CollatzResearch.WordTrace]
  refine ⟨73695330464918021457759089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49130220309945347638506059 73695330464918021457759089)
  ·
    refine ⟨55271497848688516093319317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73695330464918021457759089 55271497848688516093319317)
    ·
      refine ⟨2590851461657274191874343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 55271497848688516093319317 2590851461657274191874343)
      ·
        refine ⟨3886277192485911287811515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2590851461657274191874343 3886277192485911287811515)
        ·
          refine ⟨5829415788728866931717273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3886277192485911287811515 5829415788728866931717273)
          ·
            refine ⟨4372061841546650198787955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5829415788728866931717273 4372061841546650198787955)
            ·
              refine ⟨6558092762319975298181933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4372061841546650198787955 6558092762319975298181933)
              ·
                refine ⟨2459284785869990736818225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6558092762319975298181933 2459284785869990736818225)
                ·
                  refine ⟨1844463589402493052613669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2459284785869990736818225 1844463589402493052613669)
                  ·
                    refine ⟨345836923012967447365063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1844463589402493052613669 345836923012967447365063)
                    ·
                      rfl

theorem cell23_2020545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_2020545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020545 prefixEnd_2020545 := by exact prefixLift 2020545
  have htrace : WordTrace (prefixWord ++ tailWord_2020545) baseStart_2020545 baseEnd_2020545 := by
    simpa [prefixWord, tailWord_2020545, baseEnd_2020545] using wordTrace_append hprefix tailTrace_2020545
  have hstable : (prefixWord ++ tailWord_2020545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020545).length < 2 ^ (prefixWord ++ tailWord_2020545).sum := by decide
  have hdescent : baseEnd_2020545 < baseStart_2020545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020568 : List Nat := [2, 1, 2, 2, 5, 1, 1, 2, 1, 3, 3]
def baseStart_2020568 : Nat := 118140960795 + 2020568 * 2 ^ 59
def prefixEnd_2020568 : Nat := 4983230072969 + 3 ^ 40 * 2020568 * 2
def baseEnd_2020568 : Nat := 1037522579093955752107583

theorem tailTrace_2020568 : CollatzResearch.WordTrace tailWord_2020568 prefixEnd_2020568 1037522579093955752107583 := by
  unfold tailWord_2020568
  simp only [CollatzResearch.WordTrace]
  refine ⟨36848084671917348192923179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49130779562556464257230905 36848084671917348192923179)
  ·
    refine ⟨55272127007876022289384769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36848084671917348192923179 55272127007876022289384769)
    ·
      refine ⟨41454095255907016717038577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55272127007876022289384769 41454095255907016717038577)
      ·
        refine ⟨31090571441930262537778933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41454095255907016717038577 31090571441930262537778933)
        ·
          refine ⟨2914741072680962112916775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31090571441930262537778933 2914741072680962112916775)
          ·
            refine ⟨4372111609021443169375163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2914741072680962112916775 4372111609021443169375163)
            ·
              refine ⟨6558167413532164754062745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4372111609021443169375163 6558167413532164754062745)
              ·
                refine ⟨4918625560149123565547059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6558167413532164754062745 4918625560149123565547059)
                ·
                  refine ⟨7377938340223685348320589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4918625560149123565547059 7377938340223685348320589)
                  ·
                    refine ⟨2766726877583882005620221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7377938340223685348320589 2766726877583882005620221)
                    ·
                      refine ⟨1037522579093955752107583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2766726877583882005620221 1037522579093955752107583)
                      ·
                        rfl

theorem cell23_2020568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_2020568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020568 prefixEnd_2020568 := by exact prefixLift 2020568
  have htrace : WordTrace (prefixWord ++ tailWord_2020568) baseStart_2020568 baseEnd_2020568 := by
    simpa [prefixWord, tailWord_2020568, baseEnd_2020568] using wordTrace_append hprefix tailTrace_2020568
  have hstable : (prefixWord ++ tailWord_2020568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020568).length < 2 ^ (prefixWord ++ tailWord_2020568).sum := by decide
  have hdescent : baseEnd_2020568 < baseStart_2020568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020608 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 6, 2, 2]
def baseStart_2020608 : Nat := 118140960795 + 2020608 * 2 ^ 59
def prefixEnd_2020608 : Nat := 4983230072969 + 3 ^ 40 * 2020608 * 2
def baseEnd_2020608 : Nat := 1037543118320135595607399

theorem tailTrace_2020608 : CollatzResearch.WordTrace tailWord_2020608 prefixEnd_2020608 1037543118320135595607399 := by
  unfold tailWord_2020608
  simp only [CollatzResearch.WordTrace]
  refine ⟨36848814131844891608651239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49131752175793188811534985 36848814131844891608651239)
  ·
    refine ⟨55273221197767337412976859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36848814131844891608651239 55273221197767337412976859)
    ·
      refine ⟨82909831796651006119465289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55273221197767337412976859 82909831796651006119465289)
      ·
        refine ⟨62182373847488254589598967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82909831796651006119465289 62182373847488254589598967)
        ·
          refine ⟨93273560771232381884398451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62182373847488254589598967 93273560771232381884398451)
          ·
            refine ⟨139910341156848572826597677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93273560771232381884398451 139910341156848572826597677)
            ·
              refine ⟨52466377933818214809974129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139910341156848572826597677 52466377933818214809974129)
              ·
                refine ⟨39349783450363661107480597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52466377933818214809974129 39349783450363661107480597)
                ·
                  refine ⟨1844521099235796614413153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39349783450363661107480597 1844521099235796614413153)
                  ·
                    refine ⟨1383390824426847460809865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1844521099235796614413153 1383390824426847460809865)
                    ·
                      refine ⟨1037543118320135595607399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1383390824426847460809865 1037543118320135595607399)
                      ·
                        rfl

theorem cell23_2020608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 6, 2, 2].length) (baseStart_2020608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020608 prefixEnd_2020608 := by exact prefixLift 2020608
  have htrace : WordTrace (prefixWord ++ tailWord_2020608) baseStart_2020608 baseEnd_2020608 := by
    simpa [prefixWord, tailWord_2020608, baseEnd_2020608] using wordTrace_append hprefix tailTrace_2020608
  have hstable : (prefixWord ++ tailWord_2020608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020608).length < 2 ^ (prefixWord ++ tailWord_2020608).sum := by decide
  have hdescent : baseEnd_2020608 < baseStart_2020608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020642 : List Nat := [3, 3, 1, 1, 4, 1, 1, 1, 4, 2, 2]
def baseStart_2020642 : Nat := 118140960795 + 2020642 * 2 ^ 59
def prefixEnd_2020642 : Nat := 4983230072969 + 3 ^ 40 * 2020642 * 2
def baseEnd_2020642 : Nat := 1037560576662388462582243

theorem tailTrace_2020642 : CollatzResearch.WordTrace tailWord_2020642 prefixEnd_2020642 1037560576662388462582243 := by
  unfold tailWord_2020642
  simp only [CollatzResearch.WordTrace]
  refine ⟨18424717086391651756010045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49132578897044404682693453 18424717086391651756010045)
  ·
    refine ⟨6909268907396869408503767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18424717086391651756010045 6909268907396869408503767)
    ·
      refine ⟨10363903361095304112755651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6909268907396869408503767 10363903361095304112755651)
      ·
        refine ⟨15545855041642956169133477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10363903361095304112755651 15545855041642956169133477)
        ·
          refine ⟨2914847820308054281712527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15545855041642956169133477 2914847820308054281712527)
          ·
            refine ⟨4372271730462081422568791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2914847820308054281712527 4372271730462081422568791)
            ·
              refine ⟨6558407595693122133853187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4372271730462081422568791 6558407595693122133853187)
              ·
                refine ⟨9837611393539683200779781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6558407595693122133853187 9837611393539683200779781)
                ·
                  refine ⟨1844552136288690600146209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9837611393539683200779781 1844552136288690600146209)
                  ·
                    refine ⟨1383414102216517950109657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1844552136288690600146209 1383414102216517950109657)
                    ·
                      refine ⟨1037560576662388462582243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1383414102216517950109657 1037560576662388462582243)
                      ·
                        rfl

theorem cell23_2020642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_2020642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020642 prefixEnd_2020642 := by exact prefixLift 2020642
  have htrace : WordTrace (prefixWord ++ tailWord_2020642) baseStart_2020642 baseEnd_2020642 := by
    simpa [prefixWord, tailWord_2020642, baseEnd_2020642] using wordTrace_append hprefix tailTrace_2020642
  have hstable : (prefixWord ++ tailWord_2020642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020642).length < 2 ^ (prefixWord ++ tailWord_2020642).sum := by decide
  have hdescent : baseEnd_2020642 < baseStart_2020642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020648 : List Nat := [2, 1, 5, 1, 2, 2, 2, 1, 7]
def baseStart_2020648 : Nat := 118140960795 + 2020648 * 2 ^ 59
def prefixEnd_2020648 : Nat := 4983230072969 + 3 ^ 40 * 2020648 * 2
def baseEnd_2020648 : Nat := 115284850838479493234135

theorem tailTrace_2020648 : CollatzResearch.WordTrace tailWord_2020648 prefixEnd_2020648 115284850838479493234135 := by
  unfold tailWord_2020648
  simp only [CollatzResearch.WordTrace]
  refine ⟨36849543591772435024379299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49132724789029913365839065 36849543591772435024379299)
  ·
    refine ⟨55274315387658652536568949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36849543591772435024379299 55274315387658652536568949)
    ·
      refine ⟨5181967067592998675303339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55274315387658652536568949 5181967067592998675303339)
      ·
        refine ⟨7772950601389498012955009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5181967067592998675303339 7772950601389498012955009)
        ·
          refine ⟨5829712951042123509716257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7772950601389498012955009 5829712951042123509716257)
          ·
            refine ⟨4372284713281592632287193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5829712951042123509716257 4372284713281592632287193)
            ·
              refine ⟨3279213534961194474215395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4372284713281592632287193 3279213534961194474215395)
              ·
                refine ⟨4918820302441791711323093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3279213534961194474215395 4918820302441791711323093)
                ·
                  refine ⟨115284850838479493234135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4918820302441791711323093 115284850838479493234135)
                  ·
                    rfl

theorem cell23_2020648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 7].length) (baseStart_2020648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020648 prefixEnd_2020648 := by exact prefixLift 2020648
  have htrace : WordTrace (prefixWord ++ tailWord_2020648) baseStart_2020648 baseEnd_2020648 := by
    simpa [prefixWord, tailWord_2020648, baseEnd_2020648] using wordTrace_append hprefix tailTrace_2020648
  have hstable : (prefixWord ++ tailWord_2020648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020648).length < 2 ^ (prefixWord ++ tailWord_2020648).sum := by decide
  have hdescent : baseEnd_2020648 < baseStart_2020648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020658 : List Nat := [3, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3]
def baseStart_2020658 : Nat := 118140960795 + 2020658 * 2 ^ 59
def prefixEnd_2020658 : Nat := 4983230072969 + 3 ^ 40 * 2020658 * 2
def baseEnd_2020658 : Nat := 1037568792352860399982169

theorem tailTrace_2020658 : CollatzResearch.WordTrace tailWord_2020658 prefixEnd_2020658 1037568792352860399982169 := by
  unfold tailWord_2020658
  simp only [CollatzResearch.WordTrace]
  refine ⟨18424862978377160439155657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49132967942339094504415085 18424862978377160439155657)
  ·
    refine ⟨13818647233782870329366743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18424862978377160439155657 13818647233782870329366743)
    ·
      refine ⟨20727970850674305494050115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13818647233782870329366743 20727970850674305494050115)
      ·
        refine ⟨31091956276011458241075173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20727970850674305494050115 31091956276011458241075173)
        ·
          refine ⟨5829741801752148420201595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31091956276011458241075173 5829741801752148420201595)
          ·
            refine ⟨8744612702628222630302393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5829741801752148420201595 8744612702628222630302393)
            ·
              refine ⟨6558459526971166972726795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8744612702628222630302393 6558459526971166972726795)
              ·
                refine ⟨9837689290456750459090193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6558459526971166972726795 9837689290456750459090193)
                ·
                  refine ⟨7378266967842562844317645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9837689290456750459090193 7378266967842562844317645)
                  ·
                    refine ⟨2766850112940961066619117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7378266967842562844317645 2766850112940961066619117)
                    ·
                      refine ⟨1037568792352860399982169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2766850112940961066619117 1037568792352860399982169)
                      ·
                        rfl

theorem cell23_2020658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_2020658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020658 prefixEnd_2020658 := by exact prefixLift 2020658
  have htrace : WordTrace (prefixWord ++ tailWord_2020658) baseStart_2020658 baseEnd_2020658 := by
    simpa [prefixWord, tailWord_2020658, baseEnd_2020658] using wordTrace_append hprefix tailTrace_2020658
  have hstable : (prefixWord ++ tailWord_2020658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020658).length < 2 ^ (prefixWord ++ tailWord_2020658).sum := by decide
  have hdescent : baseEnd_2020658 < baseStart_2020658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020661 : List Nat := [1, 3, 3, 1, 2, 2, 1, 2, 1, 7]
def baseStart_2020661 : Nat := 118140960795 + 2020661 * 2 ^ 59
def prefixEnd_2020661 : Nat := 4983230072969 + 3 ^ 40 * 2020661 * 2
def baseEnd_2020661 : Nat := 345856777598274629414885

theorem tailTrace_2020661 : CollatzResearch.WordTrace tailWord_2020661 prefixEnd_2020661 345856777598274629414885 := by
  unfold tailWord_2020661
  simp only [CollatzResearch.WordTrace]
  refine ⟨73699561332497773268981837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49133040888331848845987891 73699561332497773268981837)
  ·
    refine ⟨27637335499686664975868189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73699561332497773268981837 27637335499686664975868189)
    ·
      refine ⟨10364000812382499365950571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27637335499686664975868189 10364000812382499365950571)
      ·
        refine ⟨15546001218573749048925857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10364000812382499365950571 15546001218573749048925857)
        ·
          refine ⟨11659500913930311786694393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15546001218573749048925857 11659500913930311786694393)
          ·
            refine ⟨8744625685447733840020795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11659500913930311786694393 8744625685447733840020795)
            ·
              refine ⟨13116938528171600760031193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8744625685447733840020795 13116938528171600760031193)
              ·
                refine ⟨9837703896128700570023395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13116938528171600760031193 9837703896128700570023395)
                ·
                  refine ⟨14756555844193050855035093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9837703896128700570023395 14756555844193050855035093)
                  ·
                    refine ⟨345856777598274629414885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14756555844193050855035093 345856777598274629414885)
                    ·
                      rfl

theorem cell23_2020661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_2020661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020661 prefixEnd_2020661 := by exact prefixLift 2020661
  have htrace : WordTrace (prefixWord ++ tailWord_2020661) baseStart_2020661 baseEnd_2020661 := by
    simpa [prefixWord, tailWord_2020661, baseEnd_2020661] using wordTrace_append hprefix tailTrace_2020661
  have hstable : (prefixWord ++ tailWord_2020661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020661).length < 2 ^ (prefixWord ++ tailWord_2020661).sum := by decide
  have hdescent : baseEnd_2020661 < baseStart_2020661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020681 : List Nat := [1, 2, 1, 1, 2, 3, 4, 1, 1, 3, 4]
def baseStart_2020681 : Nat := 118140960795 + 2020681 * 2 ^ 59
def prefixEnd_2020681 : Nat := 4983230072969 + 3 ^ 40 * 2020681 * 2
def baseEnd_2020681 : Nat := 1037580602407913809994563

theorem tailTrace_2020681 : CollatzResearch.WordTrace tailWord_2020681 prefixEnd_2020681 1037580602407913809994563 := by
  unfold tailWord_2020681
  simp only [CollatzResearch.WordTrace]
  refine ⟨73700290792425316684709897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49133527194950211123139931 73700290792425316684709897)
  ·
    refine ⟨55275218094318987513532423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73700290792425316684709897 55275218094318987513532423)
    ·
      refine ⟨82912827141478481270298635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55275218094318987513532423 82912827141478481270298635)
      ·
        refine ⟨124369240712217721905447953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82912827141478481270298635 124369240712217721905447953)
        ·
          refine ⟨93276930534163291429085965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124369240712217721905447953 93276930534163291429085965)
          ·
            refine ⟨34978848950311234285907237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93276930534163291429085965 34978848950311234285907237)
            ·
              refine ⟨6558534178183356428607607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34978848950311234285907237 6558534178183356428607607)
              ·
                refine ⟨9837801267275034642911411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6558534178183356428607607 9837801267275034642911411)
                ·
                  refine ⟨14756701900912551964367117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9837801267275034642911411 14756701900912551964367117)
                  ·
                    refine ⟨5533763212842206986637669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14756701900912551964367117 5533763212842206986637669)
                    ·
                      refine ⟨1037580602407913809994563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5533763212842206986637669 1037580602407913809994563)
                      ·
                        rfl

theorem cell23_2020681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 3, 4].length) (baseStart_2020681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020681 prefixEnd_2020681 := by exact prefixLift 2020681
  have htrace : WordTrace (prefixWord ++ tailWord_2020681) baseStart_2020681 baseEnd_2020681 := by
    simpa [prefixWord, tailWord_2020681, baseEnd_2020681] using wordTrace_append hprefix tailTrace_2020681
  have hstable : (prefixWord ++ tailWord_2020681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020681).length < 2 ^ (prefixWord ++ tailWord_2020681).sum := by decide
  have hdescent : baseEnd_2020681 < baseStart_2020681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020698 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2]
def baseStart_2020698 : Nat := 118140960795 + 2020698 * 2 ^ 59
def prefixEnd_2020698 : Nat := 4983230072969 + 3 ^ 40 * 2020698 * 2
def baseEnd_2020698 : Nat := 1037589331579040243481985

theorem tailTrace_2020698 : CollatzResearch.WordTrace tailWord_2020698 prefixEnd_2020698 1037589331579040243481985 := by
  unfold tailWord_2020698
  simp only [CollatzResearch.WordTrace]
  refine ⟨18425227708340932147019687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49133940555575819058719165 18425227708340932147019687)
  ·
    refine ⟨27637841562511398220529531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18425227708340932147019687 27637841562511398220529531)
    ·
      refine ⟨41456762343767097330794297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27637841562511398220529531 41456762343767097330794297)
      ·
        refine ⟨31092571757825322998095723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41456762343767097330794297 31092571757825322998095723)
        ·
          refine ⟨46638857636737984497143585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31092571757825322998095723 46638857636737984497143585)
          ·
            refine ⟨34979143227553488372857689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46638857636737984497143585 34979143227553488372857689)
            ·
              refine ⟨26234357420665116279643267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34979143227553488372857689 26234357420665116279643267)
              ·
                refine ⟨39351536130997674419464901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26234357420665116279643267 39351536130997674419464901)
                ·
                  refine ⟨7378413024562063953649669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39351536130997674419464901 7378413024562063953649669)
                  ·
                    refine ⟨1383452442105386991309313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7378413024562063953649669 1383452442105386991309313)
                    ·
                      refine ⟨1037589331579040243481985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1383452442105386991309313 1037589331579040243481985)
                      ·
                        rfl

theorem cell23_2020698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2].length) (baseStart_2020698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020698 prefixEnd_2020698 := by exact prefixLift 2020698
  have htrace : WordTrace (prefixWord ++ tailWord_2020698) baseStart_2020698 baseEnd_2020698 := by
    simpa [prefixWord, tailWord_2020698, baseEnd_2020698] using wordTrace_append hprefix tailTrace_2020698
  have hstable : (prefixWord ++ tailWord_2020698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020698).length < 2 ^ (prefixWord ++ tailWord_2020698).sum := by decide
  have hdescent : baseEnd_2020698 < baseStart_2020698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020775 : List Nat := [1, 1, 6, 1, 1, 1, 2, 2, 1, 5, 2]
def baseStart_2020775 : Nat := 118140960795 + 2020775 * 2 ^ 59
def prefixEnd_2020775 : Nat := 4983230072969 + 3 ^ 40 * 2020775 * 2
def baseEnd_2020775 : Nat := 1037628869589436442219131

theorem tailTrace_2020775 : CollatzResearch.WordTrace tailWord_2020775 prefixEnd_2020775 1037628869589436442219131 := by
  unfold tailWord_2020775
  simp only [CollatzResearch.WordTrace]
  refine ⟨73703719254084770738631779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49135812836056513825754519 73703719254084770738631779)
  ·
    refine ⟨110555578881127156107947669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73703719254084770738631779 110555578881127156107947669)
    ·
      refine ⟨5182292760052835442560047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 110555578881127156107947669 5182292760052835442560047)
      ·
        refine ⟨7773439140079253163840071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5182292760052835442560047 7773439140079253163840071)
        ·
          refine ⟨11660158710118879745760107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7773439140079253163840071 11660158710118879745760107)
          ·
            refine ⟨17490238065178319618640161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11660158710118879745760107 17490238065178319618640161)
            ·
              refine ⟨13117678548883739713980121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17490238065178319618640161 13117678548883739713980121)
              ·
                refine ⟨9838258911662804785485091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13117678548883739713980121 9838258911662804785485091)
                ·
                  refine ⟨14757388367494207178227637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9838258911662804785485091 14757388367494207178227637)
                  ·
                    refine ⟨1383505159452581922958841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14757388367494207178227637 1383505159452581922958841)
                    ·
                      refine ⟨1037628869589436442219131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1383505159452581922958841 1037628869589436442219131)
                      ·
                        rfl

theorem cell23_2020775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_2020775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020775 prefixEnd_2020775 := by exact prefixLift 2020775
  have htrace : WordTrace (prefixWord ++ tailWord_2020775) baseStart_2020775 baseEnd_2020775 := by
    simpa [prefixWord, tailWord_2020775, baseEnd_2020775] using wordTrace_append hprefix tailTrace_2020775
  have hstable : (prefixWord ++ tailWord_2020775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020775).length < 2 ^ (prefixWord ++ tailWord_2020775).sum := by decide
  have hdescent : baseEnd_2020775 < baseStart_2020775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020808 : List Nat := [2, 1, 3, 1, 3, 1, 2, 3, 1, 1, 5]
def baseStart_2020808 : Nat := 118140960795 + 2020808 * 2 ^ 59
def prefixEnd_2020808 : Nat := 4983230072969 + 3 ^ 40 * 2020808 * 2
def baseEnd_2020808 : Nat := 1037645814451034813106479

theorem tailTrace_2020808 : CollatzResearch.WordTrace tailWord_2020808 prefixEnd_2020808 1037645814451034813106479 := by
  unfold tailWord_2020808
  simp only [CollatzResearch.WordTrace]
  refine ⟨36852461431482608687291539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49136615241976811583055385 36852461431482608687291539)
  ·
    refine ⟨55278692147223913030937309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36852461431482608687291539 55278692147223913030937309)
    ·
      refine ⟨20729509555208967386601491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55278692147223913030937309 20729509555208967386601491)
      ·
        refine ⟨31094264332813451079902237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20729509555208967386601491 31094264332813451079902237)
        ·
          refine ⟨11660349124805044154963339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31094264332813451079902237 11660349124805044154963339)
          ·
            refine ⟨17490523687207566232445009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11660349124805044154963339 17490523687207566232445009)
            ·
              refine ⟨13117892765405674674333757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17490523687207566232445009 13117892765405674674333757)
              ·
                refine ⟨4919209787027128002875159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13117892765405674674333757 4919209787027128002875159)
                ·
                  refine ⟨7378814680540692004312739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4919209787027128002875159 7378814680540692004312739)
                  ·
                    refine ⟨11068222020811038006469109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7378814680540692004312739 11068222020811038006469109)
                    ·
                      refine ⟨1037645814451034813106479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11068222020811038006469109 1037645814451034813106479)
                      ·
                        rfl

theorem cell23_2020808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_2020808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020808 prefixEnd_2020808 := by exact prefixLift 2020808
  have htrace : WordTrace (prefixWord ++ tailWord_2020808) baseStart_2020808 baseEnd_2020808 := by
    simpa [prefixWord, tailWord_2020808, baseEnd_2020808] using wordTrace_append hprefix tailTrace_2020808
  have hstable : (prefixWord ++ tailWord_2020808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020808).length < 2 ^ (prefixWord ++ tailWord_2020808).sum := by decide
  have hdescent : baseEnd_2020808 < baseStart_2020808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020815 : List Nat := [1, 1, 2, 1, 1, 4, 5, 2, 2, 4]
def baseStart_2020815 : Nat := 118140960795 + 2020815 * 2 ^ 59
def prefixEnd_2020815 : Nat := 4983230072969 + 3 ^ 40 * 2020815 * 2
def baseEnd_2020815 : Nat := 345883136271872095239649

theorem tailTrace_2020815 : CollatzResearch.WordTrace tailWord_2020815 prefixEnd_2020815 345883136271872095239649 := by
  unfold tailWord_2020815
  simp only [CollatzResearch.WordTrace]
  refine ⟨73705178173939857570087899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49136785449293238380058599 73705178173939857570087899)
  ·
    refine ⟨110557767260909786355131849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73705178173939857570087899 110557767260909786355131849)
    ·
      refine ⟨82918325445682339766348887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110557767260909786355131849 82918325445682339766348887)
      ·
        refine ⟨124377488168523509649523331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82918325445682339766348887 124377488168523509649523331)
        ·
          refine ⟨186566232252785264474284997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124377488168523509649523331 186566232252785264474284997)
          ·
            refine ⟨34981168547397237088928437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186566232252785264474284997 34981168547397237088928437)
            ·
              refine ⟨3279484551318490977087041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34981168547397237088928437 3279484551318490977087041)
              ·
                refine ⟨2459613413488868232815281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3279484551318490977087041 2459613413488868232815281)
                ·
                  refine ⟨1844710060116651174611461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2459613413488868232815281 1844710060116651174611461)
                  ·
                    refine ⟨345883136271872095239649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1844710060116651174611461 345883136271872095239649)
                    ·
                      rfl

theorem cell23_2020815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2, 4].length) (baseStart_2020815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020815 prefixEnd_2020815 := by exact prefixLift 2020815
  have htrace : WordTrace (prefixWord ++ tailWord_2020815) baseStart_2020815 baseEnd_2020815 := by
    simpa [prefixWord, tailWord_2020815, baseEnd_2020815] using wordTrace_append hprefix tailTrace_2020815
  have hstable : (prefixWord ++ tailWord_2020815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020815).length < 2 ^ (prefixWord ++ tailWord_2020815).sum := by decide
  have hdescent : baseEnd_2020815 < baseStart_2020815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020835 : List Nat := [1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 4]
def baseStart_2020835 : Nat := 118140960795 + 2020835 * 2 ^ 59
def prefixEnd_2020835 : Nat := 4983230072969 + 3 ^ 40 * 2020835 * 2
def baseEnd_2020835 : Nat := 1037659678428706207468855

theorem tailTrace_2020835 : CollatzResearch.WordTrace tailWord_2020835 prefixEnd_2020835 1037659678428706207468855 := by
  unfold tailWord_2020835
  simp only [CollatzResearch.WordTrace]
  refine ⟨73705907633867400985815959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49137271755911600657210639 73705907633867400985815959)
  ·
    refine ⟨110558861450801101478723939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73705907633867400985815959 110558861450801101478723939)
    ·
      refine ⟨165838292176201652218085909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110558861450801101478723939 165838292176201652218085909)
      ·
        refine ⟨7773669945759452447722777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 165838292176201652218085909 7773669945759452447722777)
        ·
          refine ⟨5830252459319589335792083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7773669945759452447722777 5830252459319589335792083)
          ·
            refine ⟨8745378688979384003688125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5830252459319589335792083 8745378688979384003688125)
            ·
              refine ⟨3279517008367269001383047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8745378688979384003688125 3279517008367269001383047)
              ·
                refine ⟨4919275512550903502074571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3279517008367269001383047 4919275512550903502074571)
                ·
                  refine ⟨7378913268826355253111857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4919275512550903502074571 7378913268826355253111857)
                  ·
                    refine ⟨5534184951619766439833893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7378913268826355253111857 5534184951619766439833893)
                    ·
                      refine ⟨1037659678428706207468855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5534184951619766439833893 1037659678428706207468855)
                      ·
                        rfl

theorem cell23_2020835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_2020835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020835 prefixEnd_2020835 := by exact prefixLift 2020835
  have htrace : WordTrace (prefixWord ++ tailWord_2020835) baseStart_2020835 baseEnd_2020835 := by
    simpa [prefixWord, tailWord_2020835, baseEnd_2020835] using wordTrace_append hprefix tailTrace_2020835
  have hstable : (prefixWord ++ tailWord_2020835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020835).length < 2 ^ (prefixWord ++ tailWord_2020835).sum := by decide
  have hdescent : baseEnd_2020835 < baseStart_2020835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020841 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 3, 9]
def baseStart_2020841 : Nat := 118140960795 + 2020841 * 2 ^ 59
def prefixEnd_2020841 : Nat := 4983230072969 + 3 ^ 40 * 2020841 * 2
def baseEnd_2020841 : Nat := 345887586437544394664609

theorem tailTrace_2020841 : CollatzResearch.WordTrace tailWord_2020841 prefixEnd_2020841 345887586437544394664609 := by
  unfold tailWord_2020841
  simp only [CollatzResearch.WordTrace]
  refine ⟨73706126471845664010534377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49137417647897109340356251 73706126471845664010534377)
  ·
    refine ⟨55279594853884248007900783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73706126471845664010534377 55279594853884248007900783)
    ·
      refine ⟨82919392280826372011851175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55279594853884248007900783 82919392280826372011851175)
      ·
        refine ⟨124379088421239558017776763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82919392280826372011851175 124379088421239558017776763)
        ·
          refine ⟨186568632631859337026665145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124379088421239558017776763 186568632631859337026665145)
          ·
            refine ⟨139926474473894502769998859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186568632631859337026665145 139926474473894502769998859)
            ·
              refine ⟨209889711710841754154998289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139926474473894502769998859 209889711710841754154998289)
              ·
                refine ⟨157417283783131315616248717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209889711710841754154998289 157417283783131315616248717)
                ·
                  refine ⟨59031481418674243356093269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157417283783131315616248717 59031481418674243356093269)
                  ·
                    refine ⟨345887586437544394664609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 59031481418674243356093269 345887586437544394664609)
                    ·
                      rfl

theorem cell23_2020841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 9].length) (baseStart_2020841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020841 prefixEnd_2020841 := by exact prefixLift 2020841
  have htrace : WordTrace (prefixWord ++ tailWord_2020841) baseStart_2020841 baseEnd_2020841 := by
    simpa [prefixWord, tailWord_2020841, baseEnd_2020841] using wordTrace_append hprefix tailTrace_2020841
  have hstable : (prefixWord ++ tailWord_2020841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020841).length < 2 ^ (prefixWord ++ tailWord_2020841).sum := by decide
  have hdescent : baseEnd_2020841 < baseStart_2020841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020845 : List Nat := [1, 5, 1, 3, 2, 1, 1, 9]
def baseStart_2020845 : Nat := 118140960795 + 2020845 * 2 ^ 59
def prefixEnd_2020845 : Nat := 4983230072969 + 3 ^ 40 * 2020845 * 2
def baseEnd_2020845 : Nat := 38432030119824117346067

theorem tailTrace_2020845 : CollatzResearch.WordTrace tailWord_2020845 prefixEnd_2020845 38432030119824117346067 := by
  unfold tailWord_2020845
  simp only [CollatzResearch.WordTrace]
  refine ⟨73706272363831172693679989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49137514909220781795786659 73706272363831172693679989)
  ·
    refine ⟨6909963034109172440032499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73706272363831172693679989 6909963034109172440032499)
    ·
      refine ⟨10364944551163758660048749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6909963034109172440032499 10364944551163758660048749)
      ·
        refine ⟨3886854206686409497518281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10364944551163758660048749 3886854206686409497518281)
        ·
          refine ⟨2915140655014807123138711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3886854206686409497518281 2915140655014807123138711)
          ·
            refine ⟨4372710982522210684708067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2915140655014807123138711 4372710982522210684708067)
            ·
              refine ⟨6559066473783316027062101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4372710982522210684708067 6559066473783316027062101)
              ·
                refine ⟨38432030119824117346067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6559066473783316027062101 38432030119824117346067)
                ·
                  rfl

theorem cell23_2020845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 9].length) (baseStart_2020845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020845 prefixEnd_2020845 := by exact prefixLift 2020845
  have htrace : WordTrace (prefixWord ++ tailWord_2020845) baseStart_2020845 baseEnd_2020845 := by
    simpa [prefixWord, tailWord_2020845, baseEnd_2020845] using wordTrace_append hprefix tailTrace_2020845
  have hstable : (prefixWord ++ tailWord_2020845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020845).length < 2 ^ (prefixWord ++ tailWord_2020845).sum := by decide
  have hdescent : baseEnd_2020845 < baseStart_2020845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020856 : List Nat := [2, 1, 2, 1, 1, 7, 1, 3, 1, 2, 2]
def baseStart_2020856 : Nat := 118140960795 + 2020856 * 2 ^ 59
def prefixEnd_2020856 : Nat := 4983230072969 + 3 ^ 40 * 2020856 * 2
def baseEnd_2020856 : Nat := 1037670461522450625306259

theorem tailTrace_2020856 : CollatzResearch.WordTrace tailWord_2020856 prefixEnd_2020856 1037670461522450625306259 := by
  unfold tailWord_2020856
  simp only [CollatzResearch.WordTrace]
  refine ⟨36853336783395660786165211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49137782377860881048220281 36853336783395660786165211)
  ·
    refine ⟨55280005175093491179247817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36853336783395660786165211 55280005175093491179247817)
    ·
      refine ⟨41460003881320118384435863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55280005175093491179247817 41460003881320118384435863)
      ·
        refine ⟨62190005821980177576653795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41460003881320118384435863 62190005821980177576653795)
        ·
          refine ⟨93285008732970266364980693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62190005821980177576653795 93285008732970266364980693)
          ·
            refine ⟨2186367392178990617929235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 93285008732970266364980693 2186367392178990617929235)
            ·
              refine ⟨3279551088268485926893853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2186367392178990617929235 3279551088268485926893853)
              ·
                refine ⟨1229831658100682222585195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3279551088268485926893853 1229831658100682222585195)
                ·
                  refine ⟨1844747487151023333877793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1229831658100682222585195 1844747487151023333877793)
                  ·
                    refine ⟨1383560615363267500408345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1844747487151023333877793 1383560615363267500408345)
                    ·
                      refine ⟨1037670461522450625306259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1383560615363267500408345 1037670461522450625306259)
                      ·
                        rfl

theorem cell23_2020856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3, 1, 2, 2].length) (baseStart_2020856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020856 prefixEnd_2020856 := by exact prefixLift 2020856
  have htrace : WordTrace (prefixWord ++ tailWord_2020856) baseStart_2020856 baseEnd_2020856 := by
    simpa [prefixWord, tailWord_2020856, baseEnd_2020856] using wordTrace_append hprefix tailTrace_2020856
  have hstable : (prefixWord ++ tailWord_2020856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020856).length < 2 ^ (prefixWord ++ tailWord_2020856).sum := by decide
  have hdescent : baseEnd_2020856 < baseStart_2020856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020862 : List Nat := [4, 2, 2, 3, 1, 2, 9]
def baseStart_2020862 : Nat := 118140960795 + 2020862 * 2 ^ 59
def prefixEnd_2020862 : Nat := 4983230072969 + 3 ^ 40 * 2020862 * 2
def baseEnd_2020862 : Nat := 12810784474152809899151

theorem tailTrace_2020862 : CollatzResearch.WordTrace tailWord_2020862 prefixEnd_2020862 12810784474152809899151 := by
  unfold tailWord_2020862
  simp only [CollatzResearch.WordTrace]
  refine ⟨9213361550596198074631105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49137928269846389731365893 9213361550596198074631105)
  ·
    refine ⟨6910021162947148555973329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9213361550596198074631105 6910021162947148555973329)
    ·
      refine ⟨5182515872210361416979997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6910021162947148555973329 5182515872210361416979997)
      ·
        refine ⟨1943443452078885531367499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5182515872210361416979997 1943443452078885531367499)
        ·
          refine ⟨2915165178118328297051249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1943443452078885531367499 2915165178118328297051249)
          ·
            refine ⟨2186373883588746222788437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2915165178118328297051249 2186373883588746222788437)
            ·
              refine ⟨12810784474152809899151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2186373883588746222788437 12810784474152809899151)
              ·
                rfl

theorem cell23_2020862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 9].length) (baseStart_2020862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020862 prefixEnd_2020862 := by exact prefixLift 2020862
  have htrace : WordTrace (prefixWord ++ tailWord_2020862) baseStart_2020862 baseEnd_2020862 := by
    simpa [prefixWord, tailWord_2020862, baseEnd_2020862] using wordTrace_append hprefix tailTrace_2020862
  have hstable : (prefixWord ++ tailWord_2020862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020862).length < 2 ^ (prefixWord ++ tailWord_2020862).sum := by decide
  have hdescent : baseEnd_2020862 < baseStart_2020862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020908 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 4]
def baseStart_2020908 : Nat := 118140960795 + 2020908 * 2 ^ 59
def prefixEnd_2020908 : Nat := 4983230072969 + 3 ^ 40 * 2020908 * 2
def baseEnd_2020908 : Nat := 1037697162516484421856019

theorem tailTrace_2020908 : CollatzResearch.WordTrace tailWord_2020908 prefixEnd_2020908 1037697162516484421856019 := by
  unfold tailWord_2020908
  simp only [CollatzResearch.WordTrace]
  refine ⟨36854285081301467226611689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49139046775068622968815585 36854285081301467226611689)
  ·
    refine ⟨27640713810976100419958767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36854285081301467226611689 27640713810976100419958767)
    ·
      refine ⟨41461070716464150629938151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27640713810976100419958767 41461070716464150629938151)
      ·
        refine ⟨62191606074696225944907227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41461070716464150629938151 62191606074696225944907227)
        ·
          refine ⟨93287409112044338917360841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62191606074696225944907227 93287409112044338917360841)
          ·
            refine ⟨69965556834033254188020631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93287409112044338917360841 69965556834033254188020631)
            ·
              refine ⟨104948335251049881282030947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69965556834033254188020631 104948335251049881282030947)
              ·
                refine ⟨157422502876574821923046421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104948335251049881282030947 157422502876574821923046421)
                ·
                  refine ⟨7379179822339444777642801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 157422502876574821923046421 7379179822339444777642801)
                  ·
                    refine ⟨5534384866754583583232101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7379179822339444777642801 5534384866754583583232101)
                    ·
                      refine ⟨1037697162516484421856019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5534384866754583583232101 1037697162516484421856019)
                      ·
                        rfl

theorem cell23_2020908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_2020908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020908 prefixEnd_2020908 := by exact prefixLift 2020908
  have htrace : WordTrace (prefixWord ++ tailWord_2020908) baseStart_2020908 baseEnd_2020908 := by
    simpa [prefixWord, tailWord_2020908, baseEnd_2020908] using wordTrace_append hprefix tailTrace_2020908
  have hstable : (prefixWord ++ tailWord_2020908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020908).length < 2 ^ (prefixWord ++ tailWord_2020908).sum := by decide
  have hdescent : baseEnd_2020908 < baseStart_2020908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020945 : List Nat := [1, 2, 2, 1, 3, 2, 3, 1, 2, 3, 3]
def baseStart_2020945 : Nat := 118140960795 + 2020945 * 2 ^ 59
def prefixEnd_2020945 : Nat := 4983230072969 + 3 ^ 40 * 2020945 * 2
def baseEnd_2020945 : Nat := 1037716161300700777093349

theorem tailTrace_2020945 : CollatzResearch.WordTrace tailWord_2020945 prefixEnd_2020945 1037716161300700777093349 := by
  unfold tailWord_2020945
  simp only [CollatzResearch.WordTrace]
  refine ⟨73709919663468889772320289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49139946442312593181546859 73709919663468889772320289)
  ·
    refine ⟨55282439747601667329240217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73709919663468889772320289 55282439747601667329240217)
    ·
      refine ⟨41461829810701250496930163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55282439747601667329240217 41461829810701250496930163)
      ·
        refine ⟨62192744716051875745395245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41461829810701250496930163 62192744716051875745395245)
        ·
          refine ⟨23322279268519453404523217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62192744716051875745395245 23322279268519453404523217)
          ·
            refine ⟨17491709451389590053392413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23322279268519453404523217 17491709451389590053392413)
            ·
              refine ⟨6559391044271096270022155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17491709451389590053392413 6559391044271096270022155)
              ·
                refine ⟨9839086566406644405033233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6559391044271096270022155 9839086566406644405033233)
                ·
                  refine ⟨7379314924804983303774925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9839086566406644405033233 7379314924804983303774925)
                  ·
                    refine ⟨2767243096801868738915597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7379314924804983303774925 2767243096801868738915597)
                    ·
                      refine ⟨1037716161300700777093349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2767243096801868738915597 1037716161300700777093349)
                      ·
                        rfl

theorem cell23_2020945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 3, 3].length) (baseStart_2020945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020945 prefixEnd_2020945 := by exact prefixLift 2020945
  have htrace : WordTrace (prefixWord ++ tailWord_2020945) baseStart_2020945 baseEnd_2020945 := by
    simpa [prefixWord, tailWord_2020945, baseEnd_2020945] using wordTrace_append hprefix tailTrace_2020945
  have hstable : (prefixWord ++ tailWord_2020945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020945).length < 2 ^ (prefixWord ++ tailWord_2020945).sum := by decide
  have hdescent : baseEnd_2020945 < baseStart_2020945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020965 : List Nat := [1, 3, 1, 3, 3, 2, 1, 1, 1, 7]
def baseStart_2020965 : Nat := 118140960795 + 2020965 * 2 ^ 59
def prefixEnd_2020965 : Nat := 4983230072969 + 3 ^ 40 * 2020965 * 2
def baseEnd_2020965 : Nat := 345908810304596899614419

theorem tailTrace_2020965 : CollatzResearch.WordTrace tailWord_2020965 prefixEnd_2020965 345908810304596899614419 := by
  unfold tailWord_2020965
  simp only [CollatzResearch.WordTrace]
  refine ⟨73710649123396433188048349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49140432748930955458698899 73710649123396433188048349)
  ·
    refine ⟨27641493421273662445518131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73710649123396433188048349 27641493421273662445518131)
    ·
      refine ⟨41462240131910493668277197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27641493421273662445518131 41462240131910493668277197)
      ·
        refine ⟨15548340049466435125603949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41462240131910493668277197 15548340049466435125603949)
        ·
          refine ⟨5830627518549913172101481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15548340049466435125603949 5830627518549913172101481)
          ·
            refine ⟨4372970638912434879076111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5830627518549913172101481 4372970638912434879076111)
            ·
              refine ⟨6559455958368652318614167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4372970638912434879076111 6559455958368652318614167)
              ·
                refine ⟨9839183937552978477921251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6559455958368652318614167 9839183937552978477921251)
                ·
                  refine ⟨14758775906329467716881877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9839183937552978477921251 14758775906329467716881877)
                  ·
                    refine ⟨345908810304596899614419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14758775906329467716881877 345908810304596899614419)
                    ·
                      rfl

theorem cell23_2020965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 7].length) (baseStart_2020965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020965 prefixEnd_2020965 := by exact prefixLift 2020965
  have htrace : WordTrace (prefixWord ++ tailWord_2020965) baseStart_2020965 baseEnd_2020965 := by
    simpa [prefixWord, tailWord_2020965, baseEnd_2020965] using wordTrace_append hprefix tailTrace_2020965
  have hstable : (prefixWord ++ tailWord_2020965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020965).length < 2 ^ (prefixWord ++ tailWord_2020965).sum := by decide
  have hdescent : baseEnd_2020965 < baseStart_2020965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020985 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 4, 1, 4]
def baseStart_2020985 : Nat := 118140960795 + 2020985 * 2 ^ 59
def prefixEnd_2020985 : Nat := 4983230072969 + 3 ^ 40 * 2020985 * 2
def baseEnd_2020985 : Nat := 1037736700526880620593165

theorem tailTrace_2020985 : CollatzResearch.WordTrace tailWord_2020985 prefixEnd_2020985 1037736700526880620593165 := by
  unfold tailWord_2020985
  simp only [CollatzResearch.WordTrace]
  refine ⟨73711378583323976603776409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49140919055549317735850939 73711378583323976603776409)
  ·
    refine ⟨55283533937492982452832307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73711378583323976603776409 55283533937492982452832307)
    ·
      refine ⟨82925300906239473679248461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55283533937492982452832307 82925300906239473679248461)
      ·
        refine ⟨31096987839839802629718173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82925300906239473679248461 31096987839839802629718173)
        ·
          refine ⟨11661370439939925986144315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31096987839839802629718173 11661370439939925986144315)
          ·
            refine ⟨17492055659909888979216473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11661370439939925986144315 17492055659909888979216473)
            ·
              refine ⟨13119041744932416734412355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17492055659909888979216473 13119041744932416734412355)
              ·
                refine ⟨19678562617398625101618533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13119041744932416734412355 19678562617398625101618533)
                ·
                  refine ⟨3689730490762242206553475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19678562617398625101618533 3689730490762242206553475)
                  ·
                    refine ⟨5534595736143363309830213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3689730490762242206553475 5534595736143363309830213)
                    ·
                      refine ⟨1037736700526880620593165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5534595736143363309830213 1037736700526880620593165)
                      ·
                        rfl

theorem cell23_2020985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_2020985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2020985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2020985 prefixEnd_2020985 := by exact prefixLift 2020985
  have htrace : WordTrace (prefixWord ++ tailWord_2020985) baseStart_2020985 baseEnd_2020985 := by
    simpa [prefixWord, tailWord_2020985, baseEnd_2020985] using wordTrace_append hprefix tailTrace_2020985
  have hstable : (prefixWord ++ tailWord_2020985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020985).length < 2 ^ (prefixWord ++ tailWord_2020985).sum := by decide
  have hdescent : baseEnd_2020985 < baseStart_2020985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021025 : List Nat := [1, 2, 3, 3, 2, 1, 1, 2, 8]
def baseStart_2021025 : Nat := 118140960795 + 2021025 * 2 ^ 59
def prefixEnd_2021025 : Nat := 4983230072969 + 3 ^ 40 * 2021025 * 2
def baseEnd_2021025 : Nat := 115306359972562273788109

theorem tailTrace_2021025 : CollatzResearch.WordTrace tailWord_2021025 prefixEnd_2021025 115306359972562273788109 := by
  unfold tailWord_2021025
  simp only [CollatzResearch.WordTrace]
  refine ⟨73712837503179063435232529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49141891668786042290155019 73712837503179063435232529)
  ·
    refine ⟨55284628127384297576424397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73712837503179063435232529 55284628127384297576424397)
    ·
      refine ⟨20731735547769111591159149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55284628127384297576424397 20731735547769111591159149)
      ·
        refine ⟨7774400830413416846684681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20731735547769111591159149 7774400830413416846684681)
        ·
          refine ⟨5830800622810062635013511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7774400830413416846684681 5830800622810062635013511)
          ·
            refine ⟨8746200934215093952520267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5830800622810062635013511 8746200934215093952520267)
            ·
              refine ⟨13119301401322640928780401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8746200934215093952520267 13119301401322640928780401)
              ·
                refine ⟨9839476050991980696585301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13119301401322640928780401 9839476050991980696585301)
                ·
                  refine ⟨115306359972562273788109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9839476050991980696585301 115306359972562273788109)
                  ·
                    rfl

theorem cell23_2021025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 8].length) (baseStart_2021025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021025 prefixEnd_2021025 := by exact prefixLift 2021025
  have htrace : WordTrace (prefixWord ++ tailWord_2021025) baseStart_2021025 baseEnd_2021025 := by
    simpa [prefixWord, tailWord_2021025, baseEnd_2021025] using wordTrace_append hprefix tailTrace_2021025
  have hstable : (prefixWord ++ tailWord_2021025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021025).length < 2 ^ (prefixWord ++ tailWord_2021025).sum := by decide
  have hdescent : baseEnd_2021025 < baseStart_2021025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021029 : List Nat := [1, 3, 1, 2, 1, 2, 5, 3, 1, 4]
def baseStart_2021029 : Nat := 118140960795 + 2021029 * 2 ^ 59
def prefixEnd_2021029 : Nat := 4983230072969 + 3 ^ 40 * 2021029 * 2
def baseEnd_2021029 : Nat := 345919764558559482814321

theorem tailTrace_2021029 : CollatzResearch.WordTrace tailWord_2021029 prefixEnd_2021029 345919764558559482814321 := by
  unfold tailWord_2021029
  simp only [CollatzResearch.WordTrace]
  refine ⟨73712983395164572118378141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49141988930109714745585427 73712983395164572118378141)
  ·
    refine ⟨27642368773186714544391803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73712983395164572118378141 27642368773186714544391803)
    ·
      refine ⟨41463553159780071816587705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27642368773186714544391803 41463553159780071816587705)
      ·
        refine ⟨31097664869835053862440779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41463553159780071816587705 31097664869835053862440779)
        ·
          refine ⟨46646497304752580793661169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31097664869835053862440779 46646497304752580793661169)
          ·
            refine ⟨34984872978564435595245877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46646497304752580793661169 34984872978564435595245877)
            ·
              refine ⟨3279831841740415837054301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34984872978564435595245877 3279831841740415837054301)
              ·
                refine ⟨1229936940652655938895363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3279831841740415837054301 1229936940652655938895363)
                ·
                  refine ⟨1844905410978983908343045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1229936940652655938895363 1844905410978983908343045)
                  ·
                    refine ⟨345919764558559482814321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1844905410978983908343045 345919764558559482814321)
                    ·
                      rfl

theorem cell23_2021029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3, 1, 4].length) (baseStart_2021029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021029 prefixEnd_2021029 := by exact prefixLift 2021029
  have htrace : WordTrace (prefixWord ++ tailWord_2021029) baseStart_2021029 baseEnd_2021029 := by
    simpa [prefixWord, tailWord_2021029, baseEnd_2021029] using wordTrace_append hprefix tailTrace_2021029
  have hstable : (prefixWord ++ tailWord_2021029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021029).length < 2 ^ (prefixWord ++ tailWord_2021029).sum := by decide
  have hdescent : baseEnd_2021029 < baseStart_2021029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021046 : List Nat := [5, 1, 3, 1, 1, 1, 3, 1, 3, 4]
def baseStart_2021046 : Nat := 118140960795 + 2021046 * 2 ^ 59
def prefixEnd_2021046 : Nat := 4983230072969 + 3 ^ 40 * 2021046 * 2
def baseEnd_2021046 : Nat := 345922674282268293976795

theorem tailTrace_2021046 : CollatzResearch.WordTrace tailWord_2021046 prefixEnd_2021046 345922674282268293976795 := by
  unfold tailWord_2021046
  simp only [CollatzResearch.WordTrace]
  refine ⟨4607100214756436501359187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49142402290735322681164661 4607100214756436501359187)
  ·
    refine ⟨6910650322134654752038781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4607100214756436501359187 6910650322134654752038781)
    ·
      refine ⟨2591493870800495532014543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6910650322134654752038781 2591493870800495532014543)
      ·
        refine ⟨3887240806200743298021815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2591493870800495532014543 3887240806200743298021815)
        ·
          refine ⟨5830861209301114947032723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3887240806200743298021815 5830861209301114947032723)
          ·
            refine ⟨8746291813951672420549085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5830861209301114947032723 8746291813951672420549085)
            ·
              refine ⟨3279859430231877157705907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8746291813951672420549085 3279859430231877157705907)
              ·
                refine ⟨4919789145347815736558861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3279859430231877157705907 4919789145347815736558861)
                ·
                  refine ⟨1844920929505430901209573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4919789145347815736558861 1844920929505430901209573)
                  ·
                    refine ⟨345922674282268293976795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1844920929505430901209573 345922674282268293976795)
                    ·
                      rfl

theorem cell23_2021046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_2021046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021046 prefixEnd_2021046 := by exact prefixLift 2021046
  have htrace : WordTrace (prefixWord ++ tailWord_2021046) baseStart_2021046 baseEnd_2021046 := by
    simpa [prefixWord, tailWord_2021046, baseEnd_2021046] using wordTrace_append hprefix tailTrace_2021046
  have hstable : (prefixWord ++ tailWord_2021046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021046).length < 2 ^ (prefixWord ++ tailWord_2021046).sum := by decide
  have hdescent : baseEnd_2021046 < baseStart_2021046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021055 : List Nat := [1, 1, 2, 2, 2, 3, 2, 2, 3, 5]
def baseStart_2021055 : Nat := 118140960795 + 2021055 * 2 ^ 59
def prefixEnd_2021055 : Nat := 4983230072969 + 3 ^ 40 * 2021055 * 2
def baseEnd_2021055 : Nat := 345924214724231782239281

theorem tailTrace_2021055 : CollatzResearch.WordTrace tailWord_2021055 prefixEnd_2021055 345924214724231782239281 := by
  unfold tailWord_2021055
  simp only [CollatzResearch.WordTrace]
  refine ⟨73713931693070378558824619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49142621128713585705883079 73713931693070378558824619)
  ·
    refine ⟨110570897539605567838236929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73713931693070378558824619 110570897539605567838236929)
    ·
      refine ⟨82928173154704175878677697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110570897539605567838236929 82928173154704175878677697)
      ·
        refine ⟨62196129866028131909008273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82928173154704175878677697 62196129866028131909008273)
        ·
          refine ⟨46647097399521098931756205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62196129866028131909008273 46647097399521098931756205)
          ·
            refine ⟨17492661524820412099408577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46647097399521098931756205 17492661524820412099408577)
            ·
              refine ⟨13119496143615309074556433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17492661524820412099408577 13119496143615309074556433)
              ·
                refine ⟨9839622107711481805917325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13119496143615309074556433 9839622107711481805917325)
                ·
                  refine ⟨3689858290391805677218997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9839622107711481805917325 3689858290391805677218997)
                  ·
                    refine ⟨345924214724231782239281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3689858290391805677218997 345924214724231782239281)
                    ·
                      rfl

theorem cell23_2021055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 5].length) (baseStart_2021055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021055 prefixEnd_2021055 := by exact prefixLift 2021055
  have htrace : WordTrace (prefixWord ++ tailWord_2021055) baseStart_2021055 baseEnd_2021055 := by
    simpa [prefixWord, tailWord_2021055, baseEnd_2021055] using wordTrace_append hprefix tailTrace_2021055
  have hstable : (prefixWord ++ tailWord_2021055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021055).length < 2 ^ (prefixWord ++ tailWord_2021055).sum := by decide
  have hdescent : baseEnd_2021055 < baseStart_2021055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021079 : List Nat := [1, 1, 3, 2, 1, 3, 4, 1, 2, 3, 2]
def baseStart_2021079 : Nat := 118140960795 + 2021079 * 2 ^ 59
def prefixEnd_2021079 : Nat := 4983230072969 + 3 ^ 40 * 2021079 * 2
def baseEnd_2021079 : Nat := 1037784967708403252817733

theorem tailTrace_2021079 : CollatzResearch.WordTrace tailWord_2021079 prefixEnd_2021079 1037784967708403252817733 := by
  unfold tailWord_2021079
  simp only [CollatzResearch.WordTrace]
  refine ⟨73714807044983430657698291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49143204696655620438465527 73714807044983430657698291)
  ·
    refine ⟨110572210567475145986547437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73714807044983430657698291 110572210567475145986547437)
    ·
      refine ⟨41464578962803179744955289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110572210567475145986547437 41464578962803179744955289)
      ·
        refine ⟨31098434222102384808716467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41464578962803179744955289 31098434222102384808716467)
        ·
          refine ⟨46647651333153577213074701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31098434222102384808716467 46647651333153577213074701)
          ·
            refine ⟨17492869249932591454903013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46647651333153577213074701 17492869249932591454903013)
            ·
              refine ⟨3279912984362360897794315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17492869249932591454903013 3279912984362360897794315)
              ·
                refine ⟨4919869476543541346691473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3279912984362360897794315 4919869476543541346691473)
                ·
                  refine ⟨3689902107407656010018605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4919869476543541346691473 3689902107407656010018605)
                  ·
                    refine ⟨1383713290277871003756977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3689902107407656010018605 1383713290277871003756977)
                    ·
                      refine ⟨1037784967708403252817733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1383713290277871003756977 1037784967708403252817733)
                      ·
                        rfl

theorem cell23_2021079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 3, 2].length) (baseStart_2021079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021079 prefixEnd_2021079 := by exact prefixLift 2021079
  have htrace : WordTrace (prefixWord ++ tailWord_2021079) baseStart_2021079 baseEnd_2021079 := by
    simpa [prefixWord, tailWord_2021079, baseEnd_2021079] using wordTrace_append hprefix tailTrace_2021079
  have hstable : (prefixWord ++ tailWord_2021079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021079).length < 2 ^ (prefixWord ++ tailWord_2021079).sum := by decide
  have hdescent : baseEnd_2021079 < baseStart_2021079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021143 : List Nat := [1, 1, 3, 4, 2, 1, 1, 5, 1, 2, 2]
def baseStart_2021143 : Nat := 118140960795 + 2021143 * 2 ^ 59
def prefixEnd_2021143 : Nat := 4983230072969 + 3 ^ 40 * 2021143 * 2
def baseEnd_2021143 : Nat := 1037817830470291002417439

theorem tailTrace_2021143 : CollatzResearch.WordTrace tailWord_2021143 prefixEnd_2021143 1037817830470291002417439 := by
  unfold tailWord_2021143
  simp only [CollatzResearch.WordTrace]
  refine ⟨73717141316751569588028083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49144760877834379725352055 73717141316751569588028083)
  ·
    refine ⟨110575711975127354382042125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73717141316751569588028083 110575711975127354382042125)
    ·
      refine ⟨41465891990672757893265797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110575711975127354382042125 41465891990672757893265797)
      ·
        refine ⟨7774854748251142104987337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41465891990672757893265797 7774854748251142104987337)
        ·
          refine ⟨5831141061188356578740503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7774854748251142104987337 5831141061188356578740503)
          ·
            refine ⟨8746711591782534868110755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5831141061188356578740503 8746711591782534868110755)
            ·
              refine ⟨13120067387673802302166133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8746711591782534868110755 13120067387673802302166133)
              ·
                refine ⟨1230006317594418965828075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13120067387673802302166133 1230006317594418965828075)
                ·
                  refine ⟨1845009476391628448742113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1230006317594418965828075 1845009476391628448742113)
                  ·
                    refine ⟨1383757107293721336556585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1845009476391628448742113 1383757107293721336556585)
                    ·
                      refine ⟨1037817830470291002417439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1383757107293721336556585 1037817830470291002417439)
                      ·
                        rfl

theorem cell23_2021143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_2021143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021143 prefixEnd_2021143 := by exact prefixLift 2021143
  have htrace : WordTrace (prefixWord ++ tailWord_2021143) baseStart_2021143 baseEnd_2021143 := by
    simpa [prefixWord, tailWord_2021143, baseEnd_2021143] using wordTrace_append hprefix tailTrace_2021143
  have hstable : (prefixWord ++ tailWord_2021143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021143).length < 2 ^ (prefixWord ++ tailWord_2021143).sum := by decide
  have hdescent : baseEnd_2021143 < baseStart_2021143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021146 : List Nat := [3, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3]
def baseStart_2021146 : Nat := 118140960795 + 2021146 * 2 ^ 59
def prefixEnd_2021146 : Nat := 4983230072969 + 3 ^ 40 * 2021146 * 2
def baseEnd_2021146 : Nat := 1037819370912254490679925

theorem tailTrace_2021146 : CollatzResearch.WordTrace tailWord_2021146 prefixEnd_2021146 1037819370912254490679925 := by
  unfold tailWord_2021146
  simp only [CollatzResearch.WordTrace]
  refine ⟨18429312683935175275096823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49144833823827134066924861 18429312683935175275096823)
  ·
    refine ⟨27643969025902762912645235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18429312683935175275096823 27643969025902762912645235)
    ·
      refine ⟨41465953538854144368967853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27643969025902762912645235 41465953538854144368967853)
      ·
        refine ⟨15549732577070304138362945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41465953538854144368967853 15549732577070304138362945)
        ·
          refine ⟨11662299432802728103772209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15549732577070304138362945 11662299432802728103772209)
          ·
            refine ⟨8746724574602046077829157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11662299432802728103772209 8746724574602046077829157)
            ·
              refine ⟨1640010857737883639592967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8746724574602046077829157 1640010857737883639592967)
              ·
                refine ⟨2460016286606825459389451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1640010857737883639592967 2460016286606825459389451)
                ·
                  refine ⟨3690024429910238189084177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2460016286606825459389451 3690024429910238189084177)
                  ·
                    refine ⟨2767518322432678641813133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3690024429910238189084177 2767518322432678641813133)
                    ·
                      refine ⟨1037819370912254490679925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2767518322432678641813133 1037819370912254490679925)
                      ·
                        rfl

theorem cell23_2021146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_2021146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021146 prefixEnd_2021146 := by exact prefixLift 2021146
  have htrace : WordTrace (prefixWord ++ tailWord_2021146) baseStart_2021146 baseEnd_2021146 := by
    simpa [prefixWord, tailWord_2021146, baseEnd_2021146] using wordTrace_append hprefix tailTrace_2021146
  have hstable : (prefixWord ++ tailWord_2021146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021146).length < 2 ^ (prefixWord ++ tailWord_2021146).sum := by decide
  have hdescent : baseEnd_2021146 < baseStart_2021146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021175 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 1, 8]
def baseStart_2021175 : Nat := 118140960795 + 2021175 * 2 ^ 59
def prefixEnd_2021175 : Nat := 4983230072969 + 3 ^ 40 * 2021175 * 2
def baseEnd_2021175 : Nat := 345944753950411625739097

theorem tailTrace_2021175 : CollatzResearch.WordTrace tailWord_2021175 prefixEnd_2021175 345944753950411625739097 := by
  unfold tailWord_2021175
  simp only [CollatzResearch.WordTrace]
  refine ⟨73718308452635639053192979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49145538968423759368795319 73718308452635639053192979)
  ·
    refine ⟨110577462678953458579789469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73718308452635639053192979 110577462678953458579789469)
    ·
      refine ⟨41466548504607546967421051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110577462678953458579789469 41466548504607546967421051)
      ·
        refine ⟨62199822756911320451131577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41466548504607546967421051 62199822756911320451131577)
        ·
          refine ⟨46649867067683490338348683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62199822756911320451131577 46649867067683490338348683)
          ·
            refine ⟨69974800601525235507523025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46649867067683490338348683 69974800601525235507523025)
            ·
              refine ⟨52481100451143926630642269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69974800601525235507523025 52481100451143926630642269)
              ·
                refine ⟨19680412669178972486490851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52481100451143926630642269 19680412669178972486490851)
                ·
                  refine ⟨29520619003768458729736277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19680412669178972486490851 29520619003768458729736277)
                  ·
                    refine ⟨345944753950411625739097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29520619003768458729736277 345944753950411625739097)
                    ·
                      rfl

theorem cell23_2021175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_2021175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021175 prefixEnd_2021175 := by exact prefixLift 2021175
  have htrace : WordTrace (prefixWord ++ tailWord_2021175) baseStart_2021175 baseEnd_2021175 := by
    simpa [prefixWord, tailWord_2021175, baseEnd_2021175] using wordTrace_append hprefix tailTrace_2021175
  have hstable : (prefixWord ++ tailWord_2021175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021175).length < 2 ^ (prefixWord ++ tailWord_2021175).sum := by decide
  have hdescent : baseEnd_2021175 < baseStart_2021175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021202 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_2021202 : Nat := 118140960795 + 2021202 * 2 ^ 59
def prefixEnd_2021202 : Nat := 4983230072969 + 3 ^ 40 * 2021202 * 2
def baseEnd_2021202 : Nat := 1037848125828906271579667

theorem tailTrace_2021202 : CollatzResearch.WordTrace tailWord_2021202 prefixEnd_2021202 1037848125828906271579667 := by
  unfold tailWord_2021202
  simp only [CollatzResearch.WordTrace]
  refine ⟨18429823305884455666106465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49146195482358548442950573 18429823305884455666106465)
  ·
    refine ⟨13822367479413341749579849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18429823305884455666106465 13822367479413341749579849)
    ·
      refine ⟨10366775609560006312184887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13822367479413341749579849 10366775609560006312184887)
      ·
        refine ⟨15550163414340009468277331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10366775609560006312184887 15550163414340009468277331)
        ·
          refine ⟨23325245121510014202415997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15550163414340009468277331 23325245121510014202415997)
          ·
            refine ⟨8746966920566255325905999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23325245121510014202415997 8746966920566255325905999)
            ·
              refine ⟨13120450380849382988858999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8746966920566255325905999 13120450380849382988858999)
              ·
                refine ⟨19680675571274074483288499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13120450380849382988858999 19680675571274074483288499)
                ·
                  refine ⟨29521013356911111724932749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19680675571274074483288499 29521013356911111724932749)
                  ·
                    refine ⟨11070380008841666896849781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29521013356911111724932749 11070380008841666896849781)
                    ·
                      refine ⟨1037848125828906271579667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11070380008841666896849781 1037848125828906271579667)
                      ·
                        rfl

theorem cell23_2021202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_2021202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021202 prefixEnd_2021202 := by exact prefixLift 2021202
  have htrace : WordTrace (prefixWord ++ tailWord_2021202) baseStart_2021202 baseEnd_2021202 := by
    simpa [prefixWord, tailWord_2021202, baseEnd_2021202] using wordTrace_append hprefix tailTrace_2021202
  have hstable : (prefixWord ++ tailWord_2021202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021202).length < 2 ^ (prefixWord ++ tailWord_2021202).sum := by decide
  have hdescent : baseEnd_2021202 < baseStart_2021202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021216 : List Nat := [2, 1, 1, 3, 3, 2, 2, 1, 4, 2, 2]
def baseStart_2021216 : Nat := 118140960795 + 2021216 * 2 ^ 59
def prefixEnd_2021216 : Nat := 4983230072969 + 3 ^ 40 * 2021216 * 2
def baseEnd_2021216 : Nat := 1037855314558069216804603

theorem tailTrace_2021216 : CollatzResearch.WordTrace tailWord_2021216 prefixEnd_2021216 1037855314558069216804603 := by
  unfold tailWord_2021216
  simp only [CollatzResearch.WordTrace]
  refine ⟨36859901922743551527717751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49146535896991402036957001 36859901922743551527717751)
  ·
    refine ⟨55289852884115327291576627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36859901922743551527717751 55289852884115327291576627)
    ·
      refine ⟨82934779326172990937364941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55289852884115327291576627 82934779326172990937364941)
      ·
        refine ⟨31100542247314871601511853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82934779326172990937364941 31100542247314871601511853)
        ·
          refine ⟨11662703342743076850566945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31100542247314871601511853 11662703342743076850566945)
          ·
            refine ⟨8747027507057307637925209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11662703342743076850566945 8747027507057307637925209)
            ·
              refine ⟨6560270630292980728443907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8747027507057307637925209 6560270630292980728443907)
              ·
                refine ⟨9840405945439471092665861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6560270630292980728443907 9840405945439471092665861)
                ·
                  refine ⟨1845076114769900829874849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9840405945439471092665861 1845076114769900829874849)
                  ·
                    refine ⟨1383807086077425622406137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1845076114769900829874849 1383807086077425622406137)
                    ·
                      refine ⟨1037855314558069216804603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1383807086077425622406137 1037855314558069216804603)
                      ·
                        rfl

theorem cell23_2021216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 4, 2, 2].length) (baseStart_2021216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021216 prefixEnd_2021216 := by exact prefixLift 2021216
  have htrace : WordTrace (prefixWord ++ tailWord_2021216) baseStart_2021216 baseEnd_2021216 := by
    simpa [prefixWord, tailWord_2021216, baseEnd_2021216] using wordTrace_append hprefix tailTrace_2021216
  have hstable : (prefixWord ++ tailWord_2021216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021216).length < 2 ^ (prefixWord ++ tailWord_2021216).sum := by decide
  have hdescent : baseEnd_2021216 < baseStart_2021216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021232 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 3]
def baseStart_2021232 : Nat := 118140960795 + 2021232 * 2 ^ 59
def prefixEnd_2021232 : Nat := 4983230072969 + 3 ^ 40 * 2021232 * 2
def baseEnd_2021232 : Nat := 1037863530248541154204529

theorem tailTrace_2021232 : CollatzResearch.WordTrace tailWord_2021232 prefixEnd_2021232 1037863530248541154204529 := by
  unfold tailWord_2021232
  simp only [CollatzResearch.WordTrace]
  refine ⟨36860193706714568894008975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49146924942286091858678633 36860193706714568894008975)
  ·
    refine ⟨55290290560071853341013463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36860193706714568894008975 55290290560071853341013463)
    ·
      refine ⟨82935435840107780011520195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55290290560071853341013463 82935435840107780011520195)
      ·
        refine ⟨124403153760161670017280293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82935435840107780011520195 124403153760161670017280293)
        ·
          refine ⟨23325591330030313128240055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124403153760161670017280293 23325591330030313128240055)
          ·
            refine ⟨34988386995045469692360083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23325591330030313128240055 34988386995045469692360083)
            ·
              refine ⟨52482580492568204538540125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34988386995045469692360083 52482580492568204538540125)
              ·
                refine ⟨19680967684713076701952547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52482580492568204538540125 19680967684713076701952547)
                ·
                  refine ⟨29521451527069615052928821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19680967684713076701952547 29521451527069615052928821)
                  ·
                    refine ⟨2767636080662776411212077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29521451527069615052928821 2767636080662776411212077)
                    ·
                      refine ⟨1037863530248541154204529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2767636080662776411212077 1037863530248541154204529)
                      ·
                        rfl

theorem cell23_2021232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 3].length) (baseStart_2021232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021232 prefixEnd_2021232 := by exact prefixLift 2021232
  have htrace : WordTrace (prefixWord ++ tailWord_2021232) baseStart_2021232 baseEnd_2021232 := by
    simpa [prefixWord, tailWord_2021232, baseEnd_2021232] using wordTrace_append hprefix tailTrace_2021232
  have hstable : (prefixWord ++ tailWord_2021232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021232).length < 2 ^ (prefixWord ++ tailWord_2021232).sum := by decide
  have hdescent : baseEnd_2021232 < baseStart_2021232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021252 : List Nat := [2, 3, 2, 1, 1, 1, 2, 3, 1, 7]
def baseStart_2021252 : Nat := 118140960795 + 2021252 * 2 ^ 59
def prefixEnd_2021252 : Nat := 4983230072969 + 3 ^ 40 * 2021252 * 2
def baseEnd_2021252 : Nat := 345957933287210358651479

theorem tailTrace_2021252 : CollatzResearch.WordTrace tailWord_2021252 prefixEnd_2021252 345957933287210358651479 := by
  unfold tailWord_2021252
  simp only [CollatzResearch.WordTrace]
  refine ⟨36860558436678340601873005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49147411248904454135830673 36860558436678340601873005)
  ·
    refine ⟨13822709413754377725702377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36860558436678340601873005 13822709413754377725702377)
    ·
      refine ⟨10367032060315783294276783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13822709413754377725702377 10367032060315783294276783)
      ·
        refine ⟨15550548090473674941415175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10367032060315783294276783 15550548090473674941415175)
        ·
          refine ⟨23325822135710512412122763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15550548090473674941415175 23325822135710512412122763)
          ·
            refine ⟨34988733203565768618184145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23325822135710512412122763 34988733203565768618184145)
            ·
              refine ⟨26241549902674326463638109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34988733203565768618184145 26241549902674326463638109)
              ·
                refine ⟨9840581213502872423864291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26241549902674326463638109 9840581213502872423864291)
                ·
                  refine ⟨14760871820254308635796437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9840581213502872423864291 14760871820254308635796437)
                  ·
                    refine ⟨345957933287210358651479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14760871820254308635796437 345957933287210358651479)
                    ·
                      rfl

theorem cell23_2021252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_2021252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021252 prefixEnd_2021252 := by exact prefixLift 2021252
  have htrace : WordTrace (prefixWord ++ tailWord_2021252) baseStart_2021252 baseEnd_2021252 := by
    simpa [prefixWord, tailWord_2021252, baseEnd_2021252] using wordTrace_append hprefix tailTrace_2021252
  have hstable : (prefixWord ++ tailWord_2021252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021252).length < 2 ^ (prefixWord ++ tailWord_2021252).sum := by decide
  have hdescent : baseEnd_2021252 < baseStart_2021252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021276 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 2, 5, 2]
def baseStart_2021276 : Nat := 118140960795 + 2021276 * 2 ^ 59
def prefixEnd_2021276 : Nat := 4983230072969 + 3 ^ 40 * 2021276 * 2
def baseEnd_2021276 : Nat := 1037886123397338982054327

theorem tailTrace_2021276 : CollatzResearch.WordTrace tailWord_2021276 prefixEnd_2021276 1037886123397338982054327 := by
  unfold tailWord_2021276
  simp only [CollatzResearch.WordTrace]
  refine ⟨36860996112634866651309841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49147994816846488868413121 36860996112634866651309841)
  ·
    refine ⟨27645747084476149988482381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36860996112634866651309841 27645747084476149988482381)
    ·
      refine ⟨10367155156678556245680893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27645747084476149988482381 10367155156678556245680893)
      ·
        refine ⟨3887683183754458592130335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10367155156678556245680893 3887683183754458592130335)
        ·
          refine ⟨5831524775631687888195503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3887683183754458592130335 5831524775631687888195503)
          ·
            refine ⟨8747287163447531832293255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5831524775631687888195503 8747287163447531832293255)
            ·
              refine ⟨13120930745171297748439883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8747287163447531832293255 13120930745171297748439883)
              ·
                refine ⟨19681396117756946622659825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13120930745171297748439883 19681396117756946622659825)
                ·
                  refine ⟨14761047088317709966994869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19681396117756946622659825 14761047088317709966994869)
                  ·
                    refine ⟨1383848164529785309405769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14761047088317709966994869 1383848164529785309405769)
                    ·
                      refine ⟨1037886123397338982054327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1383848164529785309405769 1037886123397338982054327)
                      ·
                        rfl

theorem cell23_2021276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_2021276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021276 prefixEnd_2021276 := by exact prefixLift 2021276
  have htrace : WordTrace (prefixWord ++ tailWord_2021276) baseStart_2021276 baseEnd_2021276 := by
    simpa [prefixWord, tailWord_2021276, baseEnd_2021276] using wordTrace_append hprefix tailTrace_2021276
  have hstable : (prefixWord ++ tailWord_2021276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021276).length < 2 ^ (prefixWord ++ tailWord_2021276).sum := by decide
  have hdescent : baseEnd_2021276 < baseStart_2021276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021299 : List Nat := [1, 1, 1, 2, 3, 1, 5, 2, 3, 4]
def baseStart_2021299 : Nat := 118140960795 + 2021299 * 2 ^ 59
def prefixEnd_2021299 : Nat := 4983230072969 + 3 ^ 40 * 2021299 * 2
def baseEnd_2021299 : Nat := 345965977817464130688907

theorem tailTrace_2021299 : CollatzResearch.WordTrace tailWord_2021299 prefixEnd_2021299 345965977817464130688907 := by
  unfold tailWord_2021299
  simp only [CollatzResearch.WordTrace]
  refine ⟨73722831104186408230706951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49148554069457605487137967 73722831104186408230706951)
  ·
    refine ⟨110584246656279612346060427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73722831104186408230706951 110584246656279612346060427)
    ·
      refine ⟨165876369984419418519090641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110584246656279612346060427 165876369984419418519090641)
      ·
        refine ⟨124407277488314563889317981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165876369984419418519090641 124407277488314563889317981)
        ·
          refine ⟨46652729058117961458494243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124407277488314563889317981 46652729058117961458494243)
          ·
            refine ⟨69979093587176942187741365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46652729058117961458494243 69979093587176942187741365)
            ·
              refine ⟨6560540023797838330100753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69979093587176942187741365 6560540023797838330100753)
              ·
                refine ⟨4920405017848378747575565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6560540023797838330100753 4920405017848378747575565)
                ·
                  refine ⟨1845151881693142030340837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4920405017848378747575565 1845151881693142030340837)
                  ·
                    refine ⟨345965977817464130688907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1845151881693142030340837 345965977817464130688907)
                    ·
                      rfl

theorem cell23_2021299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3, 4].length) (baseStart_2021299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021299 prefixEnd_2021299 := by exact prefixLift 2021299
  have htrace : WordTrace (prefixWord ++ tailWord_2021299) baseStart_2021299 baseEnd_2021299 := by
    simpa [prefixWord, tailWord_2021299, baseEnd_2021299] using wordTrace_append hprefix tailTrace_2021299
  have hstable : (prefixWord ++ tailWord_2021299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021299).length < 2 ^ (prefixWord ++ tailWord_2021299).sum := by decide
  have hdescent : baseEnd_2021299 < baseStart_2021299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021312 : List Nat := [2, 1, 1, 2, 3, 2, 2, 2, 8]
def baseStart_2021312 : Nat := 118140960795 + 2021312 * 2 ^ 59
def prefixEnd_2021312 : Nat := 4983230072969 + 3 ^ 40 * 2021312 * 2
def baseEnd_2021312 : Nat := 115322734300100093467129

theorem tailTrace_2021312 : CollatzResearch.WordTrace tailWord_2021312 prefixEnd_2021312 115322734300100093467129 := by
  unfold tailWord_2021312
  simp only [CollatzResearch.WordTrace]
  refine ⟨36861652626569655725465095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49148870168759540967286793 36861652626569655725465095)
  ·
    refine ⟨55292478939854483588197643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36861652626569655725465095 55292478939854483588197643)
    ·
      refine ⟨82938718409781725382296465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55292478939854483588197643 82938718409781725382296465)
      ·
        refine ⟨62204038807336294036722349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82938718409781725382296465 62204038807336294036722349)
        ·
          refine ⟨23326514552751110263770881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62204038807336294036722349 23326514552751110263770881)
          ·
            refine ⟨17494885914563332697828161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23326514552751110263770881 17494885914563332697828161)
            ·
              refine ⟨13121164435922499523371121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17494885914563332697828161 13121164435922499523371121)
              ·
                refine ⟨9840873326941874642528341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13121164435922499523371121 9840873326941874642528341)
                ·
                  refine ⟨115322734300100093467129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9840873326941874642528341 115322734300100093467129)
                  ·
                    rfl

theorem cell23_2021312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 8].length) (baseStart_2021312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021312 prefixEnd_2021312 := by exact prefixLift 2021312
  have htrace : WordTrace (prefixWord ++ tailWord_2021312) baseStart_2021312 baseEnd_2021312 := by
    simpa [prefixWord, tailWord_2021312, baseEnd_2021312] using wordTrace_append hprefix tailTrace_2021312
  have hstable : (prefixWord ++ tailWord_2021312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021312).length < 2 ^ (prefixWord ++ tailWord_2021312).sum := by decide
  have hdescent : baseEnd_2021312 < baseStart_2021312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021333 : List Nat := [1, 3, 2, 3, 2, 1, 2, 4, 1, 4]
def baseStart_2021333 : Nat := 118140960795 + 2021333 * 2 ^ 59
def prefixEnd_2021333 : Nat := 4983230072969 + 3 ^ 40 * 2021333 * 2
def baseEnd_2021333 : Nat := 345971797264881753013855

theorem tailTrace_2021333 : CollatzResearch.WordTrace tailWord_2021333 prefixEnd_2021333 345971797264881753013855 := by
  unfold tailWord_2021333
  simp only [CollatzResearch.WordTrace]
  refine ⟨73724071186063232037444653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49149380790708821358296435 73724071186063232037444653)
  ·
    refine ⟨27646526694773712014041745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73724071186063232037444653 27646526694773712014041745)
    ·
      refine ⟨20734895021080284010531309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27646526694773712014041745 20734895021080284010531309)
      ·
        refine ⟨7775585632905106503949241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20734895021080284010531309 7775585632905106503949241)
        ·
          refine ⟨5831689224678829877961931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7775585632905106503949241 5831689224678829877961931)
          ·
            refine ⟨8747533837018244816942897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5831689224678829877961931 8747533837018244816942897)
            ·
              refine ⟨6560650377763683612707173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8747533837018244816942897 6560650377763683612707173)
              ·
                refine ⟨1230121945830690677382595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6560650377763683612707173 1230121945830690677382595)
                ·
                  refine ⟨1845182918746036016073893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1230121945830690677382595 1845182918746036016073893)
                  ·
                    refine ⟨345971797264881753013855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1845182918746036016073893 345971797264881753013855)
                    ·
                      rfl

theorem cell23_2021333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_2021333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021333 prefixEnd_2021333 := by exact prefixLift 2021333
  have htrace : WordTrace (prefixWord ++ tailWord_2021333) baseStart_2021333 baseEnd_2021333 := by
    simpa [prefixWord, tailWord_2021333, baseEnd_2021333] using wordTrace_append hprefix tailTrace_2021333
  have hstable : (prefixWord ++ tailWord_2021333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021333).length < 2 ^ (prefixWord ++ tailWord_2021333).sum := by decide
  have hdescent : baseEnd_2021333 < baseStart_2021333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021383 : List Nat := [1, 1, 4, 3, 1, 3, 1, 2, 2, 3, 2]
def baseStart_2021383 : Nat := 118140960795 + 2021383 * 2 ^ 59
def prefixEnd_2021383 : Nat := 4983230072969 + 3 ^ 40 * 2021383 * 2
def baseEnd_2021383 : Nat := 1037941065827370063416335

theorem tailTrace_2021383 : CollatzResearch.WordTrace tailWord_2021383 prefixEnd_2021383 1037941065827370063416335 := by
  unfold tailWord_2021383
  simp only [CollatzResearch.WordTrace]
  refine ⟨73725894835882090576764803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49150596557254727051176535 73725894835882090576764803)
  ·
    refine ⟨110588842253823135865147205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73725894835882090576764803 110588842253823135865147205)
    ·
      refine ⟨20735407922591837974715101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110588842253823135865147205 20735407922591837974715101)
      ·
        refine ⟨7775777970971939240518163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20735407922591837974715101 7775777970971939240518163)
        ·
          refine ⟨11663666956457908860777245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7775777970971939240518163 11663666956457908860777245)
          ·
            refine ⟨4373875108671715822791467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11663666956457908860777245 4373875108671715822791467)
            ·
              refine ⟨6560812663007573734187201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4373875108671715822791467 6560812663007573734187201)
              ·
                refine ⟨4920609497255680300640401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6560812663007573734187201 4920609497255680300640401)
                ·
                  refine ⟨3690457122941760225480301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4920609497255680300640401 3690457122941760225480301)
                  ·
                    refine ⟨1383921421103160084555113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3690457122941760225480301 1383921421103160084555113)
                    ·
                      refine ⟨1037941065827370063416335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1383921421103160084555113 1037941065827370063416335)
                      ·
                        rfl

theorem cell23_2021383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_2021383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021383 prefixEnd_2021383 := by exact prefixLift 2021383
  have htrace : WordTrace (prefixWord ++ tailWord_2021383) baseStart_2021383 baseEnd_2021383 := by
    simpa [prefixWord, tailWord_2021383, baseEnd_2021383] using wordTrace_append hprefix tailTrace_2021383
  have hstable : (prefixWord ++ tailWord_2021383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021383).length < 2 ^ (prefixWord ++ tailWord_2021383).sum := by decide
  have hdescent : baseEnd_2021383 < baseStart_2021383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021413 : List Nat := [1, 3, 1, 2, 2, 5, 1, 2, 1, 1, 4]
def baseStart_2021413 : Nat := 118140960795 + 2021413 * 2 ^ 59
def prefixEnd_2021413 : Nat := 4983230072969 + 3 ^ 40 * 2021413 * 2
def baseEnd_2021413 : Nat := 1037956470247004946041197

theorem tailTrace_2021413 : CollatzResearch.WordTrace tailWord_2021413 prefixEnd_2021413 1037956470247004946041197 := by
  unfold tailWord_2021413
  simp only [CollatzResearch.WordTrace]
  refine ⟨73726989025773405700356893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49151326017182270466904595 73726989025773405700356893)
  ·
    refine ⟨27647620884665027137633835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73726989025773405700356893 27647620884665027137633835)
    ·
      refine ⟨41471431326997540706450753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27647620884665027137633835 41471431326997540706450753)
      ·
        refine ⟨31103573495248155529838065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41471431326997540706450753 31103573495248155529838065)
        ·
          refine ⟨23327680121436116647378549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31103573495248155529838065 23327680121436116647378549)
          ·
            refine ⟨2186970011384635935691739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23327680121436116647378549 2186970011384635935691739)
            ·
              refine ⟨3280455017076953903537609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2186970011384635935691739 3280455017076953903537609)
              ·
                refine ⟨2460341262807715427653207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3280455017076953903537609 2460341262807715427653207)
                ·
                  refine ⟨3690511894211573141479811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2460341262807715427653207 3690511894211573141479811)
                  ·
                    refine ⟨5535767841317359712219717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3690511894211573141479811 5535767841317359712219717)
                    ·
                      refine ⟨1037956470247004946041197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5535767841317359712219717 1037956470247004946041197)
                      ·
                        rfl

theorem cell23_2021413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_2021413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021413 prefixEnd_2021413 := by exact prefixLift 2021413
  have htrace : WordTrace (prefixWord ++ tailWord_2021413) baseStart_2021413 baseEnd_2021413 := by
    simpa [prefixWord, tailWord_2021413, baseEnd_2021413] using wordTrace_append hprefix tailTrace_2021413
  have hstable : (prefixWord ++ tailWord_2021413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021413).length < 2 ^ (prefixWord ++ tailWord_2021413).sum := by decide
  have hdescent : baseEnd_2021413 < baseStart_2021413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021426 : List Nat := [3, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4]
def baseStart_2021426 : Nat := 118140960795 + 2021426 * 2 ^ 59
def prefixEnd_2021426 : Nat := 4983230072969 + 3 ^ 40 * 2021426 * 2
def baseEnd_2021426 : Nat := 1037963145495513395178637

theorem tailTrace_2021426 : CollatzResearch.WordTrace tailWord_2021426 prefixEnd_2021426 1037963145495513395178637 := by
  unfold tailWord_2021426
  simp only [CollatzResearch.WordTrace]
  refine ⟨18431865793681577230145033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49151642116484205947053421 18431865793681577230145033)
  ·
    refine ⟨13823899345261182922608775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18431865793681577230145033 13823899345261182922608775)
    ·
      refine ⟨20735849017891774383913163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13823899345261182922608775 20735849017891774383913163)
      ·
        refine ⟨31103773526837661575869745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20735849017891774383913163 31103773526837661575869745)
        ·
          refine ⟨23327830145128246181902309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31103773526837661575869745 23327830145128246181902309)
          ·
            refine ⟨4373968152211546159106683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23327830145128246181902309 4373968152211546159106683)
            ·
              refine ⟨6560952228317319238660025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4373968152211546159106683 6560952228317319238660025)
              ·
                refine ⟨4920714171237989428995019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6560952228317319238660025 4920714171237989428995019)
                ·
                  refine ⟨7381071256856984143492529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4920714171237989428995019 7381071256856984143492529)
                  ·
                    refine ⟨5535803442642738107619397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7381071256856984143492529 5535803442642738107619397)
                    ·
                      refine ⟨1037963145495513395178637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5535803442642738107619397 1037963145495513395178637)
                      ·
                        rfl

theorem cell23_2021426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_2021426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021426 prefixEnd_2021426 := by exact prefixLift 2021426
  have htrace : WordTrace (prefixWord ++ tailWord_2021426) baseStart_2021426 baseEnd_2021426 := by
    simpa [prefixWord, tailWord_2021426, baseEnd_2021426] using wordTrace_append hprefix tailTrace_2021426
  have hstable : (prefixWord ++ tailWord_2021426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021426).length < 2 ^ (prefixWord ++ tailWord_2021426).sum := by decide
  have hdescent : baseEnd_2021426 < baseStart_2021426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021430 : List Nat := [5, 1, 2, 1, 1, 1, 5, 1, 1, 1, 4]
def baseStart_2021430 : Nat := 118140960795 + 2021430 * 2 ^ 59
def prefixEnd_2021430 : Nat := 4983230072969 + 3 ^ 40 * 2021430 * 2
def baseEnd_2021430 : Nat := 1037965199418131379528619

theorem tailTrace_2021430 : CollatzResearch.WordTrace tailWord_2021430 prefixEnd_2021430 1037965199418131379528619 := by
  unfold tailWord_2021430
  simp only [CollatzResearch.WordTrace]
  refine ⟨4607975566669488600232859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49151739377807878402483829 4607975566669488600232859)
  ·
    refine ⟨6911963350004232900349289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4607975566669488600232859 6911963350004232900349289)
    ·
      refine ⟨5183972512503174675261967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6911963350004232900349289 5183972512503174675261967)
      ·
        refine ⟨7775958768754762012892951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5183972512503174675261967 7775958768754762012892951)
        ·
          refine ⟨11663938153132143019339427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7775958768754762012892951 11663938153132143019339427)
          ·
            refine ⟨17495907229698214529009141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11663938153132143019339427 17495907229698214529009141)
            ·
              refine ⟨1640241302784207612094607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17495907229698214529009141 1640241302784207612094607)
              ·
                refine ⟨2460361954176311418141911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1640241302784207612094607 2460361954176311418141911)
                ·
                  refine ⟨3690542931264467127212867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2460361954176311418141911 3690542931264467127212867)
                  ·
                    refine ⟨5535814396896700690819301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3690542931264467127212867 5535814396896700690819301)
                    ·
                      refine ⟨1037965199418131379528619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5535814396896700690819301 1037965199418131379528619)
                      ·
                        rfl

theorem cell23_2021430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_2021430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021430 prefixEnd_2021430 := by exact prefixLift 2021430
  have htrace : WordTrace (prefixWord ++ tailWord_2021430) baseStart_2021430 baseEnd_2021430 := by
    simpa [prefixWord, tailWord_2021430, baseEnd_2021430] using wordTrace_append hprefix tailTrace_2021430
  have hstable : (prefixWord ++ tailWord_2021430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021430).length < 2 ^ (prefixWord ++ tailWord_2021430).sum := by decide
  have hdescent : baseEnd_2021430 < baseStart_2021430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021433 : List Nat := [1, 2, 1, 5, 3, 2, 1, 1, 1, 1, 5]
def baseStart_2021433 : Nat := 118140960795 + 2021433 * 2 ^ 59
def prefixEnd_2021433 : Nat := 4983230072969 + 3 ^ 40 * 2021433 * 2
def baseEnd_2021433 : Nat := 1037966739860094867791105

theorem tailTrace_2021433 : CollatzResearch.WordTrace tailWord_2021433 prefixEnd_2021433 1037966739860094867791105 := by
  unfold tailWord_2021433
  simp only [CollatzResearch.WordTrace]
  refine ⟨73727718485700949116084953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49151812323800632744056635 73727718485700949116084953)
  ·
    refine ⟨55295788864275711837063715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73727718485700949116084953 55295788864275711837063715)
    ·
      refine ⟨82943683296413567755595573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55295788864275711837063715 82943683296413567755595573)
      ·
        refine ⟨7775970309038771977087085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82943683296413567755595573 7775970309038771977087085)
        ·
          refine ⟨2915988865889539491407657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7775970309038771977087085 2915988865889539491407657)
          ·
            refine ⟨2186991649417154618555743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2915988865889539491407657 2186991649417154618555743)
            ·
              refine ⟨3280487474125731927833615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2186991649417154618555743 3280487474125731927833615)
              ·
                refine ⟨4920731211188597891750423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3280487474125731927833615 4920731211188597891750423)
                ·
                  refine ⟨7381096816782896837625635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4920731211188597891750423 7381096816782896837625635)
                  ·
                    refine ⟨11071645225174345256438453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7381096816782896837625635 11071645225174345256438453)
                    ·
                      refine ⟨1037966739860094867791105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11071645225174345256438453 1037966739860094867791105)
                      ·
                        rfl

theorem cell23_2021433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_2021433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021433 prefixEnd_2021433 := by exact prefixLift 2021433
  have htrace : WordTrace (prefixWord ++ tailWord_2021433) baseStart_2021433 baseEnd_2021433 := by
    simpa [prefixWord, tailWord_2021433, baseEnd_2021433] using wordTrace_append hprefix tailTrace_2021433
  have hstable : (prefixWord ++ tailWord_2021433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021433).length < 2 ^ (prefixWord ++ tailWord_2021433).sum := by decide
  have hdescent : baseEnd_2021433 < baseStart_2021433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021463 : List Nat := [1, 1, 3, 2, 2, 1, 4, 3, 2, 1, 3]
def baseStart_2021463 : Nat := 118140960795 + 2021463 * 2 ^ 59
def prefixEnd_2021463 : Nat := 4983230072969 + 3 ^ 40 * 2021463 * 2
def baseEnd_2021463 : Nat := 1037982144279729750415967

theorem tailTrace_2021463 : CollatzResearch.WordTrace tailWord_2021463 prefixEnd_2021463 1037982144279729750415967 := by
  unfold tailWord_2021463
  simp only [CollatzResearch.WordTrace]
  refine ⟨73728812675592264239677043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49152541783728176159784695 73728812675592264239677043)
  ·
    refine ⟨110593219013388396359515565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73728812675592264239677043 110593219013388396359515565)
    ·
      refine ⟨41472457130020648634818337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110593219013388396359515565 41472457130020648634818337)
      ·
        refine ⟨31104342847515486476113753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41472457130020648634818337 31104342847515486476113753)
        ·
          refine ⟨23328257135636614857085315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31104342847515486476113753 23328257135636614857085315)
          ·
            refine ⟨34992385703454922285627973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23328257135636614857085315 34992385703454922285627973)
            ·
              refine ⟨6561072319397797928555245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34992385703454922285627973 6561072319397797928555245)
              ·
                refine ⟨2460402119774174223208217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6561072319397797928555245 2460402119774174223208217)
                ·
                  refine ⟨1845301589830630667406163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2460402119774174223208217 1845301589830630667406163)
                  ·
                    refine ⟨2767952384745946001109245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1845301589830630667406163 2767952384745946001109245)
                    ·
                      refine ⟨1037982144279729750415967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2767952384745946001109245 1037982144279729750415967)
                      ·
                        rfl

theorem cell23_2021463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_2021463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021463 prefixEnd_2021463 := by exact prefixLift 2021463
  have htrace : WordTrace (prefixWord ++ tailWord_2021463) baseStart_2021463 baseEnd_2021463 := by
    simpa [prefixWord, tailWord_2021463, baseEnd_2021463] using wordTrace_append hprefix tailTrace_2021463
  have hstable : (prefixWord ++ tailWord_2021463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021463).length < 2 ^ (prefixWord ++ tailWord_2021463).sum := by decide
  have hdescent : baseEnd_2021463 < baseStart_2021463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021473 : List Nat := [1, 2, 3, 1, 1, 2, 1, 6, 1, 3, 2]
def baseStart_2021473 : Nat := 118140960795 + 2021473 * 2 ^ 59
def prefixEnd_2021473 : Nat := 4983230072969 + 3 ^ 40 * 2021473 * 2
def baseEnd_2021473 : Nat := 1037987279086274711290921

theorem tailTrace_2021473 : CollatzResearch.WordTrace tailWord_2021473 prefixEnd_2021473 1037987279086274711290921 := by
  unfold tailWord_2021473
  simp only [CollatzResearch.WordTrace]
  refine ⟨73729177405556035947541073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49152784937037357298360715 73729177405556035947541073)
  ·
    refine ⟨55296883054167026960655805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73729177405556035947541073 55296883054167026960655805)
    ·
      refine ⟨20736331145312635110245927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55296883054167026960655805 20736331145312635110245927)
      ·
        refine ⟨31104496717968952665368891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20736331145312635110245927 31104496717968952665368891)
        ·
          refine ⟨46656745076953428998053337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31104496717968952665368891 46656745076953428998053337)
          ·
            refine ⟨34992558807715071748540003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46656745076953428998053337 34992558807715071748540003)
            ·
              refine ⟨52488838211572607622810005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34992558807715071748540003 52488838211572607622810005)
              ·
                refine ⟨2460414291167465982319219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52488838211572607622810005 2460414291167465982319219)
                ·
                  refine ⟨3690621436751198973478829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2460414291167465982319219 3690621436751198973478829)
                  ·
                    refine ⟨1383983038781699615054561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3690621436751198973478829 1383983038781699615054561)
                    ·
                      refine ⟨1037987279086274711290921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1383983038781699615054561 1037987279086274711290921)
                      ·
                        rfl

theorem cell23_2021473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 3, 2].length) (baseStart_2021473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021473 prefixEnd_2021473 := by exact prefixLift 2021473
  have htrace : WordTrace (prefixWord ++ tailWord_2021473) baseStart_2021473 baseEnd_2021473 := by
    simpa [prefixWord, tailWord_2021473, baseEnd_2021473] using wordTrace_append hprefix tailTrace_2021473
  have hstable : (prefixWord ++ tailWord_2021473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021473).length < 2 ^ (prefixWord ++ tailWord_2021473).sum := by decide
  have hdescent : baseEnd_2021473 < baseStart_2021473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021479 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 1, 8]
def baseStart_2021479 : Nat := 118140960795 + 2021479 * 2 ^ 59
def prefixEnd_2021479 : Nat := 4983230072969 + 3 ^ 40 * 2021479 * 2
def baseEnd_2021479 : Nat := 345996786656733895938631

theorem tailTrace_2021479 : CollatzResearch.WordTrace tailWord_2021479 prefixEnd_2021479 345996786656733895938631 := by
  unfold tailWord_2021479
  simp only [CollatzResearch.WordTrace]
  refine ⟨73729396243534298972259491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49152930829022865981506327 73729396243534298972259491)
  ·
    refine ⟨110594094365301448458389237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73729396243534298972259491 110594094365301448458389237)
    ·
      refine ⟨10368196346747010792973991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110594094365301448458389237 10368196346747010792973991)
      ·
        refine ⟨15552294520120516189460987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10368196346747010792973991 15552294520120516189460987)
        ·
          refine ⟨23328441780180774284191481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15552294520120516189460987 23328441780180774284191481)
          ·
            refine ⟨17496331335135580713143611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23328441780180774284191481 17496331335135580713143611)
            ·
              refine ⟨26244497002703371069715417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17496331335135580713143611 26244497002703371069715417)
              ·
                refine ⟨19683372752027528302286563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26244497002703371069715417 19683372752027528302286563)
                ·
                  refine ⟨29525059128041292453429845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19683372752027528302286563 29525059128041292453429845)
                  ·
                    refine ⟨345996786656733895938631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29525059128041292453429845 345996786656733895938631)
                    ·
                      rfl

theorem cell23_2021479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_2021479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021479 prefixEnd_2021479 := by exact prefixLift 2021479
  have htrace : WordTrace (prefixWord ++ tailWord_2021479) baseStart_2021479 baseEnd_2021479 := by
    simpa [prefixWord, tailWord_2021479, baseEnd_2021479] using wordTrace_append hprefix tailTrace_2021479
  have hstable : (prefixWord ++ tailWord_2021479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021479).length < 2 ^ (prefixWord ++ tailWord_2021479).sum := by decide
  have hdescent : baseEnd_2021479 < baseStart_2021479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021489 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 1, 3, 5]
def baseStart_2021489 : Nat := 118140960795 + 2021489 * 2 ^ 59
def prefixEnd_2021489 : Nat := 4983230072969 + 3 ^ 40 * 2021489 * 2
def baseEnd_2021489 : Nat := 1037995494776746648690847

theorem tailTrace_2021489 : CollatzResearch.WordTrace tailWord_2021489 prefixEnd_2021489 1037995494776746648690847 := by
  unfold tailWord_2021489
  simp only [CollatzResearch.WordTrace]
  refine ⟨73729760973498070680123521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49153173982332047120082347 73729760973498070680123521)
  ·
    refine ⟨55297320730123553010092641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73729760973498070680123521 55297320730123553010092641)
    ·
      refine ⟨41472990547592664757569481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55297320730123553010092641 41472990547592664757569481)
      ·
        refine ⟨31104742910694498568177111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41472990547592664757569481 31104742910694498568177111)
        ·
          refine ⟨46657114366041747852265667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31104742910694498568177111 46657114366041747852265667)
          ·
            refine ⟨69985671549062621778398501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46657114366041747852265667 69985671549062621778398501)
            ·
              refine ⟨13122313415449241583449719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69985671549062621778398501 13122313415449241583449719)
              ·
                refine ⟨19683470123173862375174579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13122313415449241583449719 19683470123173862375174579)
                ·
                  refine ⟨29525205184760793562761869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19683470123173862375174579 29525205184760793562761869)
                  ·
                    refine ⟨11071951944285297586035701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29525205184760793562761869 11071951944285297586035701)
                    ·
                      refine ⟨1037995494776746648690847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11071951944285297586035701 1037995494776746648690847)
                      ·
                        rfl

theorem cell23_2021489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_2021489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021489 prefixEnd_2021489 := by exact prefixLift 2021489
  have htrace : WordTrace (prefixWord ++ tailWord_2021489) baseStart_2021489 baseEnd_2021489 := by
    simpa [prefixWord, tailWord_2021489, baseEnd_2021489] using wordTrace_append hprefix tailTrace_2021489
  have hstable : (prefixWord ++ tailWord_2021489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021489).length < 2 ^ (prefixWord ++ tailWord_2021489).sum := by decide
  have hdescent : baseEnd_2021489 < baseStart_2021489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021490 : List Nat := [3, 2, 1, 2, 2, 3, 1, 3, 1, 3, 2]
def baseStart_2021490 : Nat := 118140960795 + 2021490 * 2 ^ 59
def prefixEnd_2021490 : Nat := 4983230072969 + 3 ^ 40 * 2021490 * 2
def baseEnd_2021490 : Nat := 1037996008257401144778343

theorem tailTrace_2021490 : CollatzResearch.WordTrace tailWord_2021490 prefixEnd_2021490 1037996008257401144778343 := by
  unfold tailWord_2021490
  simp only [CollatzResearch.WordTrace]
  refine ⟨18432449361623611962727481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49153198297662965233939949 18432449361623611962727481)
  ·
    refine ⟨13824337021217708972045611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18432449361623611962727481 13824337021217708972045611)
    ·
      refine ⟨20736505531826563458068417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13824337021217708972045611 20736505531826563458068417)
      ·
        refine ⟨15552379148869922593551313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20736505531826563458068417 15552379148869922593551313)
        ·
          refine ⟨11664284361652441945163485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15552379148869922593551313 11664284361652441945163485)
          ·
            refine ⟨4374106635619665729436307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11664284361652441945163485 4374106635619665729436307)
            ·
              refine ⟨6561159953429498594154461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4374106635619665729436307 6561159953429498594154461)
              ·
                refine ⟨2460434982536061972807923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6561159953429498594154461 2460434982536061972807923)
                ·
                  refine ⟨3690652473804092959211885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2460434982536061972807923 3690652473804092959211885)
                  ·
                    refine ⟨1383994677676534859704457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3690652473804092959211885 1383994677676534859704457)
                    ·
                      refine ⟨1037996008257401144778343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1383994677676534859704457 1037996008257401144778343)
                      ·
                        rfl

theorem cell23_2021490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_2021490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021490 prefixEnd_2021490 := by exact prefixLift 2021490
  have htrace : WordTrace (prefixWord ++ tailWord_2021490) baseStart_2021490 baseEnd_2021490 := by
    simpa [prefixWord, tailWord_2021490, baseEnd_2021490] using wordTrace_append hprefix tailTrace_2021490
  have hstable : (prefixWord ++ tailWord_2021490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021490).length < 2 ^ (prefixWord ++ tailWord_2021490).sum := by decide
  have hdescent : baseEnd_2021490 < baseStart_2021490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021524 : List Nat := [2, 4, 2, 3, 1, 1, 2, 2, 1, 3, 2]
def baseStart_2021524 : Nat := 118140960795 + 2021524 * 2 ^ 59
def prefixEnd_2021524 : Nat := 4983230072969 + 3 ^ 40 * 2021524 * 2
def baseEnd_2021524 : Nat := 1038013466599654011753187

theorem tailTrace_2021524 : CollatzResearch.WordTrace tailWord_2021524 prefixEnd_2021524 1038013466599654011753187 := by
  unfold tailWord_2021524
  simp only [CollatzResearch.WordTrace]
  refine ⟨36865518764185635828823813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49154025018914181105098417 36865518764185635828823813)
  ·
    refine ⟨6912284768284806717904465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36865518764185635828823813 6912284768284806717904465)
    ·
      refine ⟨5184213576213605038428349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6912284768284806717904465 5184213576213605038428349)
      ·
        refine ⟨1944080091080101889410631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5184213576213605038428349 1944080091080101889410631)
        ·
          refine ⟨2916120136620152834115947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1944080091080101889410631 2916120136620152834115947)
          ·
            refine ⟨4374180204930229251173921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2916120136620152834115947 4374180204930229251173921)
            ·
              refine ⟨3280635153697671938380441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4374180204930229251173921 3280635153697671938380441)
              ·
                refine ⟨2460476365273253953785331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3280635153697671938380441 2460476365273253953785331)
                ·
                  refine ⟨3690714547909880930677997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2460476365273253953785331 3690714547909880930677997)
                  ·
                    refine ⟨1384017955466205349004249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3690714547909880930677997 1384017955466205349004249)
                    ·
                      refine ⟨1038013466599654011753187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1384017955466205349004249 1038013466599654011753187)
                      ·
                        rfl

theorem cell23_2021524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_2021524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021524 prefixEnd_2021524 := by exact prefixLift 2021524
  have htrace : WordTrace (prefixWord ++ tailWord_2021524) baseStart_2021524 baseEnd_2021524 := by
    simpa [prefixWord, tailWord_2021524, baseEnd_2021524] using wordTrace_append hprefix tailTrace_2021524
  have hstable : (prefixWord ++ tailWord_2021524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021524).length < 2 ^ (prefixWord ++ tailWord_2021524).sum := by decide
  have hdescent : baseEnd_2021524 < baseStart_2021524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021576 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 6, 1, 4]
def baseStart_2021576 : Nat := 118140960795 + 2021576 * 2 ^ 59
def prefixEnd_2021576 : Nat := 4983230072969 + 3 ^ 40 * 2021576 * 2
def baseEnd_2021576 : Nat := 1038040167593687808302947

theorem tailTrace_2021576 : CollatzResearch.WordTrace tailWord_2021576 prefixEnd_2021576 1038040167593687808302947 := by
  unfold tailWord_2021576
  simp only [CollatzResearch.WordTrace]
  refine ⟨36866467062091442269270291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49155289416121923025693721 36866467062091442269270291)
  ·
    refine ⟨55299700593137163403905437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36866467062091442269270291 55299700593137163403905437)
    ·
      refine ⟨20737387722426436276464539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55299700593137163403905437 20737387722426436276464539)
      ·
        refine ⟨31106081583639654414696809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20737387722426436276464539 31106081583639654414696809)
        ·
          refine ⟨23329561187729740811022607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31106081583639654414696809 23329561187729740811022607)
          ·
            refine ⟨34994341781594611216533911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23329561187729740811022607 34994341781594611216533911)
            ·
              refine ⟨52491512672391916824800867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34994341781594611216533911 52491512672391916824800867)
              ·
                refine ⟨78737269008587875237201301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52491512672391916824800867 78737269008587875237201301)
                ·
                  refine ⟨3690809484777556651743811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78737269008587875237201301 3690809484777556651743811)
                  ·
                    refine ⟨5536214227166334977615717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3690809484777556651743811 5536214227166334977615717)
                    ·
                      refine ⟨1038040167593687808302947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5536214227166334977615717 1038040167593687808302947)
                      ·
                        rfl

theorem cell23_2021576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_2021576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021576 prefixEnd_2021576 := by exact prefixLift 2021576
  have htrace : WordTrace (prefixWord ++ tailWord_2021576) baseStart_2021576 baseEnd_2021576 := by
    simpa [prefixWord, tailWord_2021576, baseEnd_2021576] using wordTrace_append hprefix tailTrace_2021576
  have hstable : (prefixWord ++ tailWord_2021576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021576).length < 2 ^ (prefixWord ++ tailWord_2021576).sum := by decide
  have hdescent : baseEnd_2021576 < baseStart_2021576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021590 : List Nat := [5, 2, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_2021590 : Nat := 118140960795 + 2021590 * 2 ^ 59
def prefixEnd_2021590 : Nat := 4983230072969 + 3 ^ 40 * 2021590 * 2
def baseEnd_2021590 : Nat := 346015785440950251175961

theorem tailTrace_2021590 : CollatzResearch.WordTrace tailWord_2021590 prefixEnd_2021590 346015785440950251175961 := by
  unfold tailWord_2021590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4608340296633260308096889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49155629830754776619700149 4608340296633260308096889)
  ·
    refine ⟨3456255222474945231072667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4608340296633260308096889 3456255222474945231072667)
    ·
      refine ⟨5184382833712417846609001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3456255222474945231072667 5184382833712417846609001)
      ·
        refine ⟨3888287125284313384956751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5184382833712417846609001 3888287125284313384956751)
        ·
          refine ⟨5832430687926470077435127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3888287125284313384956751 5832430687926470077435127)
          ·
            refine ⟨8748646031889705116152691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5832430687926470077435127 8748646031889705116152691)
            ·
              refine ⟨13122969047834557674229037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8748646031889705116152691 13122969047834557674229037)
              ·
                refine ⟨4921113392937959127835889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13122969047834557674229037 4921113392937959127835889)
                ·
                  refine ⟨3690835044703469345876917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4921113392937959127835889 3690835044703469345876917)
                  ·
                    refine ⟨346015785440950251175961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3690835044703469345876917 346015785440950251175961)
                    ·
                      rfl

theorem cell23_2021590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_2021590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021590 prefixEnd_2021590 := by exact prefixLift 2021590
  have htrace : WordTrace (prefixWord ++ tailWord_2021590) baseStart_2021590 baseEnd_2021590 := by
    simpa [prefixWord, tailWord_2021590, baseEnd_2021590] using wordTrace_append hprefix tailTrace_2021590
  have hstable : (prefixWord ++ tailWord_2021590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021590).length < 2 ^ (prefixWord ++ tailWord_2021590).sum := by decide
  have hdescent : baseEnd_2021590 < baseStart_2021590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021676 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 3, 6]
def baseStart_2021676 : Nat := 118140960795 + 2021676 * 2 ^ 59
def prefixEnd_2021676 : Nat := 4983230072969 + 3 ^ 40 * 2021676 * 2
def baseEnd_2021676 : Nat := 346030505219712472350829

theorem tailTrace_2021676 : CollatzResearch.WordTrace tailWord_2021676 prefixEnd_2021676 346030505219712472350829 := by
  unfold tailWord_2021676
  simp only [CollatzResearch.WordTrace]
  refine ⟨36868290711910300808590441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49157720949213734411453921 36868290711910300808590441)
  ·
    refine ⟨27651218033932725606442831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36868290711910300808590441 27651218033932725606442831)
    ·
      refine ⟨41476827050899088409664247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27651218033932725606442831 41476827050899088409664247)
      ·
        refine ⟨62215240576348632614496371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41476827050899088409664247 62215240576348632614496371)
        ·
          refine ⟨93322860864522948921744557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62215240576348632614496371 93322860864522948921744557)
          ·
            refine ⟨34996072824196105845654209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93322860864522948921744557 34996072824196105845654209)
            ·
              refine ⟨26247054618147079384240657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34996072824196105845654209 26247054618147079384240657)
              ·
                refine ⟨19685290963610309538180493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26247054618147079384240657 19685290963610309538180493)
                ·
                  refine ⟨7381984111353866076817685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19685290963610309538180493 7381984111353866076817685)
                  ·
                    refine ⟨346030505219712472350829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7381984111353866076817685 346030505219712472350829)
                    ·
                      rfl

theorem cell23_2021676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 6].length) (baseStart_2021676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021676 prefixEnd_2021676 := by exact prefixLift 2021676
  have htrace : WordTrace (prefixWord ++ tailWord_2021676) baseStart_2021676 baseEnd_2021676 := by
    simpa [prefixWord, tailWord_2021676, baseEnd_2021676] using wordTrace_append hprefix tailTrace_2021676
  have hstable : (prefixWord ++ tailWord_2021676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021676).length < 2 ^ (prefixWord ++ tailWord_2021676).sum := by decide
  have hdescent : baseEnd_2021676 < baseStart_2021676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021697 : List Nat := [1, 2, 5, 2, 2, 1, 2, 2, 1, 5]
def baseStart_2021697 : Nat := 118140960795 + 2021697 * 2 ^ 59
def prefixEnd_2021697 : Nat := 4983230072969 + 3 ^ 40 * 2021697 * 2
def baseEnd_2021697 : Nat := 346034099584293944963297

theorem tailTrace_2021697 : CollatzResearch.WordTrace tailWord_2021697 prefixEnd_2021697 346034099584293944963297 := by
  unfold tailWord_2021697
  simp only [CollatzResearch.WordTrace]
  refine ⟨73737347356744522203695345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49158231571163014802463563 73737347356744522203695345)
  ·
    refine ⟨55303010517558391652771509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73737347356744522203695345 55303010517558391652771509)
    ·
      refine ⟨5184657236021099217447329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55303010517558391652771509 5184657236021099217447329)
      ·
        refine ⟨3888492927015824413085497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5184657236021099217447329 3888492927015824413085497)
        ·
          refine ⟨2916369695261868309814123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3888492927015824413085497 2916369695261868309814123)
          ·
            refine ⟨4374554542892802464721185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2916369695261868309814123 4374554542892802464721185)
            ·
              refine ⟨3280915907169601848540889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4374554542892802464721185 3280915907169601848540889)
              ·
                refine ⟨2460686930377201386405667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3280915907169601848540889 2460686930377201386405667)
                ·
                  refine ⟨3691030395565802079608501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2460686930377201386405667 3691030395565802079608501)
                  ·
                    refine ⟨346034099584293944963297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3691030395565802079608501 346034099584293944963297)
                    ·
                      rfl

theorem cell23_2021697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_2021697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021697 prefixEnd_2021697 := by exact prefixLift 2021697
  have htrace : WordTrace (prefixWord ++ tailWord_2021697) baseStart_2021697 baseEnd_2021697 := by
    simpa [prefixWord, tailWord_2021697, baseEnd_2021697] using wordTrace_append hprefix tailTrace_2021697
  have hstable : (prefixWord ++ tailWord_2021697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021697).length < 2 ^ (prefixWord ++ tailWord_2021697).sum := by decide
  have hdescent : baseEnd_2021697 < baseStart_2021697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021784 : List Nat := [2, 1, 2, 5, 1, 2, 2, 2, 2, 1, 3]
def baseStart_2021784 : Nat := 118140960795 + 2021784 * 2 ^ 59
def prefixEnd_2021784 : Nat := 4983230072969 + 3 ^ 40 * 2021784 * 2
def baseEnd_2021784 : Nat := 1038146971569822994501991

theorem tailTrace_2021784 : CollatzResearch.WordTrace tailWord_2021784 prefixEnd_2021784 1038146971569822994501991 := by
  unfold tailWord_2021784
  simp only [CollatzResearch.WordTrace]
  refine ⟨36870260253714668031056203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49160347004952890708074937 36870260253714668031056203)
  ·
    refine ⟨55305390380572002046584305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36870260253714668031056203 55305390380572002046584305)
    ·
      refine ⟨41479042785429001534938229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55305390380572002046584305 41479042785429001534938229)
      ·
        refine ⟨3888660261133968893900459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41479042785429001534938229 3888660261133968893900459)
        ·
          refine ⟨5832990391700953340850689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3888660261133968893900459 5832990391700953340850689)
          ·
            refine ⟨4374742793775715005638017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5832990391700953340850689 4374742793775715005638017)
            ·
              refine ⟨3281057095331786254228513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4374742793775715005638017 3281057095331786254228513)
              ·
                refine ⟨2460792821498839690671385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3281057095331786254228513 2460792821498839690671385)
                ·
                  refine ⟨1845594616124129768003539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2460792821498839690671385 1845594616124129768003539)
                  ·
                    refine ⟨2768391924186194652005309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1845594616124129768003539 2768391924186194652005309)
                    ·
                      refine ⟨1038146971569822994501991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2768391924186194652005309 1038146971569822994501991)
                      ·
                        rfl

theorem cell23_2021784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_2021784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021784 prefixEnd_2021784 := by exact prefixLift 2021784
  have htrace : WordTrace (prefixWord ++ tailWord_2021784) baseStart_2021784 baseEnd_2021784 := by
    simpa [prefixWord, tailWord_2021784, baseEnd_2021784] using wordTrace_append hprefix tailTrace_2021784
  have hstable : (prefixWord ++ tailWord_2021784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021784).length < 2 ^ (prefixWord ++ tailWord_2021784).sum := by decide
  have hdescent : baseEnd_2021784 < baseStart_2021784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021800 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 1, 8]
def baseStart_2021800 : Nat := 118140960795 + 2021800 * 2 ^ 59
def prefixEnd_2021800 : Nat := 4983230072969 + 3 ^ 40 * 2021800 * 2
def baseEnd_2021800 : Nat := 346051729086764977300639

theorem tailTrace_2021800 : CollatzResearch.WordTrace tailWord_2021800 prefixEnd_2021800 346051729086764977300639 := by
  unfold tailWord_2021800
  simp only [CollatzResearch.WordTrace]
  refine ⟨36870552037685685397347427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49160736050247580529796569 36870552037685685397347427)
  ·
    refine ⟨55305828056528528096021141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36870552037685685397347427 55305828056528528096021141)
    ·
      refine ⟨2592460690149774754500991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 55305828056528528096021141 2592460690149774754500991)
      ·
        refine ⟨3888691035224662131751487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2592460690149774754500991 3888691035224662131751487)
        ·
          refine ⟨5833036552836993197627231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3888691035224662131751487 5833036552836993197627231)
          ·
            refine ⟨8749554829255489796440847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5833036552836993197627231 8749554829255489796440847)
            ·
              refine ⟨13124332243883234694661271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8749554829255489796440847 13124332243883234694661271)
              ·
                refine ⟨19686498365824852041991907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13124332243883234694661271 19686498365824852041991907)
                ·
                  refine ⟨29529747548737278062987861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19686498365824852041991907 29529747548737278062987861)
                  ·
                    refine ⟨346051729086764977300639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29529747548737278062987861 346051729086764977300639)
                    ·
                      rfl

theorem cell23_2021800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_2021800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021800 prefixEnd_2021800 := by exact prefixLift 2021800
  have htrace : WordTrace (prefixWord ++ tailWord_2021800) baseStart_2021800 baseEnd_2021800 := by
    simpa [prefixWord, tailWord_2021800, baseEnd_2021800] using wordTrace_append hprefix tailTrace_2021800
  have hstable : (prefixWord ++ tailWord_2021800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021800).length < 2 ^ (prefixWord ++ tailWord_2021800).sum := by decide
  have hdescent : baseEnd_2021800 < baseStart_2021800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021828 : List Nat := [2, 3, 3, 2, 2, 2, 2, 1, 1, 3, 2]
def baseStart_2021828 : Nat := 118140960795 + 2021828 * 2 ^ 59
def prefixEnd_2021828 : Nat := 4983230072969 + 3 ^ 40 * 2021828 * 2
def baseEnd_2021828 : Nat := 1038169564718620822351789

theorem tailTrace_2021828 : CollatzResearch.WordTrace tailWord_2021828 prefixEnd_2021828 1038169564718620822351789 := by
  unfold tailWord_2021828
  simp only [CollatzResearch.WordTrace]
  refine ⟨36871062659634965788357069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49161416879513287717809425 36871062659634965788357069)
  ·
    refine ⟨13826648497363112170633901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36871062659634965788357069 13826648497363112170633901)
    ·
      refine ⟨5184993186511167063987713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13826648497363112170633901 5184993186511167063987713)
      ·
        refine ⟨3888744889883375297990785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5184993186511167063987713 3888744889883375297990785)
        ·
          refine ⟨2916558667412531473493089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3888744889883375297990785 2916558667412531473493089)
          ·
            refine ⟨2187419000559398605119817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2916558667412531473493089 2187419000559398605119817)
            ·
              refine ⟨1640564250419548953839863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2187419000559398605119817 1640564250419548953839863)
              ·
                refine ⟨2460846375629323430759795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1640564250419548953839863 2460846375629323430759795)
                ·
                  refine ⟨3691269563443985146139693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2460846375629323430759795 3691269563443985146139693)
                  ·
                    refine ⟨1384226086291494429802385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3691269563443985146139693 1384226086291494429802385)
                    ·
                      refine ⟨1038169564718620822351789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1384226086291494429802385 1038169564718620822351789)
                      ·
                        rfl

theorem cell23_2021828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_2021828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021828 prefixEnd_2021828 := by exact prefixLift 2021828
  have htrace : WordTrace (prefixWord ++ tailWord_2021828) baseStart_2021828 baseEnd_2021828 := by
    simpa [prefixWord, tailWord_2021828, baseEnd_2021828] using wordTrace_append hprefix tailTrace_2021828
  have hstable : (prefixWord ++ tailWord_2021828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021828).length < 2 ^ (prefixWord ++ tailWord_2021828).sum := by decide
  have hdescent : baseEnd_2021828 < baseStart_2021828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021858 : List Nat := [3, 3, 3, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_2021858 : Nat := 118140960795 + 2021858 * 2 ^ 59
def prefixEnd_2021858 : Nat := 4983230072969 + 3 ^ 40 * 2021858 * 2
def baseEnd_2021858 : Nat := 1038184969138255704976651

theorem tailTrace_2021858 : CollatzResearch.WordTrace tailWord_2021858 prefixEnd_2021858 1038184969138255704976651 := by
  unfold tailWord_2021858
  simp only [CollatzResearch.WordTrace]
  refine ⟨18435804877290311675076557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49162146339440831133537485 18435804877290311675076557)
  ·
    refine ⟨6913426828983866878153709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18435804877290311675076557 6913426828983866878153709)
    ·
      refine ⟨2592535060868950079307641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6913426828983866878153709 2592535060868950079307641)
      ·
        refine ⟨1944401295651712559480731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2592535060868950079307641 1944401295651712559480731)
        ·
          refine ⟨2916601943477568839221097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1944401295651712559480731 2916601943477568839221097)
          ·
            refine ⟨2187451457608176629415823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2916601943477568839221097 2187451457608176629415823)
            ·
              refine ⟨3281177186412264944123735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2187451457608176629415823 3281177186412264944123735)
              ·
                refine ⟨4921765779618397416185603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3281177186412264944123735 4921765779618397416185603)
                ·
                  refine ⟨7382648669427596124278405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4921765779618397416185603 7382648669427596124278405)
                  ·
                    refine ⟨1384246625517674273302201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7382648669427596124278405 1384246625517674273302201)
                    ·
                      refine ⟨1038184969138255704976651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1384246625517674273302201 1038184969138255704976651)
                      ·
                        rfl

theorem cell23_2021858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_2021858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021858 prefixEnd_2021858 := by exact prefixLift 2021858
  have htrace : WordTrace (prefixWord ++ tailWord_2021858) baseStart_2021858 baseEnd_2021858 := by
    simpa [prefixWord, tailWord_2021858, baseEnd_2021858] using wordTrace_append hprefix tailTrace_2021858
  have hstable : (prefixWord ++ tailWord_2021858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021858).length < 2 ^ (prefixWord ++ tailWord_2021858).sum := by decide
  have hdescent : baseEnd_2021858 < baseStart_2021858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021873 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 2, 8]
def baseStart_2021873 : Nat := 118140960795 + 2021873 * 2 ^ 59
def prefixEnd_2021873 : Nat := 4983230072969 + 3 ^ 40 * 2021873 * 2
def baseEnd_2021873 : Nat := 346064223782691048763027

theorem tailTrace_2021873 : CollatzResearch.WordTrace tailWord_2021873 prefixEnd_2021873 346064223782691048763027 := by
  unfold tailWord_2021873
  simp only [CollatzResearch.WordTrace]
  refine ⟨73743766604106904262102273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49162511069404602841401515 73743766604106904262102273)
  ·
    refine ⟨55307824953080178196576705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73743766604106904262102273 55307824953080178196576705)
    ·
      refine ⟨41480868714810133647432529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55307824953080178196576705 41480868714810133647432529)
      ·
        refine ⟨31110651536107600235574397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41480868714810133647432529 31110651536107600235574397)
        ·
          refine ⟨11666494326040350088340399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31110651536107600235574397 11666494326040350088340399)
          ·
            refine ⟨17499741489060525132510599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11666494326040350088340399 17499741489060525132510599)
            ·
              refine ⟨26249612233590787698765899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17499741489060525132510599 26249612233590787698765899)
              ·
                refine ⟨39374418350386181548148849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26249612233590787698765899 39374418350386181548148849)
                ·
                  refine ⟨29530813762789636161111637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39374418350386181548148849 29530813762789636161111637)
                  ·
                    refine ⟨346064223782691048763027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29530813762789636161111637 346064223782691048763027)
                    ·
                      rfl

theorem cell23_2021873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_2021873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021873 prefixEnd_2021873 := by exact prefixLift 2021873
  have htrace : WordTrace (prefixWord ++ tailWord_2021873) baseStart_2021873 baseEnd_2021873 := by
    simpa [prefixWord, tailWord_2021873, baseEnd_2021873] using wordTrace_append hprefix tailTrace_2021873
  have hstable : (prefixWord ++ tailWord_2021873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021873).length < 2 ^ (prefixWord ++ tailWord_2021873).sum := by decide
  have hdescent : baseEnd_2021873 < baseStart_2021873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021880 : List Nat := [2, 1, 2, 1, 1, 4, 2, 3, 2, 1, 4]
def baseStart_2021880 : Nat := 118140960795 + 2021880 * 2 ^ 59
def prefixEnd_2021880 : Nat := 4983230072969 + 3 ^ 40 * 2021880 * 2
def baseEnd_2021880 : Nat := 1038196265712654618901549

theorem tailTrace_2021880 : CollatzResearch.WordTrace tailWord_2021880 prefixEnd_2021880 1038196265712654618901549 := by
  unfold tailWord_2021880
  simp only [CollatzResearch.WordTrace]
  refine ⟨36872010957540772228803547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49162681276721029638404729 36872010957540772228803547)
  ·
    refine ⟨55308016436311158343205321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36872010957540772228803547 55308016436311158343205321)
    ·
      refine ⟨41481012327233368757403991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55308016436311158343205321 41481012327233368757403991)
      ·
        refine ⟨62221518490850053136105987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41481012327233368757403991 62221518490850053136105987)
        ·
          refine ⟨93332277736275079704158981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62221518490850053136105987 93332277736275079704158981)
          ·
            refine ⟨17499802075551577444529809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93332277736275079704158981 17499802075551577444529809)
            ·
              refine ⟨13124851556663683083397357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17499802075551577444529809 13124851556663683083397357)
              ·
                refine ⟨4921819333748881156274009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13124851556663683083397357 4921819333748881156274009)
                ·
                  refine ⟨3691364500311660867205507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4921819333748881156274009 3691364500311660867205507)
                  ·
                    refine ⟨5537046750467491300808261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3691364500311660867205507 5537046750467491300808261)
                    ·
                      refine ⟨1038196265712654618901549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5537046750467491300808261 1038196265712654618901549)
                      ·
                        rfl

theorem cell23_2021880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_2021880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021880 prefixEnd_2021880 := by exact prefixLift 2021880
  have htrace : WordTrace (prefixWord ++ tailWord_2021880) baseStart_2021880 baseEnd_2021880 := by
    simpa [prefixWord, tailWord_2021880, baseEnd_2021880] using wordTrace_append hprefix tailTrace_2021880
  have hstable : (prefixWord ++ tailWord_2021880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021880).length < 2 ^ (prefixWord ++ tailWord_2021880).sum := by decide
  have hdescent : baseEnd_2021880 < baseStart_2021880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
