import V185TrunkScan23Chunk0629

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3725731 : List Nat := [1, 1, 1, 4, 1, 4, 2, 1, 1, 5, 2]
def baseStart_3725731 : Nat := 118140960795 + 3725731 * 2 ^ 59
def prefixEnd_3725731 : Nat := 4983230072969 + 3 ^ 40 * 3725731 * 2
def baseEnd_3725731 : Nat := 1913090792356467794028181

theorem tailTrace_3725731 : CollatzResearch.WordTrace tailWord_3725731 prefixEnd_3725731 1913090792356467794028181 := by
  unfold tailWord_3725731
  simp only [CollatzResearch.WordTrace]
  refine ⟨135888573265320366041145047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90592382176880244027430031 135888573265320366041145047)
  ·
    refine ⟨203832859897980549061717571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135888573265320366041145047 203832859897980549061717571)
    ·
      refine ⟨305749289846970823592576357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203832859897980549061717571 305749289846970823592576357)
      ·
        refine ⟨57327991846307029423608067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305749289846970823592576357 57327991846307029423608067)
        ·
          refine ⟨85991987769460544135412101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57327991846307029423608067 85991987769460544135412101)
          ·
            refine ⟨16123497706773852025389769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85991987769460544135412101 16123497706773852025389769)
            ·
              refine ⟨12092623280080389019042327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16123497706773852025389769 12092623280080389019042327)
              ·
                refine ⟨18138934920120583528563491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12092623280080389019042327 18138934920120583528563491)
                ·
                  refine ⟨27208402380180875292845237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18138934920120583528563491 27208402380180875292845237)
                  ·
                    refine ⟨2550787723141957058704241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27208402380180875292845237 2550787723141957058704241)
                    ·
                      refine ⟨1913090792356467794028181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2550787723141957058704241 1913090792356467794028181)
                      ·
                        rfl

theorem cell23_3725731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 5, 2].length) (baseStart_3725731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725731 prefixEnd_3725731 := by exact prefixLift 3725731
  have htrace : WordTrace (prefixWord ++ tailWord_3725731) baseStart_3725731 baseEnd_3725731 := by
    simpa [prefixWord, tailWord_3725731, baseEnd_3725731] using wordTrace_append hprefix tailTrace_3725731
  have hstable : (prefixWord ++ tailWord_3725731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725731).length < 2 ^ (prefixWord ++ tailWord_3725731).sum := by decide
  have hdescent : baseEnd_3725731 < baseStart_3725731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725791 : List Nat := [1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 4]
def baseStart_3725791 : Nat := 118140960795 + 3725791 * 2 ^ 59
def prefixEnd_3725791 : Nat := 4983230072969 + 3 ^ 40 * 3725791 * 2
def baseEnd_3725791 : Nat := 1913121601195737559277905

theorem tailTrace_3725791 : CollatzResearch.WordTrace tailWord_3725791 prefixEnd_3725791 1913121601195737559277905 := by
  unfold tailWord_3725791
  simp only [CollatzResearch.WordTrace]
  refine ⟨135890761645102996288329227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90593841096735330858886151 135890761645102996288329227)
  ·
    refine ⟨203836142467654494432493841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135890761645102996288329227 203836142467654494432493841)
    ·
      refine ⟨152877106850740870824370381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203836142467654494432493841 152877106850740870824370381)
      ·
        refine ⟨57328915069027826559138893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152877106850740870824370381 57328915069027826559138893)
        ·
          refine ⟨21498343150885434959677085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57328915069027826559138893 21498343150885434959677085)
          ·
            refine ⟨8061878681582038109878907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21498343150885434959677085 8061878681582038109878907)
            ·
              refine ⟨12092818022373057164818361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8061878681582038109878907 12092818022373057164818361)
              ·
                refine ⟨9069613516779792873613771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12092818022373057164818361 9069613516779792873613771)
                ·
                  refine ⟨13604420275169689310420657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9069613516779792873613771 13604420275169689310420657)
                  ·
                    refine ⟨10203315206377266982815493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13604420275169689310420657 10203315206377266982815493)
                    ·
                      refine ⟨1913121601195737559277905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10203315206377266982815493 1913121601195737559277905)
                      ·
                        rfl

theorem cell23_3725791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_3725791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725791 prefixEnd_3725791 := by exact prefixLift 3725791
  have htrace : WordTrace (prefixWord ++ tailWord_3725791) baseStart_3725791 baseEnd_3725791 := by
    simpa [prefixWord, tailWord_3725791, baseEnd_3725791] using wordTrace_append hprefix tailTrace_3725791
  have hstable : (prefixWord ++ tailWord_3725791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725791).length < 2 ^ (prefixWord ++ tailWord_3725791).sum := by decide
  have hdescent : baseEnd_3725791 < baseStart_3725791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725795 : List Nat := [1, 1, 1, 6, 3, 1, 3, 1, 1, 1, 4]
def baseStart_3725795 : Nat := 118140960795 + 3725795 * 2 ^ 59
def prefixEnd_3725795 : Nat := 4983230072969 + 3 ^ 40 * 3725795 * 2
def baseEnd_3725795 : Nat := 1913123655118355543627887

theorem tailTrace_3725795 : CollatzResearch.WordTrace tailWord_3725795 prefixEnd_3725795 1913123655118355543627887 := by
  unfold tailWord_3725795
  simp only [CollatzResearch.WordTrace]
  refine ⟨135890907537088504971474839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90593938358059003314316559 135890907537088504971474839)
  ·
    refine ⟨203836361305632757457212259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135890907537088504971474839 203836361305632757457212259)
    ·
      refine ⟨305754541958449136185818389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203836361305632757457212259 305754541958449136185818389)
      ·
        refine ⟨14332244154302303258710237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 305754541958449136185818389 14332244154302303258710237)
        ·
          refine ⟨5374591557863363722016339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14332244154302303258710237 5374591557863363722016339)
          ·
            refine ⟨8061887336795045583024509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5374591557863363722016339 8061887336795045583024509)
            ·
              refine ⟨3023207751298142093634191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8061887336795045583024509 3023207751298142093634191)
              ·
                refine ⟨4534811626947213140451287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3023207751298142093634191 4534811626947213140451287)
                ·
                  refine ⟨6802217440420819710676931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4534811626947213140451287 6802217440420819710676931)
                  ·
                    refine ⟨10203326160631229566015397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6802217440420819710676931 10203326160631229566015397)
                    ·
                      refine ⟨1913123655118355543627887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10203326160631229566015397 1913123655118355543627887)
                      ·
                        rfl

theorem cell23_3725795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_3725795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725795 prefixEnd_3725795 := by exact prefixLift 3725795
  have htrace : WordTrace (prefixWord ++ tailWord_3725795) baseStart_3725795 baseEnd_3725795 := by
    simpa [prefixWord, tailWord_3725795, baseEnd_3725795] using wordTrace_append hprefix tailTrace_3725795
  have hstable : (prefixWord ++ tailWord_3725795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725795).length < 2 ^ (prefixWord ++ tailWord_3725795).sum := by decide
  have hdescent : baseEnd_3725795 < baseStart_3725795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725805 : List Nat := [1, 5, 1, 3, 1, 2, 2, 2, 2, 4]
def baseStart_3725805 : Nat := 118140960795 + 3725805 * 2 ^ 59
def prefixEnd_3725805 : Nat := 4983230072969 + 3 ^ 40 * 3725805 * 2
def baseEnd_3725805 : Nat := 637709596641633501500947

theorem tailTrace_3725805 : CollatzResearch.WordTrace tailWord_3725805 prefixEnd_3725805 637709596641633501500947 := by
  unfold tailWord_3725805
  simp only [CollatzResearch.WordTrace]
  refine ⟨135891272267052276679338869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90594181511368184452892579 135891272267052276679338869)
  ·
    refine ⟨12739806775036150938688019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135891272267052276679338869 12739806775036150938688019)
    ·
      refine ⟨19109710162554226408032029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12739806775036150938688019 19109710162554226408032029)
      ·
        refine ⟨7166141310957834903012011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19109710162554226408032029 7166141310957834903012011)
        ·
          refine ⟨10749211966436752354518017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7166141310957834903012011 10749211966436752354518017)
          ·
            refine ⟨8061908974827564265888513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10749211966436752354518017 8061908974827564265888513)
            ·
              refine ⟨6046431731120673199416385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8061908974827564265888513 6046431731120673199416385)
              ·
                refine ⟨4534823798340504899562289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6046431731120673199416385 4534823798340504899562289)
                ·
                  refine ⟨3401117848755378674671717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4534823798340504899562289 3401117848755378674671717)
                  ·
                    refine ⟨637709596641633501500947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3401117848755378674671717 637709596641633501500947)
                    ·
                      rfl

theorem cell23_3725805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_3725805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725805 prefixEnd_3725805 := by exact prefixLift 3725805
  have htrace : WordTrace (prefixWord ++ tailWord_3725805) baseStart_3725805 baseEnd_3725805 := by
    simpa [prefixWord, tailWord_3725805, baseEnd_3725805] using wordTrace_append hprefix tailTrace_3725805
  have hstable : (prefixWord ++ tailWord_3725805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725805).length < 2 ^ (prefixWord ++ tailWord_3725805).sum := by decide
  have hdescent : baseEnd_3725805 < baseStart_3725805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725828 : List Nat := [2, 3, 2, 3, 1, 1, 1, 3, 1, 3, 3]
def baseStart_3725828 : Nat := 118140960795 + 3725828 * 2 ^ 59
def prefixEnd_3725828 : Nat := 4983230072969 + 3 ^ 40 * 3725828 * 2
def baseEnd_3725828 : Nat := 1913140599979953914515235

theorem tailTrace_3725828 : CollatzResearch.WordTrace tailWord_3725828 prefixEnd_3725828 1913140599979953914515235 := by
  unfold tailWord_3725828
  simp only [CollatzResearch.WordTrace]
  refine ⟨67946055572984475803713069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90594740763979301071617425 67946055572984475803713069)
  ·
    refine ⟨25479770839869178426392401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67946055572984475803713069 25479770839869178426392401)
    ·
      refine ⟨19109828129901883819794301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25479770839869178426392401 19109828129901883819794301)
      ·
        refine ⟨7166185548713206432422863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19109828129901883819794301 7166185548713206432422863)
        ·
          refine ⟨10749278323069809648634295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7166185548713206432422863 10749278323069809648634295)
          ·
            refine ⟨16123917484604714472951443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10749278323069809648634295 16123917484604714472951443)
            ·
              refine ⟨24185876226907071709427165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16123917484604714472951443 24185876226907071709427165)
              ·
                refine ⟨9069703585090151891035187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24185876226907071709427165 9069703585090151891035187)
                ·
                  refine ⟨13604555377635227836552781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9069703585090151891035187 13604555377635227836552781)
                  ·
                    refine ⟨5101708266613210438707293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13604555377635227836552781 5101708266613210438707293)
                    ·
                      refine ⟨1913140599979953914515235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5101708266613210438707293 1913140599979953914515235)
                      ·
                        rfl

theorem cell23_3725828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_3725828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725828 prefixEnd_3725828 := by exact prefixLift 3725828
  have htrace : WordTrace (prefixWord ++ tailWord_3725828) baseStart_3725828 baseEnd_3725828 := by
    simpa [prefixWord, tailWord_3725828, baseEnd_3725828] using wordTrace_append hprefix tailTrace_3725828
  have hstable : (prefixWord ++ tailWord_3725828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725828).length < 2 ^ (prefixWord ++ tailWord_3725828).sum := by decide
  have hdescent : baseEnd_3725828 < baseStart_3725828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725878 : List Nat := [5, 1, 2, 1, 2, 1, 2, 1, 2, 6]
def baseStart_3725878 : Nat := 118140960795 + 3725878 * 2 ^ 59
def prefixEnd_3725878 : Nat := 4983230072969 + 3 ^ 40 * 3725878 * 2
def baseEnd_3725878 : Nat := 637722091337559572963335

theorem tailTrace_3725878 : CollatzResearch.WordTrace tailWord_3725878 prefixEnd_3725878 637722091337559572963335 := by
  unfold tailWord_3725878
  simp only [CollatzResearch.WordTrace]
  refine ⟨8493370924736738134171643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90595956530525206764497525 8493370924736738134171643)
  ·
    refine ⟨12740056387105107201257465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8493370924736738134171643 12740056387105107201257465)
    ·
      refine ⟨9555042290328830400943099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12740056387105107201257465 9555042290328830400943099)
      ·
        refine ⟨14332563435493245601414649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9555042290328830400943099 14332563435493245601414649)
        ·
          refine ⟨10749422576619934201060987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14332563435493245601414649 10749422576619934201060987)
          ·
            refine ⟨16124133864929901301591481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10749422576619934201060987 16124133864929901301591481)
            ·
              refine ⟨12093100398697425976193611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16124133864929901301591481 12093100398697425976193611)
              ·
                refine ⟨18139650598046138964290417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12093100398697425976193611 18139650598046138964290417)
                ·
                  refine ⟨13604737948534604223217813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18139650598046138964290417 13604737948534604223217813)
                  ·
                    refine ⟨637722091337559572963335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13604737948534604223217813 637722091337559572963335)
                    ·
                      rfl

theorem cell23_3725878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_3725878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725878 prefixEnd_3725878 := by exact prefixLift 3725878
  have htrace : WordTrace (prefixWord ++ tailWord_3725878) baseStart_3725878 baseEnd_3725878 := by
    simpa [prefixWord, tailWord_3725878, baseEnd_3725878] using wordTrace_append hprefix tailTrace_3725878
  have hstable : (prefixWord ++ tailWord_3725878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725878).length < 2 ^ (prefixWord ++ tailWord_3725878).sum := by decide
  have hdescent : baseEnd_3725878 < baseStart_3725878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725881 : List Nat := [1, 2, 1, 5, 1, 1, 1, 3, 2, 2, 4]
def baseStart_3725881 : Nat := 118140960795 + 3725881 * 2 ^ 59
def prefixEnd_3725881 : Nat := 4983230072969 + 3 ^ 40 * 3725881 * 2
def baseEnd_3725881 : Nat := 1913167814454642207152491

theorem tailTrace_3725881 : CollatzResearch.WordTrace tailWord_3725881 prefixEnd_3725881 1913167814454642207152491 := by
  unfold tailWord_3725881
  simp only [CollatzResearch.WordTrace]
  refine ⟨135894044214776941659105497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90596029476517961106070331 135894044214776941659105497)
  ·
    refine ⟨101920533161082706244329123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135894044214776941659105497 101920533161082706244329123)
    ·
      refine ⟨152880799741624059366493685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101920533161082706244329123 152880799741624059366493685)
      ·
        refine ⟨14332574975777255565608783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152880799741624059366493685 14332574975777255565608783)
        ·
          refine ⟨21498862463665883348413175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14332574975777255565608783 21498862463665883348413175)
          ·
            refine ⟨32248293695498825022619763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21498862463665883348413175 32248293695498825022619763)
            ·
              refine ⟨48372440543248237533929645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32248293695498825022619763 48372440543248237533929645)
              ·
                refine ⟨18139665203718089075223617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48372440543248237533929645 18139665203718089075223617)
                ·
                  refine ⟨13604748902788566806417713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18139665203718089075223617 13604748902788566806417713)
                  ·
                    refine ⟨10203561677091425104813285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13604748902788566806417713 10203561677091425104813285)
                    ·
                      refine ⟨1913167814454642207152491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10203561677091425104813285 1913167814454642207152491)
                      ·
                        rfl

theorem cell23_3725881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_3725881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725881 prefixEnd_3725881 := by exact prefixLift 3725881
  have htrace : WordTrace (prefixWord ++ tailWord_3725881) baseStart_3725881 baseEnd_3725881 := by
    simpa [prefixWord, tailWord_3725881, baseEnd_3725881] using wordTrace_append hprefix tailTrace_3725881
  have hstable : (prefixWord ++ tailWord_3725881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725881).length < 2 ^ (prefixWord ++ tailWord_3725881).sum := by decide
  have hdescent : baseEnd_3725881 < baseStart_3725881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725885 : List Nat := [1, 4, 1, 3, 2, 1, 3, 1, 1, 4, 2]
def baseStart_3725885 : Nat := 118140960795 + 3725885 * 2 ^ 59
def prefixEnd_3725885 : Nat := 4983230072969 + 3 ^ 40 * 3725885 * 2
def baseEnd_3725885 : Nat := 1913169868377260191502473

theorem tailTrace_3725885 : CollatzResearch.WordTrace tailWord_3725885 prefixEnd_3725885 1913169868377260191502473 := by
  unfold tailWord_3725885
  simp only [CollatzResearch.WordTrace]
  refine ⟨135894190106762450342251109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90596126737841633561500739 135894190106762450342251109)
  ·
    refine ⟨25480160645017959439172083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135894190106762450342251109 25480160645017959439172083)
    ·
      refine ⟨38220240967526939158758125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25480160645017959439172083 38220240967526939158758125)
      ·
        refine ⟨14332590362822602184534297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38220240967526939158758125 14332590362822602184534297)
        ·
          refine ⟨10749442772116951638400723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14332590362822602184534297 10749442772116951638400723)
          ·
            refine ⟨16124164158175427457601085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10749442772116951638400723 16124164158175427457601085)
            ·
              refine ⟨6046561559315785296600407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16124164158175427457601085 6046561559315785296600407)
              ·
                refine ⟨9069842338973677944900611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6046561559315785296600407 9069842338973677944900611)
                ·
                  refine ⟨13604763508460516917350917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9069842338973677944900611 13604763508460516917350917)
                  ·
                    refine ⟨2550893157836346922003297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13604763508460516917350917 2550893157836346922003297)
                    ·
                      refine ⟨1913169868377260191502473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2550893157836346922003297 1913169868377260191502473)
                      ·
                        rfl

theorem cell23_3725885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_3725885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725885 prefixEnd_3725885 := by exact prefixLift 3725885
  have htrace : WordTrace (prefixWord ++ tailWord_3725885) baseStart_3725885 baseEnd_3725885 := by
    simpa [prefixWord, tailWord_3725885, baseEnd_3725885] using wordTrace_append hprefix tailTrace_3725885
  have hstable : (prefixWord ++ tailWord_3725885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725885).length < 2 ^ (prefixWord ++ tailWord_3725885).sum := by decide
  have hdescent : baseEnd_3725885 < baseStart_3725885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725921 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 4, 5]
def baseStart_3725921 : Nat := 118140960795 + 3725921 * 2 ^ 59
def prefixEnd_3725921 : Nat := 4983230072969 + 3 ^ 40 * 3725921 * 2
def baseEnd_3725921 : Nat := 637729451226940683550769

theorem tailTrace_3725921 : CollatzResearch.WordTrace tailWord_3725921 prefixEnd_3725921 637729451226940683550769 := by
  unfold tailWord_3725921
  simp only [CollatzResearch.WordTrace]
  refine ⟨135895503134632028490561617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90597002089754685660374411 135895503134632028490561617)
  ·
    refine ⟨101921627350974021367921213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135895503134632028490561617 101921627350974021367921213)
    ·
      refine ⟨38220610256615258012970455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101921627350974021367921213 38220610256615258012970455)
      ·
        refine ⟨57330915384922887019455683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38220610256615258012970455 57330915384922887019455683)
        ·
          refine ⟨85996373077384330529183525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57330915384922887019455683 85996373077384330529183525)
          ·
            refine ⟨16124319952009561974221911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85996373077384330529183525 16124319952009561974221911)
            ·
              refine ⟨24186479928014342961332867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16124319952009561974221911 24186479928014342961332867)
              ·
                refine ⟨36279719892021514441999301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24186479928014342961332867 36279719892021514441999301)
                ·
                  refine ⟨6802447479754033957874869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36279719892021514441999301 6802447479754033957874869)
                  ·
                    refine ⟨637729451226940683550769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6802447479754033957874869 637729451226940683550769)
                    ·
                      rfl

theorem cell23_3725921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_3725921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725921 prefixEnd_3725921 := by exact prefixLift 3725921
  have htrace : WordTrace (prefixWord ++ tailWord_3725921) baseStart_3725921 baseEnd_3725921 := by
    simpa [prefixWord, tailWord_3725921, baseEnd_3725921] using wordTrace_append hprefix tailTrace_3725921
  have hstable : (prefixWord ++ tailWord_3725921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725921).length < 2 ^ (prefixWord ++ tailWord_3725921).sum := by decide
  have hdescent : baseEnd_3725921 < baseStart_3725921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725925 : List Nat := [1, 3, 1, 3, 5, 1, 1, 1, 7]
def baseStart_3725925 : Nat := 118140960795 + 3725925 * 2 ^ 59
def prefixEnd_3725925 : Nat := 4983230072969 + 3 ^ 40 * 3725925 * 2
def baseEnd_3725925 : Nat := 212576711955937781666921

theorem tailTrace_3725925 : CollatzResearch.WordTrace tailWord_3725925 prefixEnd_3725925 212576711955937781666921 := by
  unfold tailWord_3725925
  simp only [CollatzResearch.WordTrace]
  refine ⟨135895649026617537173707229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90597099351078358115804819 135895649026617537173707229)
  ·
    refine ⟨50960868384981576440140211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135895649026617537173707229 50960868384981576440140211)
    ·
      refine ⟨76441302577472364660210317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50960868384981576440140211 76441302577472364660210317)
      ·
        refine ⟨28665488466552136747578869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76441302577472364660210317 28665488466552136747578869)
        ·
          refine ⟨2687389543739262820085519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28665488466552136747578869 2687389543739262820085519)
          ·
            refine ⟨4031084315608894230128279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2687389543739262820085519 4031084315608894230128279)
            ·
              refine ⟨6046626473413341345192419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4031084315608894230128279 6046626473413341345192419)
              ·
                refine ⟨9069939710120012017788629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6046626473413341345192419 9069939710120012017788629)
                ·
                  refine ⟨212576711955937781666921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9069939710120012017788629 212576711955937781666921)
                  ·
                    rfl

theorem cell23_3725925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 7].length) (baseStart_3725925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725925 prefixEnd_3725925 := by exact prefixLift 3725925
  have htrace : WordTrace (prefixWord ++ tailWord_3725925) baseStart_3725925 baseEnd_3725925 := by
    simpa [prefixWord, tailWord_3725925, baseEnd_3725925] using wordTrace_append hprefix tailTrace_3725925
  have hstable : (prefixWord ++ tailWord_3725925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725925).length < 2 ^ (prefixWord ++ tailWord_3725925).sum := by decide
  have hdescent : baseEnd_3725925 < baseStart_3725925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725936 : List Nat := [2, 1, 1, 1, 8, 1, 2, 1, 2, 2, 2]
def baseStart_3725936 : Nat := 118140960795 + 3725936 * 2 ^ 59
def prefixEnd_3725936 : Nat := 4983230072969 + 3 ^ 40 * 3725936 * 2
def baseEnd_3725936 : Nat := 1913196055890639491964739

theorem tailTrace_3725936 : CollatzResearch.WordTrace tailWord_3725936 prefixEnd_3725936 1913196055890639491964739 := by
  unfold tailWord_3725936
  simp only [CollatzResearch.WordTrace]
  refine ⟨67948025114788843026178831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90597366819718457368238441 67948025114788843026178831)
  ·
    refine ⟨101922037672183264539268247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67948025114788843026178831 101922037672183264539268247)
    ·
      refine ⟨152883056508274896808902371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101922037672183264539268247 152883056508274896808902371)
      ·
        refine ⟨229324584762412345213353557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152883056508274896808902371 229324584762412345213353557)
        ·
          refine ⟨2687397477684519670468987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 229324584762412345213353557 2687397477684519670468987)
          ·
            refine ⟨4031096216526779505703481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2687397477684519670468987 4031096216526779505703481)
            ·
              refine ⟨3023322162395084629277611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4031096216526779505703481 3023322162395084629277611)
              ·
                refine ⟨4534983243592626943916417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3023322162395084629277611 4534983243592626943916417)
                ·
                  refine ⟨3401237432694470207937313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4534983243592626943916417 3401237432694470207937313)
                  ·
                    refine ⟨2550928074520852655952985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3401237432694470207937313 2550928074520852655952985)
                    ·
                      refine ⟨1913196055890639491964739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2550928074520852655952985 1913196055890639491964739)
                      ·
                        rfl

theorem cell23_3725936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 2, 2, 2].length) (baseStart_3725936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725936 prefixEnd_3725936 := by exact prefixLift 3725936
  have htrace : WordTrace (prefixWord ++ tailWord_3725936) baseStart_3725936 baseEnd_3725936 := by
    simpa [prefixWord, tailWord_3725936, baseEnd_3725936] using wordTrace_append hprefix tailTrace_3725936
  have hstable : (prefixWord ++ tailWord_3725936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725936).length < 2 ^ (prefixWord ++ tailWord_3725936).sum := by decide
  have hdescent : baseEnd_3725936 < baseStart_3725936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3725981 : List Nat := [1, 4, 2, 1, 1, 1, 2, 3, 8]
def baseStart_3725981 : Nat := 118140960795 + 3725981 * 2 ^ 59
def prefixEnd_3725981 : Nat := 4983230072969 + 3 ^ 40 * 3725981 * 2
def baseEnd_3725981 : Nat := 212579906946676868433559

theorem tailTrace_3725981 : CollatzResearch.WordTrace tailWord_3725981 prefixEnd_3725981 212579906946676868433559 := by
  unfold tailWord_3725981
  simp only [CollatzResearch.WordTrace]
  refine ⟨135897691514414658737745797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90598461009609772491830531 135897691514414658737745797)
  ·
    refine ⟨25480817158952748513327337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135897691514414658737745797 25480817158952748513327337)
    ·
      refine ⟨19110612869214561384995503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25480817158952748513327337 19110612869214561384995503)
      ·
        refine ⟨28665919303821842077493255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19110612869214561384995503 28665919303821842077493255)
        ·
          refine ⟨42998878955732763116239883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28665919303821842077493255 42998878955732763116239883)
          ·
            refine ⟨64498318433599144674359825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42998878955732763116239883 64498318433599144674359825)
            ·
              refine ⟨48373738825199358505769869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64498318433599144674359825 48373738825199358505769869)
              ·
                refine ⟨18140152059449759439663701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48373738825199358505769869 18140152059449759439663701)
                ·
                  refine ⟨212579906946676868433559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18140152059449759439663701 212579906946676868433559)
                  ·
                    rfl

theorem cell23_3725981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_3725981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3725981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3725981 prefixEnd_3725981 := by exact prefixLift 3725981
  have htrace : WordTrace (prefixWord ++ tailWord_3725981) baseStart_3725981 baseEnd_3725981 := by
    simpa [prefixWord, tailWord_3725981, baseEnd_3725981] using wordTrace_append hprefix tailTrace_3725981
  have hstable : (prefixWord ++ tailWord_3725981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3725981).length < 2 ^ (prefixWord ++ tailWord_3725981).sum := by decide
  have hdescent : baseEnd_3725981 < baseStart_3725981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3725981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726042 : List Nat := [3, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3]
def baseStart_3726042 : Nat := 118140960795 + 3726042 * 2 ^ 59
def prefixEnd_3726042 : Nat := 4983230072969 + 3 ^ 40 * 3726042 * 2
def baseEnd_3726042 : Nat := 1913250484840016077239251

theorem tailTrace_3726042 : CollatzResearch.WordTrace tailWord_3726042 prefixEnd_3726042 1913250484840016077239251 := by
  unfold tailWord_3726042
  simp only [CollatzResearch.WordTrace]
  refine ⟨33974979091798416538929095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90599944244795777437144253 33974979091798416538929095)
  ·
    refine ⟨50962468637697624808393643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33974979091798416538929095 50962468637697624808393643)
    ·
      refine ⟨76443702956546437212590465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50962468637697624808393643 76443702956546437212590465)
      ·
        refine ⟨57332777217409827909442849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76443702956546437212590465 57332777217409827909442849)
        ·
          refine ⟨42999582913057370932082137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57332777217409827909442849 42999582913057370932082137)
          ·
            refine ⟨32249687184793028199061603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42999582913057370932082137 32249687184793028199061603)
            ·
              refine ⟨48374530777189542298592405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32249687184793028199061603 48374530777189542298592405)
              ·
                refine ⟨2267556130180759795246519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48374530777189542298592405 2267556130180759795246519)
                ·
                  refine ⟨3401334195271139692869779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2267556130180759795246519 3401334195271139692869779)
                  ·
                    refine ⟨5102001292906709539304669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3401334195271139692869779 5102001292906709539304669)
                    ·
                      refine ⟨1913250484840016077239251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5102001292906709539304669 1913250484840016077239251)
                      ·
                        rfl

theorem cell23_3726042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3].length) (baseStart_3726042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726042 prefixEnd_3726042 := by exact prefixLift 3726042
  have htrace : WordTrace (prefixWord ++ tailWord_3726042) baseStart_3726042 baseEnd_3726042 := by
    simpa [prefixWord, tailWord_3726042, baseEnd_3726042] using wordTrace_append hprefix tailTrace_3726042
  have hstable : (prefixWord ++ tailWord_3726042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726042).length < 2 ^ (prefixWord ++ tailWord_3726042).sum := by decide
  have hdescent : baseEnd_3726042 < baseStart_3726042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726065 : List Nat := [1, 2, 2, 2, 2, 2, 4, 2, 1, 1, 4]
def baseStart_3726065 : Nat := 118140960795 + 3726065 * 2 ^ 59
def prefixEnd_3726065 : Nat := 4983230072969 + 3 ^ 40 * 3726065 * 2
def baseEnd_3726065 : Nat := 1913262294895069487251645

theorem tailTrace_3726065 : CollatzResearch.WordTrace tailWord_3726065 prefixEnd_3726065 1913262294895069487251645 := by
  unfold tailWord_3726065
  simp only [CollatzResearch.WordTrace]
  refine ⟨135900755246110341083803649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90600503497406894055869099 135900755246110341083803649)
  ·
    refine ⟨101925566434582755812852737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135900755246110341083803649 101925566434582755812852737)
    ·
      refine ⟨76444174825937066859639553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101925566434582755812852737 76444174825937066859639553)
      ·
        refine ⟨57333131119452800144729665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76444174825937066859639553 57333131119452800144729665)
        ·
          refine ⟨42999848339589600108547249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57333131119452800144729665 42999848339589600108547249)
          ·
            refine ⟨32249886254692200081410437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42999848339589600108547249 32249886254692200081410437)
            ·
              refine ⟨6046853672754787515264457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32249886254692200081410437 6046853672754787515264457)
              ·
                refine ⟨4535140254566090636448343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6046853672754787515264457 4535140254566090636448343)
                ·
                  refine ⟨6802710381849135954672515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4535140254566090636448343 6802710381849135954672515)
                  ·
                    refine ⟨10204065572773703932008773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6802710381849135954672515 10204065572773703932008773)
                    ·
                      refine ⟨1913262294895069487251645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10204065572773703932008773 1913262294895069487251645)
                      ·
                        rfl

theorem cell23_3726065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_3726065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726065 prefixEnd_3726065 := by exact prefixLift 3726065
  have htrace : WordTrace (prefixWord ++ tailWord_3726065) baseStart_3726065 baseEnd_3726065 := by
    simpa [prefixWord, tailWord_3726065, baseEnd_3726065] using wordTrace_append hprefix tailTrace_3726065
  have hstable : (prefixWord ++ tailWord_3726065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726065).length < 2 ^ (prefixWord ++ tailWord_3726065).sum := by decide
  have hdescent : baseEnd_3726065 < baseStart_3726065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726082 : List Nat := [3, 4, 1, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_3726082 : Nat := 118140960795 + 3726082 * 2 ^ 59
def prefixEnd_3726082 : Nat := 4983230072969 + 3 ^ 40 * 3726082 * 2
def baseEnd_3726082 : Nat := 1913271024066195920739067

theorem tailTrace_3726082 : CollatzResearch.WordTrace tailWord_3726082 prefixEnd_3726082 1913271024066195920739067 := by
  unfold tailWord_3726082
  simp only [CollatzResearch.WordTrace]
  refine ⟨33975343821762188246793125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90600916858032501991448333 33975343821762188246793125)
  ·
    refine ⟨6370376966580410296273711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33975343821762188246793125 6370376966580410296273711)
    ·
      refine ⟨9555565449870615444410567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6370376966580410296273711 9555565449870615444410567)
      ·
        refine ⟨14333348174805923166615851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9555565449870615444410567 14333348174805923166615851)
        ·
          refine ⟨21500022262208884749923777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14333348174805923166615851 21500022262208884749923777)
          ·
            refine ⟨16125016696656663562442833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21500022262208884749923777 16125016696656663562442833)
            ·
              refine ⟨12093762522492497671832125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16125016696656663562442833 12093762522492497671832125)
              ·
                refine ⟨4535160945934686626937047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12093762522492497671832125 4535160945934686626937047)
                ·
                  refine ⟨6802741418902029940405571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4535160945934686626937047 6802741418902029940405571)
                  ·
                    refine ⟨10204112128353044910608357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6802741418902029940405571 10204112128353044910608357)
                    ·
                      refine ⟨1913271024066195920739067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10204112128353044910608357 1913271024066195920739067)
                      ·
                        rfl

theorem cell23_3726082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_3726082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726082 prefixEnd_3726082 := by exact prefixLift 3726082
  have htrace : WordTrace (prefixWord ++ tailWord_3726082) baseStart_3726082 baseEnd_3726082 := by
    simpa [prefixWord, tailWord_3726082, baseEnd_3726082] using wordTrace_append hprefix tailTrace_3726082
  have hstable : (prefixWord ++ tailWord_3726082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726082).length < 2 ^ (prefixWord ++ tailWord_3726082).sum := by decide
  have hdescent : baseEnd_3726082 < baseStart_3726082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726088 : List Nat := [2, 1, 3, 2, 2, 4, 9]
def baseStart_3726088 : Nat := 118140960795 + 3726088 * 2 ^ 59
def prefixEnd_3726088 : Nat := 4983230072969 + 3 ^ 40 * 3726088 * 2
def baseEnd_3726088 : Nat := 23620667962347196262519

theorem tailTrace_3726088 : CollatzResearch.WordTrace tailWord_3726088 prefixEnd_3726088 23620667962347196262519 := by
  unfold tailWord_3726088
  simp only [CollatzResearch.WordTrace]
  refine ⟨67950797062513508005945459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90601062750018010674593945 67950797062513508005945459)
  ·
    refine ⟨101926195593770262008918189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67950797062513508005945459 101926195593770262008918189)
    ·
      refine ⟨38222323347663848253344321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101926195593770262008918189 38222323347663848253344321)
      ·
        refine ⟨28666742510747886190008241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38222323347663848253344321 28666742510747886190008241)
        ·
          refine ⟨21500056883060914642506181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28666742510747886190008241 21500056883060914642506181)
          ·
            refine ⟨4031260665573921495469909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21500056883060914642506181 4031260665573921495469909)
            ·
              refine ⟨23620667962347196262519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4031260665573921495469909 23620667962347196262519)
              ·
                rfl

theorem cell23_3726088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 9].length) (baseStart_3726088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726088 prefixEnd_3726088 := by exact prefixLift 3726088
  have htrace : WordTrace (prefixWord ++ tailWord_3726088) baseStart_3726088 baseEnd_3726088 := by
    simpa [prefixWord, tailWord_3726088, baseEnd_3726088] using wordTrace_append hprefix tailTrace_3726088
  have hstable : (prefixWord ++ tailWord_3726088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726088).length < 2 ^ (prefixWord ++ tailWord_3726088).sum := by decide
  have hdescent : baseEnd_3726088 < baseStart_3726088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726109 : List Nat := [1, 4, 2, 4, 1, 1, 1, 3, 2, 4]
def baseStart_3726109 : Nat := 118140960795 + 3726109 * 2 ^ 59
def prefixEnd_3726109 : Nat := 4983230072969 + 3 ^ 40 * 3726109 * 2
def baseEnd_3726109 : Nat := 637761629347955771700481

theorem tailTrace_3726109 : CollatzResearch.WordTrace tailWord_3726109 prefixEnd_3726109 637761629347955771700481 := by
  unfold tailWord_3726109
  simp only [CollatzResearch.WordTrace]
  refine ⟨135902360057950936598405381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90601573371967291065603587 135902360057950936598405381)
  ·
    refine ⟨25481692510865800612201009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135902360057950936598405381 25481692510865800612201009)
    ·
      refine ⟨19111269383149350459150757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25481692510865800612201009 19111269383149350459150757)
      ·
        refine ⟨3583363009340503211090767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19111269383149350459150757 3583363009340503211090767)
        ·
          refine ⟨5375044514010754816636151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3583363009340503211090767 5375044514010754816636151)
          ·
            refine ⟨8062566771016132224954227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5375044514010754816636151 8062566771016132224954227)
            ·
              refine ⟨12093850156524198337431341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8062566771016132224954227 12093850156524198337431341)
              ·
                refine ⟨4535193808696574376536753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12093850156524198337431341 4535193808696574376536753)
                ·
                  refine ⟨3401395356522430782402565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4535193808696574376536753 3401395356522430782402565)
                  ·
                    refine ⟨637761629347955771700481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3401395356522430782402565 637761629347955771700481)
                    ·
                      rfl

theorem cell23_3726109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_3726109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726109 prefixEnd_3726109 := by exact prefixLift 3726109
  have htrace : WordTrace (prefixWord ++ tailWord_3726109) baseStart_3726109 baseEnd_3726109 := by
    simpa [prefixWord, tailWord_3726109, baseEnd_3726109] using wordTrace_append hprefix tailTrace_3726109
  have hstable : (prefixWord ++ tailWord_3726109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726109).length < 2 ^ (prefixWord ++ tailWord_3726109).sum := by decide
  have hdescent : baseEnd_3726109 < baseStart_3726109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726150 : List Nat := [6, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2]
def baseStart_3726150 : Nat := 118140960795 + 3726150 * 2 ^ 59
def prefixEnd_3726150 : Nat := 4983230072969 + 3 ^ 40 * 3726150 * 2
def baseEnd_3726150 : Nat := 1913305940750701654688755

theorem tailTrace_3726150 : CollatzResearch.WordTrace tailWord_3726150 prefixEnd_3726150 1913305940750701654688755 := by
  unfold tailWord_3726150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4246995482837575018770247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 90602570300534933733765269 4246995482837575018770247)
  ·
    refine ⟨6370493224256362528155371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4246995482837575018770247 6370493224256362528155371)
    ·
      refine ⟨9555739836384543792233057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6370493224256362528155371 9555739836384543792233057)
      ·
        refine ⟨7166804877288407844174793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9555739836384543792233057 7166804877288407844174793)
        ·
          refine ⟨5375103657966305883131095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7166804877288407844174793 5375103657966305883131095)
          ·
            refine ⟨8062655486949458824696643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5375103657966305883131095 8062655486949458824696643)
            ·
              refine ⟨12093983230424188237044965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8062655486949458824696643 12093983230424188237044965)
              ·
                refine ⟨2267621855704535294445931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12093983230424188237044965 2267621855704535294445931)
                ·
                  refine ⟨3401432783556802941668897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2267621855704535294445931 3401432783556802941668897)
                  ·
                    refine ⟨2551074587667602206251673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3401432783556802941668897 2551074587667602206251673)
                    ·
                      refine ⟨1913305940750701654688755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2551074587667602206251673 1913305940750701654688755)
                      ·
                        rfl

theorem cell23_3726150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_3726150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726150 prefixEnd_3726150 := by exact prefixLift 3726150
  have htrace : WordTrace (prefixWord ++ tailWord_3726150) baseStart_3726150 baseEnd_3726150 := by
    simpa [prefixWord, tailWord_3726150, baseEnd_3726150] using wordTrace_append hprefix tailTrace_3726150
  have hstable : (prefixWord ++ tailWord_3726150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726150).length < 2 ^ (prefixWord ++ tailWord_3726150).sum := by decide
  have hdescent : baseEnd_3726150 < baseStart_3726150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726158 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5]
def baseStart_3726158 : Nat := 118140960795 + 3726158 * 2 ^ 59
def prefixEnd_3726158 : Nat := 4983230072969 + 3 ^ 40 * 3726158 * 2
def baseEnd_3726158 : Nat := 1913310048595937623388717

theorem tailTrace_3726158 : CollatzResearch.WordTrace tailWord_3726158 prefixEnd_3726158 1913310048595937623388717 := by
  unfold tailWord_3726158
  simp only [CollatzResearch.WordTrace]
  refine ⟨16988018404346677245867391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90602764823182278644626085 16988018404346677245867391)
  ·
    refine ⟨25482027606520015868801087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16988018404346677245867391 25482027606520015868801087)
    ·
      refine ⟨38223041409780023803201631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25482027606520015868801087 38223041409780023803201631)
      ·
        refine ⟨57334562114670035704802447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38223041409780023803201631 57334562114670035704802447)
        ·
          refine ⟨86001843172005053557203671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57334562114670035704802447 86001843172005053557203671)
          ·
            refine ⟨129002764758007580335805507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86001843172005053557203671 129002764758007580335805507)
            ·
              refine ⟨193504147137011370503708261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129002764758007580335805507 193504147137011370503708261)
              ·
                refine ⟨36282027588189631969445299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193504147137011370503708261 36282027588189631969445299)
                ·
                  refine ⟨54423041382284447954167949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36282027588189631969445299 54423041382284447954167949)
                  ·
                    refine ⟨20408640518356667982812981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54423041382284447954167949 20408640518356667982812981)
                    ·
                      refine ⟨1913310048595937623388717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20408640518356667982812981 1913310048595937623388717)
                      ·
                        rfl

theorem cell23_3726158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_3726158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726158 prefixEnd_3726158 := by exact prefixLift 3726158
  have htrace : WordTrace (prefixWord ++ tailWord_3726158) baseStart_3726158 baseEnd_3726158 := by
    simpa [prefixWord, tailWord_3726158, baseEnd_3726158] using wordTrace_append hprefix tailTrace_3726158
  have hstable : (prefixWord ++ tailWord_3726158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726158).length < 2 ^ (prefixWord ++ tailWord_3726158).sum := by decide
  have hdescent : baseEnd_3726158 < baseStart_3726158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726195 : List Nat := [1, 1, 1, 2, 2, 1, 5, 5, 5]
def baseStart_3726195 : Nat := 118140960795 + 3726195 * 2 ^ 59
def prefixEnd_3726195 : Nat := 4983230072969 + 3 ^ 40 * 3726195 * 2
def baseEnd_3726195 : Nat := 212592116375572664291783

theorem tailTrace_3726195 : CollatzResearch.WordTrace tailWord_3726195 prefixEnd_3726195 212592116375572664291783 := by
  unfold tailWord_3726195
  simp only [CollatzResearch.WordTrace]
  refine ⟨135905496735639373286036039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90603664490426248857357359 135905496735639373286036039)
  ·
    refine ⟨203858245103459059929054059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135905496735639373286036039 203858245103459059929054059)
    ·
      refine ⟨305787367655188589893581089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203858245103459059929054059 305787367655188589893581089)
      ·
        refine ⟨229340525741391442420185817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305787367655188589893581089 229340525741391442420185817)
        ·
          refine ⟨172005394306043581815139363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229340525741391442420185817 172005394306043581815139363)
          ·
            refine ⟨258008091459065372722709045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172005394306043581815139363 258008091459065372722709045)
            ·
              refine ⟨24188258574287378692753973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 258008091459065372722709045 24188258574287378692753973)
              ·
                refine ⟨2267649241339441752445685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24188258574287378692753973 2267649241339441752445685)
                ·
                  refine ⟨212592116375572664291783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2267649241339441752445685 212592116375572664291783)
                  ·
                    rfl

theorem cell23_3726195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5, 5].length) (baseStart_3726195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726195 prefixEnd_3726195 := by exact prefixLift 3726195
  have htrace : WordTrace (prefixWord ++ tailWord_3726195) baseStart_3726195 baseEnd_3726195 := by
    simpa [prefixWord, tailWord_3726195, baseEnd_3726195] using wordTrace_append hprefix tailTrace_3726195
  have hstable : (prefixWord ++ tailWord_3726195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726195).length < 2 ^ (prefixWord ++ tailWord_3726195).sum := by decide
  have hdescent : baseEnd_3726195 < baseStart_3726195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726205 : List Nat := [1, 4, 1, 1, 2, 1, 3, 2, 2, 3, 3]
def baseStart_3726205 : Nat := 118140960795 + 3726205 * 2 ^ 59
def prefixEnd_3726205 : Nat := 4983230072969 + 3 ^ 40 * 3726205 * 2
def baseEnd_3726205 : Nat := 1913334182186698939501001

theorem tailTrace_3726205 : CollatzResearch.WordTrace tailWord_3726205 prefixEnd_3726205 1913334182186698939501001 := by
  unfold tailWord_3726205
  simp only [CollatzResearch.WordTrace]
  refine ⟨135905861465603144993900069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90603907643735429995933379 135905861465603144993900069)
  ·
    refine ⟨25482349024800589686356263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135905861465603144993900069 25482349024800589686356263)
    ·
      refine ⟨38223523537200884529534395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25482349024800589686356263 38223523537200884529534395)
      ·
        refine ⟨57335285305801326794301593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38223523537200884529534395 57335285305801326794301593)
        ·
          refine ⟨43001463979350995095726195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57335285305801326794301593 43001463979350995095726195)
          ·
            refine ⟨64502195969026492643589293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43001463979350995095726195 64502195969026492643589293)
            ·
              refine ⟨24188323488384934741345985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64502195969026492643589293 24188323488384934741345985)
              ·
                refine ⟨18141242616288701056009489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24188323488384934741345985 18141242616288701056009489)
                ·
                  refine ⟨13605931962216525792007117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18141242616288701056009489 13605931962216525792007117)
                  ·
                    refine ⟨5102224485831197172002669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13605931962216525792007117 5102224485831197172002669)
                    ·
                      refine ⟨1913334182186698939501001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5102224485831197172002669 1913334182186698939501001)
                      ·
                        rfl

theorem cell23_3726205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_3726205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726205 prefixEnd_3726205 := by exact prefixLift 3726205
  have htrace : WordTrace (prefixWord ++ tailWord_3726205) baseStart_3726205 baseEnd_3726205 := by
    simpa [prefixWord, tailWord_3726205, baseEnd_3726205] using wordTrace_append hprefix tailTrace_3726205
  have hstable : (prefixWord ++ tailWord_3726205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726205).length < 2 ^ (prefixWord ++ tailWord_3726205).sum := by decide
  have hdescent : baseEnd_3726205 < baseStart_3726205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726272 : List Nat := [2, 1, 1, 2, 3, 3, 3, 1, 3, 4]
def baseStart_3726272 : Nat := 118140960795 + 3726272 * 2 ^ 59
def prefixEnd_3726272 : Nat := 4983230072969 + 3 ^ 40 * 3726272 * 2
def baseEnd_3726272 : Nat := 637789528463516725787731

theorem tailTrace_3726272 : CollatzResearch.WordTrace tailWord_3726272 prefixEnd_3726272 637789528463516725787731 := by
  unfold tailWord_3726272
  simp only [CollatzResearch.WordTrace]
  refine ⟨67954152578180207718294535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90605536770906943624392713 67954152578180207718294535)
  ·
    refine ⟨101931228867270311577441803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67954152578180207718294535 101931228867270311577441803)
    ·
      refine ⟨152896843300905467366162705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101931228867270311577441803 152896843300905467366162705)
      ·
        refine ⟨114672632475679100524622029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152896843300905467366162705 114672632475679100524622029)
        ·
          refine ⟨43002237178379662696733261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114672632475679100524622029 43002237178379662696733261)
          ·
            refine ⟨16125838941892373511274973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43002237178379662696733261 16125838941892373511274973)
            ·
              refine ⟨6047189603209640066728115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16125838941892373511274973 6047189603209640066728115)
              ·
                refine ⟨9070784404814460100092173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6047189603209640066728115 9070784404814460100092173)
                ·
                  refine ⟨3401544151805422537534565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9070784404814460100092173 3401544151805422537534565)
                  ·
                    refine ⟨637789528463516725787731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3401544151805422537534565 637789528463516725787731)
                    ·
                      rfl

theorem cell23_3726272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 3, 4].length) (baseStart_3726272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726272 prefixEnd_3726272 := by exact prefixLift 3726272
  have htrace : WordTrace (prefixWord ++ tailWord_3726272) baseStart_3726272 baseEnd_3726272 := by
    simpa [prefixWord, tailWord_3726272, baseEnd_3726272] using wordTrace_append hprefix tailTrace_3726272
  have hstable : (prefixWord ++ tailWord_3726272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726272).length < 2 ^ (prefixWord ++ tailWord_3726272).sum := by decide
  have hdescent : baseEnd_3726272 < baseStart_3726272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726362 : List Nat := [3, 1, 1, 3, 1, 2, 2, 2, 4, 4]
def baseStart_3726362 : Nat := 118140960795 + 3726362 * 2 ^ 59
def prefixEnd_3726362 : Nat := 4983230072969 + 3 ^ 40 * 3726362 * 2
def baseEnd_3726362 : Nat := 637804932883151608412593

theorem tailTrace_3726362 : CollatzResearch.WordTrace tailWord_3726362 prefixEnd_3726362 637804932883151608412593 := by
  unfold tailWord_3726362
  simp only [CollatzResearch.WordTrace]
  refine ⟨33977896931508590201841335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90607725150689573871576893 33977896931508590201841335)
  ·
    refine ⟨50966845397262885302762003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33977896931508590201841335 50966845397262885302762003)
    ·
      refine ⟨76450268095894327954143005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50966845397262885302762003 76450268095894327954143005)
      ·
        refine ⟨28668850535960372982803627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76450268095894327954143005 28668850535960372982803627)
        ·
          refine ⟨43003275803940559474205441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28668850535960372982803627 43003275803940559474205441)
          ·
            refine ⟨32252456852955419605654081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43003275803940559474205441 32252456852955419605654081)
            ·
              refine ⟨24189342639716564704240561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32252456852955419605654081 24189342639716564704240561)
              ·
                refine ⟨18142006979787423528180421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24189342639716564704240561 18142006979787423528180421)
                ·
                  refine ⟨3401626308710141911533829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18142006979787423528180421 3401626308710141911533829)
                  ·
                    refine ⟨637804932883151608412593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3401626308710141911533829 637804932883151608412593)
                    ·
                      rfl

theorem cell23_3726362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 4, 4].length) (baseStart_3726362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726362 prefixEnd_3726362 := by exact prefixLift 3726362
  have htrace : WordTrace (prefixWord ++ tailWord_3726362) baseStart_3726362 baseEnd_3726362 := by
    simpa [prefixWord, tailWord_3726362, baseEnd_3726362] using wordTrace_append hprefix tailTrace_3726362
  have hstable : (prefixWord ++ tailWord_3726362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726362).length < 2 ^ (prefixWord ++ tailWord_3726362).sum := by decide
  have hdescent : baseEnd_3726362 < baseStart_3726362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726369 : List Nat := [1, 2, 3, 2, 3, 2, 1, 3, 1, 1, 4]
def baseStart_3726369 : Nat := 118140960795 + 3726369 * 2 ^ 59
def prefixEnd_3726369 : Nat := 4983230072969 + 3 ^ 40 * 3726369 * 2
def baseEnd_3726369 : Nat := 1913418393014036297850247

theorem tailTrace_3726369 : CollatzResearch.WordTrace tailWord_3726369 prefixEnd_3726369 1913418393014036297850247 := by
  unfold tailWord_3726369
  simp only [CollatzResearch.WordTrace]
  refine ⟨135911843037009001002870161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90607895358006000668580107 135911843037009001002870161)
  ·
    refine ⟨101933882277756750752152621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135911843037009001002870161 101933882277756750752152621)
    ·
      refine ⟨38225205854158781532057233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101933882277756750752152621 38225205854158781532057233)
      ·
        refine ⟨28668904390619086149042925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38225205854158781532057233 28668904390619086149042925)
        ·
          refine ⟨10750839146482157305891097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28668904390619086149042925 10750839146482157305891097)
          ·
            refine ⟨8063129359861617979418323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10750839146482157305891097 8063129359861617979418323)
            ·
              refine ⟨12094694039792426969127485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8063129359861617979418323 12094694039792426969127485)
              ·
                refine ⟨4535510264922160113422807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12094694039792426969127485 4535510264922160113422807)
                ·
                  refine ⟨6803265397383240170134211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4535510264922160113422807 6803265397383240170134211)
                  ·
                    refine ⟨10204898096074860255201317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6803265397383240170134211 10204898096074860255201317)
                    ·
                      refine ⟨1913418393014036297850247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10204898096074860255201317 1913418393014036297850247)
                      ·
                        rfl

theorem cell23_3726369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_3726369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726369 prefixEnd_3726369 := by exact prefixLift 3726369
  have htrace : WordTrace (prefixWord ++ tailWord_3726369) baseStart_3726369 baseEnd_3726369 := by
    simpa [prefixWord, tailWord_3726369, baseEnd_3726369] using wordTrace_append hprefix tailTrace_3726369
  have hstable : (prefixWord ++ tailWord_3726369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726369).length < 2 ^ (prefixWord ++ tailWord_3726369).sum := by decide
  have hdescent : baseEnd_3726369 < baseStart_3726369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726382 : List Nat := [4, 1, 3, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_3726382 : Nat := 118140960795 + 3726382 * 2 ^ 59
def prefixEnd_3726382 : Nat := 4983230072969 + 3 ^ 40 * 3726382 * 2
def baseEnd_3726382 : Nat := 1913425068262544746987687

theorem tailTrace_3726382 : CollatzResearch.WordTrace tailWord_3726382 prefixEnd_3726382 1913425068262544746987687 := by
  unfold tailWord_3726382
  simp only [CollatzResearch.WordTrace]
  refine ⟨16989039648245238027886675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90608211457307936148728933 16989039648245238027886675)
  ·
    refine ⟨25483559472367857041830013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16989039648245238027886675 25483559472367857041830013)
    ·
      refine ⟨9556334802137946390686255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25483559472367857041830013 9556334802137946390686255)
      ·
        refine ⟨14334502203206919586029383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9556334802137946390686255 14334502203206919586029383)
        ·
          refine ⟨21501753304810379379044075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14334502203206919586029383 21501753304810379379044075)
          ·
            refine ⟨32252629957215569068566113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21501753304810379379044075 32252629957215569068566113)
            ·
              refine ⟨24189472467911676801424585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32252629957215569068566113 24189472467911676801424585)
              ·
                refine ⟨18142104350933757601068439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24189472467911676801424585 18142104350933757601068439)
                ·
                  refine ⟨27213156526400636401602659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18142104350933757601068439 27213156526400636401602659)
                  ·
                    refine ⟨40819734789600954602403989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27213156526400636401602659 40819734789600954602403989)
                    ·
                      refine ⟨1913425068262544746987687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40819734789600954602403989 1913425068262544746987687)
                      ·
                        rfl

theorem cell23_3726382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_3726382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726382 prefixEnd_3726382 := by exact prefixLift 3726382
  have htrace : WordTrace (prefixWord ++ tailWord_3726382) baseStart_3726382 baseEnd_3726382 := by
    simpa [prefixWord, tailWord_3726382, baseEnd_3726382] using wordTrace_append hprefix tailTrace_3726382
  have hstable : (prefixWord ++ tailWord_3726382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726382).length < 2 ^ (prefixWord ++ tailWord_3726382).sum := by decide
  have hdescent : baseEnd_3726382 < baseStart_3726382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726386 : List Nat := [3, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2]
def baseStart_3726386 : Nat := 118140960795 + 3726386 * 2 ^ 59
def prefixEnd_3726386 : Nat := 4983230072969 + 3 ^ 40 * 3726386 * 2
def baseEnd_3726386 : Nat := 1913427122185162731337669

theorem tailTrace_3726386 : CollatzResearch.WordTrace tailWord_3726386 prefixEnd_3726386 1913427122185162731337669 := by
  unfold tailWord_3726386
  simp only [CollatzResearch.WordTrace]
  refine ⟨33978115769486853226559753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90608308718631608604159341 33978115769486853226559753)
  ·
    refine ⟨25483586827115139919919815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33978115769486853226559753 25483586827115139919919815)
    ·
      refine ⟨38225380240672709879879723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25483586827115139919919815 38225380240672709879879723)
      ·
        refine ⟨57338070361009064819819585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38225380240672709879879723 57338070361009064819819585)
        ·
          refine ⟨43003552770756798614864689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57338070361009064819819585 43003552770756798614864689)
          ·
            refine ⟨32252664578067598961148517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43003552770756798614864689 32252664578067598961148517)
            ·
              refine ⟨6047374608387674805215347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32252664578067598961148517 6047374608387674805215347)
              ·
                refine ⟨9071061912581512207823021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6047374608387674805215347 9071061912581512207823021)
                ·
                  refine ⟨3401648217218067077933633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9071061912581512207823021 3401648217218067077933633)
                  ·
                    refine ⟨2551236162913550308450225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3401648217218067077933633 2551236162913550308450225)
                    ·
                      refine ⟨1913427122185162731337669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2551236162913550308450225 1913427122185162731337669)
                      ·
                        rfl

theorem cell23_3726386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2].length) (baseStart_3726386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726386 prefixEnd_3726386 := by exact prefixLift 3726386
  have htrace : WordTrace (prefixWord ++ tailWord_3726386) baseStart_3726386 baseEnd_3726386 := by
    simpa [prefixWord, tailWord_3726386, baseEnd_3726386] using wordTrace_append hprefix tailTrace_3726386
  have hstable : (prefixWord ++ tailWord_3726386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726386).length < 2 ^ (prefixWord ++ tailWord_3726386).sum := by decide
  have hdescent : baseEnd_3726386 < baseStart_3726386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726396 : List Nat := [2, 2, 2, 2, 2, 3, 3, 1, 2, 4]
def baseStart_3726396 : Nat := 118140960795 + 3726396 * 2 ^ 59
def prefixEnd_3726396 : Nat := 4983230072969 + 3 ^ 40 * 3726396 * 2
def baseEnd_3726396 : Nat := 637810752330569230737541

theorem tailTrace_3726396 : CollatzResearch.WordTrace tailWord_3726396 prefixEnd_3726396 637810752330569230737541 := by
  unfold tailWord_3726396
  simp only [CollatzResearch.WordTrace]
  refine ⟨67956413903955592307051521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90608551871940789742735361 67956413903955592307051521)
  ·
    refine ⟨50967310427966694230288641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67956413903955592307051521 50967310427966694230288641)
    ·
      refine ⟨38225482820975020672716481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50967310427966694230288641 38225482820975020672716481)
      ·
        refine ⟨28669112115731265504537361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38225482820975020672716481 28669112115731265504537361)
        ·
          refine ⟨21501834086798449128403021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28669112115731265504537361 21501834086798449128403021)
          ·
            refine ⟨8063187782549418423151133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21501834086798449128403021 8063187782549418423151133)
            ·
              refine ⟨3023695418456031908681675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8063187782549418423151133 3023695418456031908681675)
              ·
                refine ⟨4535543127684047863022513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3023695418456031908681675 4535543127684047863022513)
                ·
                  refine ⟨3401657345763035897266885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4535543127684047863022513 3401657345763035897266885)
                  ·
                    refine ⟨637810752330569230737541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3401657345763035897266885 637810752330569230737541)
                    ·
                      rfl

theorem cell23_3726396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_3726396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726396 prefixEnd_3726396 := by exact prefixLift 3726396
  have htrace : WordTrace (prefixWord ++ tailWord_3726396) baseStart_3726396 baseEnd_3726396 := by
    simpa [prefixWord, tailWord_3726396, baseEnd_3726396] using wordTrace_append hprefix tailTrace_3726396
  have hstable : (prefixWord ++ tailWord_3726396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726396).length < 2 ^ (prefixWord ++ tailWord_3726396).sum := by decide
  have hdescent : baseEnd_3726396 < baseStart_3726396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726405 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 2, 7]
def baseStart_3726405 : Nat := 118140960795 + 3726405 * 2 ^ 59
def prefixEnd_3726405 : Nat := 4983230072969 + 3 ^ 40 * 3726405 * 2
def baseEnd_3726405 : Nat := 637812292772532719000027

theorem tailTrace_3726405 : CollatzResearch.WordTrace tailWord_3726405 prefixEnd_3726405 637812292772532719000027 := by
  unfold tailWord_3726405
  simp only [CollatzResearch.WordTrace]
  refine ⟨135913156064878579151180669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90608770709919052767453779 135913156064878579151180669)
  ·
    refine ⟨50967433524329467181692751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135913156064878579151180669 50967433524329467181692751)
    ·
      refine ⟨76451150286494200772539127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50967433524329467181692751 76451150286494200772539127)
      ·
        refine ⟨114676725429741301158808691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76451150286494200772539127 114676725429741301158808691)
        ·
          refine ⟨172015088144611951738213037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114676725429741301158808691 172015088144611951738213037)
          ·
            refine ⟨64505658054229481901829889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172015088144611951738213037 64505658054229481901829889)
            ·
              refine ⟨48379243540672111426372417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64505658054229481901829889 48379243540672111426372417)
              ·
                refine ⟨36284432655504083569779313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48379243540672111426372417 36284432655504083569779313)
                ·
                  refine ⟨27213324491628062677334485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36284432655504083569779313 27213324491628062677334485)
                  ·
                    refine ⟨637812292772532719000027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27213324491628062677334485 637812292772532719000027)
                    ·
                      rfl

theorem cell23_3726405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_3726405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726405 prefixEnd_3726405 := by exact prefixLift 3726405
  have htrace : WordTrace (prefixWord ++ tailWord_3726405) baseStart_3726405 baseEnd_3726405 := by
    simpa [prefixWord, tailWord_3726405, baseEnd_3726405] using wordTrace_append hprefix tailTrace_3726405
  have hstable : (prefixWord ++ tailWord_3726405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726405).length < 2 ^ (prefixWord ++ tailWord_3726405).sum := by decide
  have hdescent : baseEnd_3726405 < baseStart_3726405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726493 : List Nat := [1, 4, 2, 1, 1, 2, 4, 2, 2, 2, 2]
def baseStart_3726493 : Nat := 118140960795 + 3726493 * 2 ^ 59
def prefixEnd_3726493 : Nat := 4983230072969 + 3 ^ 40 * 3726493 * 2
def baseEnd_3726493 : Nat := 1913482064615193812699677

theorem tailTrace_3726493 : CollatzResearch.WordTrace tailWord_3726493 prefixEnd_3726493 1913482064615193812699677 := by
  unfold tailWord_3726493
  simp only [CollatzResearch.WordTrace]
  refine ⟨135916365688559770180384133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90610910459039846786922755 135916365688559770180384133)
  ·
    refine ⟨25484318566604956908822025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135916365688559770180384133 25484318566604956908822025)
    ·
      refine ⟨19113238924953717681616519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25484318566604956908822025 19113238924953717681616519)
      ·
        refine ⟨28669858387430576522424779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19113238924953717681616519 28669858387430576522424779)
        ·
          refine ⟨43004787581145864783637169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28669858387430576522424779 43004787581145864783637169)
          ·
            refine ⟨32253590685859398587727877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43004787581145864783637169 32253590685859398587727877)
            ·
              refine ⟨6047548253598637235198977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32253590685859398587727877 6047548253598637235198977)
              ·
                refine ⟨4535661190198977926399233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6047548253598637235198977 4535661190198977926399233)
                ·
                  refine ⟨3401745892649233444799425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4535661190198977926399233 3401745892649233444799425)
                  ·
                    refine ⟨2551309419486925083599569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3401745892649233444799425 2551309419486925083599569)
                    ·
                      refine ⟨1913482064615193812699677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2551309419486925083599569 1913482064615193812699677)
                      ·
                        rfl

theorem cell23_3726493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_3726493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726493 prefixEnd_3726493 := by exact prefixLift 3726493
  have htrace : WordTrace (prefixWord ++ tailWord_3726493) baseStart_3726493 baseEnd_3726493 := by
    simpa [prefixWord, tailWord_3726493, baseEnd_3726493] using wordTrace_append hprefix tailTrace_3726493
  have hstable : (prefixWord ++ tailWord_3726493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726493).length < 2 ^ (prefixWord ++ tailWord_3726493).sum := by decide
  have hdescent : baseEnd_3726493 < baseStart_3726493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726506 : List Nat := [3, 1, 5, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_3726506 : Nat := 118140960795 + 3726506 * 2 ^ 59
def prefixEnd_3726506 : Nat := 4983230072969 + 3 ^ 40 * 3726506 * 2
def baseEnd_3726506 : Nat := 1913488739863702261837117

theorem tailTrace_3726506 : CollatzResearch.WordTrace tailWord_3726506 prefixEnd_3726506 1913488739863702261837117 := by
  unfold tailWord_3726506
  simp only [CollatzResearch.WordTrace]
  refine ⟨33979209959378168350151843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90611226558341782267071581 33979209959378168350151843)
  ·
    refine ⟨50968814939067252525227765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33979209959378168350151843 50968814939067252525227765)
    ·
      refine ⟨4778326400537554924240103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50968814939067252525227765 4778326400537554924240103)
      ·
        refine ⟨7167489600806332386360155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4778326400537554924240103 7167489600806332386360155)
        ·
          refine ⟨10751234401209498579540233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7167489600806332386360155 10751234401209498579540233)
          ·
            refine ⟨8063425800907123934655175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10751234401209498579540233 8063425800907123934655175)
            ·
              refine ⟨12095138701360685901982763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8063425800907123934655175 12095138701360685901982763)
              ·
                refine ⟨18142708052041028852974145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12095138701360685901982763 18142708052041028852974145)
                ·
                  refine ⟨13607031039030771639730609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18142708052041028852974145 13607031039030771639730609)
                  ·
                    refine ⟨10205273279273078729797957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13607031039030771639730609 10205273279273078729797957)
                    ·
                      refine ⟨1913488739863702261837117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10205273279273078729797957 1913488739863702261837117)
                      ·
                        rfl

theorem cell23_3726506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_3726506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726506 prefixEnd_3726506 := by exact prefixLift 3726506
  have htrace : WordTrace (prefixWord ++ tailWord_3726506) baseStart_3726506 baseEnd_3726506 := by
    simpa [prefixWord, tailWord_3726506, baseEnd_3726506] using wordTrace_append hprefix tailTrace_3726506
  have hstable : (prefixWord ++ tailWord_3726506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726506).length < 2 ^ (prefixWord ++ tailWord_3726506).sum := by decide
  have hdescent : baseEnd_3726506 < baseStart_3726506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726519 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 2, 5, 2]
def baseStart_3726519 : Nat := 118140960795 + 3726519 * 2 ^ 59
def prefixEnd_3726519 : Nat := 4983230072969 + 3 ^ 40 * 3726519 * 2
def baseEnd_3726519 : Nat := 1913495415112210710974557

theorem tailTrace_3726519 : CollatzResearch.WordTrace tailWord_3726519 prefixEnd_3726519 1913495415112210710974557 := by
  unfold tailWord_3726519
  simp only [CollatzResearch.WordTrace]
  refine ⟨135917313986465576620830611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90611542657643717747220407 135917313986465576620830611)
  ·
    refine ⟨203875970979698364931245917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135917313986465576620830611 203875970979698364931245917)
    ·
      refine ⟨76453489117386886849217219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203875970979698364931245917 76453489117386886849217219)
      ·
        refine ⟨114680233676080330273825829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76453489117386886849217219 114680233676080330273825829)
        ·
          refine ⟨21502543814265061926342343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114680233676080330273825829 21502543814265061926342343)
          ·
            refine ⟨32253815721397592889513515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21502543814265061926342343 32253815721397592889513515)
            ·
              refine ⟨48380723582096389334270273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32253815721397592889513515 48380723582096389334270273)
              ·
                refine ⟨36285542686572292000702705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48380723582096389334270273 36285542686572292000702705)
                ·
                  refine ⟨27214157014929219000527029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36285542686572292000702705 27214157014929219000527029)
                  ·
                    refine ⟨2551327220149614281299409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27214157014929219000527029 2551327220149614281299409)
                    ·
                      refine ⟨1913495415112210710974557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2551327220149614281299409 1913495415112210710974557)
                      ·
                        rfl

theorem cell23_3726519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 5, 2].length) (baseStart_3726519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726519 prefixEnd_3726519 := by exact prefixLift 3726519
  have htrace : WordTrace (prefixWord ++ tailWord_3726519) baseStart_3726519 baseEnd_3726519 := by
    simpa [prefixWord, tailWord_3726519, baseEnd_3726519] using wordTrace_append hprefix tailTrace_3726519
  have hstable : (prefixWord ++ tailWord_3726519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726519).length < 2 ^ (prefixWord ++ tailWord_3726519).sum := by decide
  have hdescent : baseEnd_3726519 < baseStart_3726519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726559 : List Nat := [1, 1, 2, 3, 2, 1, 3, 3, 3, 4]
def baseStart_3726559 : Nat := 118140960795 + 3726559 * 2 ^ 59
def prefixEnd_3726559 : Nat := 4983230072969 + 3 ^ 40 * 3726559 * 2
def baseEnd_3726559 : Nat := 637838651446130184824791

theorem tailTrace_3726559 : CollatzResearch.WordTrace tailWord_3726559 prefixEnd_3726559 637838651446130184824791 := by
  unfold tailWord_3726559
  simp only [CollatzResearch.WordTrace]
  refine ⟨135918772906320663452286731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90612515270880442301524487 135918772906320663452286731)
  ·
    refine ⟨203878159359480995178430097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135918772906320663452286731 203878159359480995178430097)
    ·
      refine ⟨152908619519610746383822573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203878159359480995178430097 152908619519610746383822573)
      ·
        refine ⟨57340732319854029893933465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152908619519610746383822573 57340732319854029893933465)
        ·
          refine ⟨43005549239890522420450099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57340732319854029893933465 43005549239890522420450099)
          ·
            refine ⟨64508323859835783630675149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43005549239890522420450099 64508323859835783630675149)
            ·
              refine ⟨24190621447438418861503181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64508323859835783630675149 24190621447438418861503181)
              ·
                refine ⟨9071483042789407073063693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24190621447438418861503181 9071483042789407073063693)
                ·
                  refine ⟨3401806141046027652398885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9071483042789407073063693 3401806141046027652398885)
                  ·
                    refine ⟨637838651446130184824791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3401806141046027652398885 637838651446130184824791)
                    ·
                      rfl

theorem cell23_3726559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 4].length) (baseStart_3726559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726559 prefixEnd_3726559 := by exact prefixLift 3726559
  have htrace : WordTrace (prefixWord ++ tailWord_3726559) baseStart_3726559 baseEnd_3726559 := by
    simpa [prefixWord, tailWord_3726559, baseEnd_3726559] using wordTrace_append hprefix tailTrace_3726559
  have hstable : (prefixWord ++ tailWord_3726559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726559).length < 2 ^ (prefixWord ++ tailWord_3726559).sum := by decide
  have hdescent : baseEnd_3726559 < baseStart_3726559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726593 : List Nat := [1, 2, 4, 1, 1, 3, 3, 3, 1, 4]
def baseStart_3726593 : Nat := 118140960795 + 3726593 * 2 ^ 59
def prefixEnd_3726593 : Nat := 4983230072969 + 3 ^ 40 * 3726593 * 2
def baseEnd_3726593 : Nat := 637844470893547807149739

theorem tailTrace_3726593 : CollatzResearch.WordTrace tailWord_3726593 prefixEnd_3726593 637844470893547807149739 := by
  unfold tailWord_3726593
  simp only [CollatzResearch.WordTrace]
  refine ⟨135920012988197487259024433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90613341992131658172682955 135920012988197487259024433)
  ·
    refine ⟨101940009741148115444268325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135920012988197487259024433 101940009741148115444268325)
    ·
      refine ⟨19113751826465271645800311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101940009741148115444268325 19113751826465271645800311)
      ·
        refine ⟨28670627739697907468700467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19113751826465271645800311 28670627739697907468700467)
        ·
          refine ⟨43005941609546861203050701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28670627739697907468700467 43005941609546861203050701)
          ·
            refine ⟨16127228103580072951144013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43005941609546861203050701 16127228103580072951144013)
            ·
              refine ⟨6047710538842527356679005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16127228103580072951144013 6047710538842527356679005)
              ·
                refine ⟨2267891452065947758754627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6047710538842527356679005 2267891452065947758754627)
                ·
                  refine ⟨3401837178098921638131941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2267891452065947758754627 3401837178098921638131941)
                  ·
                    refine ⟨637844470893547807149739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3401837178098921638131941 637844470893547807149739)
                    ·
                      rfl

theorem cell23_3726593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_3726593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726593 prefixEnd_3726593 := by exact prefixLift 3726593
  have htrace : WordTrace (prefixWord ++ tailWord_3726593) baseStart_3726593 baseEnd_3726593 := by
    simpa [prefixWord, tailWord_3726593, baseEnd_3726593] using wordTrace_append hprefix tailTrace_3726593
  have hstable : (prefixWord ++ tailWord_3726593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726593).length < 2 ^ (prefixWord ++ tailWord_3726593).sum := by decide
  have hdescent : baseEnd_3726593 < baseStart_3726593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726623 : List Nat := [1, 1, 2, 4, 4, 2, 2, 1, 6]
def baseStart_3726623 : Nat := 118140960795 + 3726623 * 2 ^ 59
def prefixEnd_3726623 : Nat := 4983230072969 + 3 ^ 40 * 3726623 * 2
def baseEnd_3726623 : Nat := 212616535233364256008231

theorem tailTrace_3726623 : CollatzResearch.WordTrace tailWord_3726623 prefixEnd_3726623 212616535233364256008231 := by
  unfold tailWord_3726623
  simp only [CollatzResearch.WordTrace]
  refine ⟨135921107178088802382616523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90614071452059201588411015 135921107178088802382616523)
  ·
    refine ⟨203881660767133203573924785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135921107178088802382616523 203881660767133203573924785)
    ·
      refine ⟨152911245575349902680443589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203881660767133203573924785 152911245575349902680443589)
      ·
        refine ⟨28670858545378106752583173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152911245575349902680443589 28670858545378106752583173)
        ·
          refine ⟨5375785977258395016109345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28670858545378106752583173 5375785977258395016109345)
          ·
            refine ⟨4031839482943796262082009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5375785977258395016109345 4031839482943796262082009)
            ·
              refine ⟨3023879612207847196561507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4031839482943796262082009 3023879612207847196561507)
              ·
                refine ⟨4535819418311770794842261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3023879612207847196561507 4535819418311770794842261)
                ·
                  refine ⟨212616535233364256008231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4535819418311770794842261 212616535233364256008231)
                  ·
                    rfl

theorem cell23_3726623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 6].length) (baseStart_3726623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726623 prefixEnd_3726623 := by exact prefixLift 3726623
  have htrace : WordTrace (prefixWord ++ tailWord_3726623) baseStart_3726623 baseEnd_3726623 := by
    simpa [prefixWord, tailWord_3726623, baseEnd_3726623] using wordTrace_append hprefix tailTrace_3726623
  have hstable : (prefixWord ++ tailWord_3726623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726623).length < 2 ^ (prefixWord ++ tailWord_3726623).sum := by decide
  have hdescent : baseEnd_3726623 < baseStart_3726623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726643 : List Nat := [1, 1, 1, 2, 5, 3, 2, 1, 2, 3, 2]
def baseStart_3726643 : Nat := 118140960795 + 3726643 * 2 ^ 59
def prefixEnd_3726643 : Nat := 4983230072969 + 3 ^ 40 * 3726643 * 2
def baseEnd_3726643 : Nat := 1913559086713368225823987

theorem tailTrace_3726643 : CollatzResearch.WordTrace tailWord_3726643 prefixEnd_3726643 1913559086713368225823987 := by
  unfold tailWord_3726643
  simp only [CollatzResearch.WordTrace]
  refine ⟨135921836638016345798344583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90614557758677563865563055 135921836638016345798344583)
  ·
    refine ⟨203882754957024518697516875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135921836638016345798344583 203882754957024518697516875)
    ·
      refine ⟨305824132435536778046275313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203882754957024518697516875 305824132435536778046275313)
      ·
        refine ⟨229368099326652583534706485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305824132435536778046275313 229368099326652583534706485)
        ·
          refine ⟨21503259311873679706378733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 229368099326652583534706485 21503259311873679706378733)
          ·
            refine ⟨8063722241952629889892025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21503259311873679706378733 8063722241952629889892025)
            ·
              refine ⟨6047791681464472417419019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8063722241952629889892025 6047791681464472417419019)
              ·
                refine ⟨9071687522196708626128529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6047791681464472417419019 9071687522196708626128529)
                ·
                  refine ⟨6803765641647531469596397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9071687522196708626128529 6803765641647531469596397)
                  ·
                    refine ⟨2551412115617824301098649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6803765641647531469596397 2551412115617824301098649)
                    ·
                      refine ⟨1913559086713368225823987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2551412115617824301098649 1913559086713368225823987)
                      ·
                        rfl

theorem cell23_3726643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 3, 2].length) (baseStart_3726643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726643 prefixEnd_3726643 := by exact prefixLift 3726643
  have htrace : WordTrace (prefixWord ++ tailWord_3726643) baseStart_3726643 baseEnd_3726643 := by
    simpa [prefixWord, tailWord_3726643, baseEnd_3726643] using wordTrace_append hprefix tailTrace_3726643
  have hstable : (prefixWord ++ tailWord_3726643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726643).length < 2 ^ (prefixWord ++ tailWord_3726643).sum := by decide
  have hdescent : baseEnd_3726643 < baseStart_3726643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726660 : List Nat := [2, 3, 4, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_3726660 : Nat := 118140960795 + 3726660 * 2 ^ 59
def prefixEnd_3726660 : Nat := 4983230072969 + 3 ^ 40 * 3726660 * 2
def baseEnd_3726660 : Nat := 1913567815884494659311409

theorem tailTrace_3726660 : CollatzResearch.WordTrace tailWord_3726660 prefixEnd_3726660 1913567815884494659311409 := by
  unfold tailWord_3726660
  simp only [CollatzResearch.WordTrace]
  refine ⟨67961228339477378850856717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90614971119303171801142289 67961228339477378850856717)
  ·
    refine ⟨25485460627304017069071269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67961228339477378850856717 25485460627304017069071269)
    ·
      refine ⟨4778523867619503200450863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25485460627304017069071269 4778523867619503200450863)
      ·
        refine ⟨7167785801429254800676295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4778523867619503200450863 7167785801429254800676295)
        ·
          refine ⟨10751678702143882201014443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7167785801429254800676295 10751678702143882201014443)
          ·
            refine ⟨16127518053215823301521665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10751678702143882201014443 16127518053215823301521665)
            ·
              refine ⟨12095638539911867476141249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16127518053215823301521665 12095638539911867476141249)
              ·
                refine ⟨9071728904933900607105937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12095638539911867476141249 9071728904933900607105937)
                ·
                  refine ⟨6803796678700425455329453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9071728904933900607105937 6803796678700425455329453)
                  ·
                    refine ⟨2551423754512659545748545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6803796678700425455329453 2551423754512659545748545)
                    ·
                      refine ⟨1913567815884494659311409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2551423754512659545748545 1913567815884494659311409)
                      ·
                        rfl

theorem cell23_3726660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_3726660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726660 prefixEnd_3726660 := by exact prefixLift 3726660
  have htrace : WordTrace (prefixWord ++ tailWord_3726660) baseStart_3726660 baseEnd_3726660 := by
    simpa [prefixWord, tailWord_3726660, baseEnd_3726660] using wordTrace_append hprefix tailTrace_3726660
  have hstable : (prefixWord ++ tailWord_3726660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726660).length < 2 ^ (prefixWord ++ tailWord_3726660).sum := by decide
  have hdescent : baseEnd_3726660 < baseStart_3726660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726673 : List Nat := [1, 2, 2, 1, 4, 1, 2, 3, 3, 2, 2]
def baseStart_3726673 : Nat := 118140960795 + 3726673 * 2 ^ 59
def prefixEnd_3726673 : Nat := 4983230072969 + 3 ^ 40 * 3726673 * 2
def baseEnd_3726673 : Nat := 1913574491133003108448849

theorem tailTrace_3726673 : CollatzResearch.WordTrace tailWord_3726673 prefixEnd_3726673 1913574491133003108448849 := by
  unfold tailWord_3726673
  simp only [CollatzResearch.WordTrace]
  refine ⟨135922930827907660921936673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90615287218605107281291115 135922930827907660921936673)
  ·
    refine ⟨101942198120930745691452505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135922930827907660921936673 101942198120930745691452505)
    ·
      refine ⟨76456648590698059268589379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101942198120930745691452505 76456648590698059268589379)
      ·
        refine ⟨114684972886047088902884069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76456648590698059268589379 114684972886047088902884069)
        ·
          refine ⟨21503432416133829169290763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114684972886047088902884069 21503432416133829169290763)
          ·
            refine ⟨32255148624200743753936145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21503432416133829169290763 32255148624200743753936145)
            ·
              refine ⟨24191361468150557815452109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32255148624200743753936145 24191361468150557815452109)
              ·
                refine ⟨9071760550556459180794541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24191361468150557815452109 9071760550556459180794541)
                ·
                  refine ⟨3401910206458672192797953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9071760550556459180794541 3401910206458672192797953)
                  ·
                    refine ⟨2551432654844004144598465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3401910206458672192797953 2551432654844004144598465)
                    ·
                      refine ⟨1913574491133003108448849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2551432654844004144598465 1913574491133003108448849)
                      ·
                        rfl

theorem cell23_3726673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3, 2, 2].length) (baseStart_3726673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726673 prefixEnd_3726673 := by exact prefixLift 3726673
  have htrace : WordTrace (prefixWord ++ tailWord_3726673) baseStart_3726673 baseEnd_3726673 := by
    simpa [prefixWord, tailWord_3726673, baseEnd_3726673] using wordTrace_append hprefix tailTrace_3726673
  have hstable : (prefixWord ++ tailWord_3726673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726673).length < 2 ^ (prefixWord ++ tailWord_3726673).sum := by decide
  have hdescent : baseEnd_3726673 < baseStart_3726673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726676 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 5, 2, 3]
def baseStart_3726676 : Nat := 118140960795 + 3726676 * 2 ^ 59
def prefixEnd_3726676 : Nat := 4983230072969 + 3 ^ 40 * 3726676 * 2
def baseEnd_3726676 : Nat := 1913576031574966596711335

theorem tailTrace_3726676 : CollatzResearch.WordTrace tailWord_3726676 prefixEnd_3726676 1913576031574966596711335 := by
  unfold tailWord_3726676
  simp only [CollatzResearch.WordTrace]
  refine ⟨67961520123448396217147941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90615360164597861622863921 67961520123448396217147941)
  ·
    refine ⟨12742785023146574290715239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67961520123448396217147941 12742785023146574290715239)
    ·
      refine ⟨19114177534719861436072859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12742785023146574290715239 19114177534719861436072859)
      ·
        refine ⟨28671266302079792154109289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19114177534719861436072859 28671266302079792154109289)
        ·
          refine ⟨21503449726559844115581967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28671266302079792154109289 21503449726559844115581967)
          ·
            refine ⟨32255174589839766173372951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21503449726559844115581967 32255174589839766173372951)
            ·
              refine ⟨48382761884759649260059427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32255174589839766173372951 48382761884759649260059427)
              ·
                refine ⟨72574142827139473890089141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48382761884759649260059427 72574142827139473890089141)
                ·
                  refine ⟨6803825890044325677195857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72574142827139473890089141 6803825890044325677195857)
                  ·
                    refine ⟨5102869417533244257896893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6803825890044325677195857 5102869417533244257896893)
                    ·
                      refine ⟨1913576031574966596711335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5102869417533244257896893 1913576031574966596711335)
                      ·
                        rfl

theorem cell23_3726676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_3726676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726676 prefixEnd_3726676 := by exact prefixLift 3726676
  have htrace : WordTrace (prefixWord ++ tailWord_3726676) baseStart_3726676 baseEnd_3726676 := by
    simpa [prefixWord, tailWord_3726676, baseEnd_3726676] using wordTrace_append hprefix tailTrace_3726676
  have hstable : (prefixWord ++ tailWord_3726676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726676).length < 2 ^ (prefixWord ++ tailWord_3726676).sum := by decide
  have hdescent : baseEnd_3726676 < baseStart_3726676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726679 : List Nat := [1, 1, 3, 2, 3, 2, 3, 8]
def baseStart_3726679 : Nat := 118140960795 + 3726679 * 2 ^ 59
def prefixEnd_3726679 : Nat := 4983230072969 + 3 ^ 40 * 3726679 * 2
def baseEnd_3726679 : Nat := 70873243408034447591623

theorem tailTrace_3726679 : CollatzResearch.WordTrace tailWord_3726679 prefixEnd_3726679 70873243408034447591623 := by
  unfold tailWord_3726679
  simp only [CollatzResearch.WordTrace]
  refine ⟨135923149665885923946655091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90615433110590615964436727 135923149665885923946655091)
  ·
    refine ⟨203884724498828885919982637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135923149665885923946655091 203884724498828885919982637)
    ·
      refine ⟨76456771687060832219993489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203884724498828885919982637 76456771687060832219993489)
      ·
        refine ⟨57342578765295624164995117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76456771687060832219993489 57342578765295624164995117)
        ·
          refine ⟨21503467036985859061873169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57342578765295624164995117 21503467036985859061873169)
          ·
            refine ⟨16127600277739394296404877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21503467036985859061873169 16127600277739394296404877)
            ·
              refine ⟨6047850104152272861151829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16127600277739394296404877 6047850104152272861151829)
              ·
                refine ⟨70873243408034447591623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6047850104152272861151829 70873243408034447591623)
                ·
                  rfl

theorem cell23_3726679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 8].length) (baseStart_3726679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726679 prefixEnd_3726679 := by exact prefixLift 3726679
  have htrace : WordTrace (prefixWord ++ tailWord_3726679) baseStart_3726679 baseEnd_3726679 := by
    simpa [prefixWord, tailWord_3726679, baseEnd_3726679] using wordTrace_append hprefix tailTrace_3726679
  have hstable : (prefixWord ++ tailWord_3726679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726679).length < 2 ^ (prefixWord ++ tailWord_3726679).sum := by decide
  have hdescent : baseEnd_3726679 < baseStart_3726679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726690 : List Nat := [3, 3, 2, 1, 1, 1, 3, 2, 3, 2, 2]
def baseStart_3726690 : Nat := 118140960795 + 3726690 * 2 ^ 59
def prefixEnd_3726690 : Nat := 4983230072969 + 3 ^ 40 * 3726690 * 2
def baseEnd_3726690 : Nat := 1913583220304129541936271

theorem tailTrace_3726690 : CollatzResearch.WordTrace tailWord_3726690 prefixEnd_3726690 1913583220304129541936271 := by
  unfold tailWord_3726690
  simp only [CollatzResearch.WordTrace]
  refine ⟨33980887717211518206326381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90615700579230715216870349 33980887717211518206326381)
  ·
    refine ⟨12742832893954319327372393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33980887717211518206326381 12742832893954319327372393)
    ·
      refine ⟨9557124670465739495529295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12742832893954319327372393 9557124670465739495529295)
      ·
        refine ⟨14335687005698609243293943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9557124670465739495529295 14335687005698609243293943)
        ·
          refine ⟨21503530508547913864940915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14335687005698609243293943 21503530508547913864940915)
          ·
            refine ⟨32255295762821870797411373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21503530508547913864940915 32255295762821870797411373)
            ·
              refine ⟨12095735911058201549029265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32255295762821870797411373 12095735911058201549029265)
              ·
                refine ⟨9071801933293651161771949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12095735911058201549029265 9071801933293651161771949)
                ·
                  refine ⟨3401925724985119185664481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9071801933293651161771949 3401925724985119185664481)
                  ·
                    refine ⟨2551444293738839389248361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3401925724985119185664481 2551444293738839389248361)
                    ·
                      refine ⟨1913583220304129541936271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2551444293738839389248361 1913583220304129541936271)
                      ·
                        rfl

theorem cell23_3726690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_3726690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726690 prefixEnd_3726690 := by exact prefixLift 3726690
  have htrace : WordTrace (prefixWord ++ tailWord_3726690) baseStart_3726690 baseEnd_3726690 := by
    simpa [prefixWord, tailWord_3726690, baseEnd_3726690] using wordTrace_append hprefix tailTrace_3726690
  have hstable : (prefixWord ++ tailWord_3726690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726690).length < 2 ^ (prefixWord ++ tailWord_3726690).sum := by decide
  have hdescent : baseEnd_3726690 < baseStart_3726690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726706 : List Nat := [3, 2, 1, 2, 1, 2, 1, 4, 1, 3, 3]
def baseStart_3726706 : Nat := 118140960795 + 3726706 * 2 ^ 59
def prefixEnd_3726706 : Nat := 4983230072969 + 3 ^ 40 * 3726706 * 2
def baseEnd_3726706 : Nat := 1913591435994601479336197

theorem tailTrace_3726706 : CollatzResearch.WordTrace tailWord_3726706 prefixEnd_3726706 1913591435994601479336197 := by
  unfold tailWord_3726706
  simp only [CollatzResearch.WordTrace]
  refine ⟨33981033609197026889471993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90616089624525405038591981 33981033609197026889471993)
  ·
    refine ⟨25485775206897770167103995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33981033609197026889471993 25485775206897770167103995)
    ·
      refine ⟨38228662810346655250655993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25485775206897770167103995 38228662810346655250655993)
      ·
        refine ⟨28671497107759991437991995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38228662810346655250655993 28671497107759991437991995)
        ·
          refine ⟨43007245661639987156987993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28671497107759991437991995 43007245661639987156987993)
          ·
            refine ⟨32255434246229990367740995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43007245661639987156987993 32255434246229990367740995)
            ·
              refine ⟨48383151369344985551611493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32255434246229990367740995 48383151369344985551611493)
              ·
                refine ⟨9071840881752184790927155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48383151369344985551611493 9071840881752184790927155)
                ·
                  refine ⟨13607761322628277186390733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9071840881752184790927155 13607761322628277186390733)
                  ·
                    refine ⟨5102910495985603944896525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13607761322628277186390733 5102910495985603944896525)
                    ·
                      refine ⟨1913591435994601479336197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5102910495985603944896525 1913591435994601479336197)
                      ·
                        rfl

theorem cell23_3726706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_3726706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726706 prefixEnd_3726706 := by exact prefixLift 3726706
  have htrace : WordTrace (prefixWord ++ tailWord_3726706) baseStart_3726706 baseEnd_3726706 := by
    simpa [prefixWord, tailWord_3726706, baseEnd_3726706] using wordTrace_append hprefix tailTrace_3726706
  have hstable : (prefixWord ++ tailWord_3726706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726706).length < 2 ^ (prefixWord ++ tailWord_3726706).sum := by decide
  have hdescent : baseEnd_3726706 < baseStart_3726706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726723 : List Nat := [1, 1, 1, 3, 5, 2, 1, 1, 4, 1, 3]
def baseStart_3726723 : Nat := 118140960795 + 3726723 * 2 ^ 59
def prefixEnd_3726723 : Nat := 4983230072969 + 3 ^ 40 * 3726723 * 2
def baseEnd_3726723 : Nat := 1913600165165727912823619

theorem tailTrace_3726723 : CollatzResearch.WordTrace tailWord_3726723 prefixEnd_3726723 1913600165165727912823619 := by
  unfold tailWord_3726723
  simp only [CollatzResearch.WordTrace]
  refine ⟨135924754477726519461256823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90616502985151012974171215 135924754477726519461256823)
  ·
    refine ⟨203887131716589779191885235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135924754477726519461256823 203887131716589779191885235)
    ·
      refine ⟨305830697574884668787827853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203887131716589779191885235 305830697574884668787827853)
      ·
        refine ⟨114686511590581750795435445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305830697574884668787827853 114686511590581750795435445)
        ·
          refine ⟨10751860461617039137072073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114686511590581750795435445 10751860461617039137072073)
          ·
            refine ⟨8063895346212779352804055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10751860461617039137072073 8063895346212779352804055)
            ·
              refine ⟨12095843019319169029206083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8063895346212779352804055 12095843019319169029206083)
              ·
                refine ⟨18143764528978753543809125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12095843019319169029206083 18143764528978753543809125)
                ·
                  refine ⟨3401955849183516289464211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18143764528978753543809125 3401955849183516289464211)
                  ·
                    refine ⟨5102933773775274434196317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3401955849183516289464211 5102933773775274434196317)
                    ·
                      refine ⟨1913600165165727912823619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5102933773775274434196317 1913600165165727912823619)
                      ·
                        rfl

theorem cell23_3726723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4, 1, 3].length) (baseStart_3726723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726723 prefixEnd_3726723 := by exact prefixLift 3726723
  have htrace : WordTrace (prefixWord ++ tailWord_3726723) baseStart_3726723 baseEnd_3726723 := by
    simpa [prefixWord, tailWord_3726723, baseEnd_3726723] using wordTrace_append hprefix tailTrace_3726723
  have hstable : (prefixWord ++ tailWord_3726723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726723).length < 2 ^ (prefixWord ++ tailWord_3726723).sum := by decide
  have hdescent : baseEnd_3726723 < baseStart_3726723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726740 : List Nat := [2, 4, 2, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_3726740 : Nat := 118140960795 + 3726740 * 2 ^ 59
def prefixEnd_3726740 : Nat := 4983230072969 + 3 ^ 40 * 3726740 * 2
def baseEnd_3726740 : Nat := 1913608894336854346311041

theorem tailTrace_3726740 : CollatzResearch.WordTrace tailWord_3726740 prefixEnd_3726740 1913608894336854346311041 := by
  unfold tailWord_3726740
  simp only [CollatzResearch.WordTrace]
  refine ⟨67962687259332465682312837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90616916345776620909750449 67962687259332465682312837)
  ·
    refine ⟨12743003861124837315433657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67962687259332465682312837 12743003861124837315433657)
    ·
      refine ⟨9557252895843627986575243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12743003861124837315433657 9557252895843627986575243)
      ·
        refine ⟨14335879343765441979862865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9557252895843627986575243 14335879343765441979862865)
        ·
          refine ⟨10751909507824081484897149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14335879343765441979862865 10751909507824081484897149)
          ·
            refine ⟨4031966065434030556836431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10751909507824081484897149 4031966065434030556836431)
            ·
              refine ⟨6047949098151045835254647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4031966065434030556836431 6047949098151045835254647)
              ·
                refine ⟨9071923647226568752881971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6047949098151045835254647 9071923647226568752881971)
                ·
                  refine ⟨13607885470839853129322957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9071923647226568752881971 13607885470839853129322957)
                  ·
                    refine ⟨5102957051564944923496109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13607885470839853129322957 5102957051564944923496109)
                    ·
                      refine ⟨1913608894336854346311041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5102957051564944923496109 1913608894336854346311041)
                      ·
                        rfl

theorem cell23_3726740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_3726740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726740 prefixEnd_3726740 := by exact prefixLift 3726740
  have htrace : WordTrace (prefixWord ++ tailWord_3726740) baseStart_3726740 baseEnd_3726740 := by
    simpa [prefixWord, tailWord_3726740, baseEnd_3726740] using wordTrace_append hprefix tailTrace_3726740
  have hstable : (prefixWord ++ tailWord_3726740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726740).length < 2 ^ (prefixWord ++ tailWord_3726740).sum := by decide
  have hdescent : baseEnd_3726740 < baseStart_3726740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726799 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 3, 7]
def baseStart_3726799 : Nat := 118140960795 + 3726799 * 2 ^ 59
def prefixEnd_3726799 : Nat := 4983230072969 + 3 ^ 40 * 3726799 * 2
def baseEnd_3726799 : Nat := 637879729898489871824423

theorem tailTrace_3726799 : CollatzResearch.WordTrace tailWord_3726799 prefixEnd_3726799 637879729898489871824423 := by
  unfold tailWord_3726799
  simp only [CollatzResearch.WordTrace]
  refine ⟨135927526425451184441023451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90618350950300789627348967 135927526425451184441023451)
  ·
    refine ⟨203891289638176776661535177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135927526425451184441023451 203891289638176776661535177)
    ·
      refine ⟨152918467228632582496151383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203891289638176776661535177 152918467228632582496151383)
      ·
        refine ⟨229377700842948873744227075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152918467228632582496151383 229377700842948873744227075)
        ·
          refine ⟨344066551264423310616340613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229377700842948873744227075 344066551264423310616340613)
          ·
            refine ⟨64512478362079370740563865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 344066551264423310616340613 64512478362079370740563865)
            ·
              refine ⟨48384358771559528055422899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64512478362079370740563865 48384358771559528055422899)
              ·
                refine ⟨72576538157339292083134349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48384358771559528055422899 72576538157339292083134349)
                ·
                  refine ⟨27216201809002234531175381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72576538157339292083134349 27216201809002234531175381)
                  ·
                    refine ⟨637879729898489871824423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27216201809002234531175381 637879729898489871824423)
                    ·
                      rfl

theorem cell23_3726799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 7].length) (baseStart_3726799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726799 prefixEnd_3726799 := by exact prefixLift 3726799
  have htrace : WordTrace (prefixWord ++ tailWord_3726799) baseStart_3726799 baseEnd_3726799 := by
    simpa [prefixWord, tailWord_3726799, baseEnd_3726799] using wordTrace_append hprefix tailTrace_3726799
  have hstable : (prefixWord ++ tailWord_3726799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726799).length < 2 ^ (prefixWord ++ tailWord_3726799).sum := by decide
  have hdescent : baseEnd_3726799 < baseStart_3726799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726837 : List Nat := [1, 3, 5, 1, 1, 1, 4, 2, 5]
def baseStart_3726837 : Nat := 118140960795 + 3726837 * 2 ^ 59
def prefixEnd_3726837 : Nat := 4983230072969 + 3 ^ 40 * 3726837 * 2
def baseEnd_3726837 : Nat := 212628744662260051866455

theorem tailTrace_3726837 : CollatzResearch.WordTrace tailWord_3726837 prefixEnd_3726837 212628744662260051866455 := by
  unfold tailWord_3726837
  simp only [CollatzResearch.WordTrace]
  refine ⟨135928912399313516930906765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90619274932875677953937843 135928912399313516930906765)
  ·
    refine ⟨50973342149742568849090037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135928912399313516930906765 50973342149742568849090037)
    ·
      refine ⟨4778750826538365829602191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50973342149742568849090037 4778750826538365829602191)
      ·
        refine ⟨7168126239807548744403287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4778750826538365829602191 7168126239807548744403287)
        ·
          refine ⟨10752189359711323116604931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7168126239807548744403287 10752189359711323116604931)
          ·
            refine ⟨16128284039566984674907397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10752189359711323116604931 16128284039566984674907397)
            ·
              refine ⟨3024053257418809626545137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16128284039566984674907397 3024053257418809626545137)
              ·
                refine ⟨2268039943064107219908853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3024053257418809626545137 2268039943064107219908853)
                ·
                  refine ⟨212628744662260051866455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2268039943064107219908853 212628744662260051866455)
                  ·
                    rfl

theorem cell23_3726837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2, 5].length) (baseStart_3726837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726837 prefixEnd_3726837 := by exact prefixLift 3726837
  have htrace : WordTrace (prefixWord ++ tailWord_3726837) baseStart_3726837 baseEnd_3726837 := by
    simpa [prefixWord, tailWord_3726837, baseEnd_3726837] using wordTrace_append hprefix tailTrace_3726837
  have hstable : (prefixWord ++ tailWord_3726837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726837).length < 2 ^ (prefixWord ++ tailWord_3726837).sum := by decide
  have hdescent : baseEnd_3726837 < baseStart_3726837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726876 : List Nat := [2, 2, 3, 1, 2, 1, 2, 2, 8]
def baseStart_3726876 : Nat := 118140960795 + 3726876 * 2 ^ 59
def prefixEnd_3726876 : Nat := 4983230072969 + 3 ^ 40 * 3726876 * 2
def baseEnd_3726876 : Nat := 212630969745096201578935

theorem tailTrace_3726876 : CollatzResearch.WordTrace tailWord_3726876 prefixEnd_3726876 212630969745096201578935 := by
  unfold tailWord_3726876
  simp only [CollatzResearch.WordTrace]
  refine ⟨67965167423086113295788241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90620223230781484394384321 67965167423086113295788241)
  ·
    refine ⟨50973875567314584971841181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67965167423086113295788241 50973875567314584971841181)
    ·
      refine ⟨19115203337742969364440443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50973875567314584971841181 19115203337742969364440443)
      ·
        refine ⟨28672805006614454046660665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19115203337742969364440443 28672805006614454046660665)
        ·
          refine ⟨21504603754960840534995499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28672805006614454046660665 21504603754960840534995499)
          ·
            refine ⟨32256905632441260802493249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21504603754960840534995499 32256905632441260802493249)
            ·
              refine ⟨24192679224330945601869937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32256905632441260802493249 24192679224330945601869937)
              ·
                refine ⟨18144509418248209201402453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24192679224330945601869937 18144509418248209201402453)
                ·
                  refine ⟨212630969745096201578935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18144509418248209201402453 212630969745096201578935)
                  ·
                    rfl

theorem cell23_3726876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 8].length) (baseStart_3726876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726876 prefixEnd_3726876 := by exact prefixLift 3726876
  have htrace : WordTrace (prefixWord ++ tailWord_3726876) baseStart_3726876 baseEnd_3726876 := by
    simpa [prefixWord, tailWord_3726876, baseEnd_3726876] using wordTrace_append hprefix tailTrace_3726876
  have hstable : (prefixWord ++ tailWord_3726876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726876).length < 2 ^ (prefixWord ++ tailWord_3726876).sum := by decide
  have hdescent : baseEnd_3726876 < baseStart_3726876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726930 : List Nat := [3, 2, 2, 1, 2, 2, 2, 1, 1, 5, 2]
def baseStart_3726930 : Nat := 118140960795 + 3726930 * 2 ^ 59
def prefixEnd_3726930 : Nat := 4983230072969 + 3 ^ 40 * 3726930 * 2
def baseEnd_3726930 : Nat := 1913706455661208602935167

theorem tailTrace_3726930 : CollatzResearch.WordTrace tailWord_3726930 prefixEnd_3726930 1913706455661208602935167 := by
  unfold tailWord_3726930
  simp only [CollatzResearch.WordTrace]
  refine ⟨33983076096994148453510561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90621536258651062542694829 33983076096994148453510561)
  ·
    refine ⟨25487307072745611340132921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33983076096994148453510561 25487307072745611340132921)
    ·
      refine ⟨19115480304559208505099691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25487307072745611340132921 19115480304559208505099691)
      ·
        refine ⟨28673220456838812757649537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19115480304559208505099691 28673220456838812757649537)
        ·
          refine ⟨21504915342629109568237153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28673220456838812757649537 21504915342629109568237153)
          ·
            refine ⟨16128686506971832176177865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21504915342629109568237153 16128686506971832176177865)
            ·
              refine ⟨12096514880228874132133399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16128686506971832176177865 12096514880228874132133399)
              ·
                refine ⟨18144772320343311198200099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12096514880228874132133399 18144772320343311198200099)
                ·
                  refine ⟨27217158480514966797300149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18144772320343311198200099 27217158480514966797300149)
                  ·
                    refine ⟨2551608607548278137246889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27217158480514966797300149 2551608607548278137246889)
                    ·
                      refine ⟨1913706455661208602935167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2551608607548278137246889 1913706455661208602935167)
                      ·
                        rfl

theorem cell23_3726930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_3726930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726930 prefixEnd_3726930 := by exact prefixLift 3726930
  have htrace : WordTrace (prefixWord ++ tailWord_3726930) baseStart_3726930 baseEnd_3726930 := by
    simpa [prefixWord, tailWord_3726930, baseEnd_3726930] using wordTrace_append hprefix tailTrace_3726930
  have hstable : (prefixWord ++ tailWord_3726930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726930).length < 2 ^ (prefixWord ++ tailWord_3726930).sum := by decide
  have hdescent : baseEnd_3726930 < baseStart_3726930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726936 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 3, 6]
def baseStart_3726936 : Nat := 118140960795 + 3726936 * 2 ^ 59
def prefixEnd_3726936 : Nat := 4983230072969 + 3 ^ 40 * 3726936 * 2
def baseEnd_3726936 : Nat := 637903178848378526486713

theorem tailTrace_3726936 : CollatzResearch.WordTrace tailWord_3726936 prefixEnd_3726936 637903178848378526486713 := by
  unfold tailWord_3726936
  simp only [CollatzResearch.WordTrace]
  refine ⟨67966261612977428419380331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90621682150636571225840441 67966261612977428419380331)
  ·
    refine ⟨101949392419466142629070497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67966261612977428419380331 101949392419466142629070497)
    ·
      refine ⟨76462044314599606971802873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101949392419466142629070497 76462044314599606971802873)
      ·
        refine ⟨57346533235949705228852155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76462044314599606971802873 57346533235949705228852155)
        ·
          refine ⟨86019799853924557843278233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57346533235949705228852155 86019799853924557843278233)
          ·
            refine ⟨64514849890443418382458675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86019799853924557843278233 64514849890443418382458675)
            ·
              refine ⟨96772274835665127573688013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64514849890443418382458675 96772274835665127573688013)
              ·
                refine ⟨36289603063374422840133005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96772274835665127573688013 36289603063374422840133005)
                ·
                  refine ⟨13608601148765408565049877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36289603063374422840133005 13608601148765408565049877)
                  ·
                    refine ⟨637903178848378526486713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13608601148765408565049877 637903178848378526486713)
                    ·
                      rfl

theorem cell23_3726936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 3, 6].length) (baseStart_3726936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726936 prefixEnd_3726936 := by exact prefixLift 3726936
  have htrace : WordTrace (prefixWord ++ tailWord_3726936) baseStart_3726936 baseEnd_3726936 := by
    simpa [prefixWord, tailWord_3726936, baseEnd_3726936] using wordTrace_append hprefix tailTrace_3726936
  have hstable : (prefixWord ++ tailWord_3726936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726936).length < 2 ^ (prefixWord ++ tailWord_3726936).sum := by decide
  have hdescent : baseEnd_3726936 < baseStart_3726936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726940 : List Nat := [2, 2, 4, 1, 2, 1, 2, 3, 1, 5]
def baseStart_3726940 : Nat := 118140960795 + 3726940 * 2 ^ 59
def prefixEnd_3726940 : Nat := 4983230072969 + 3 ^ 40 * 3726940 * 2
def baseEnd_3726940 : Nat := 637903863489251187936707

theorem tailTrace_3726940 : CollatzResearch.WordTrace tailWord_3726940 prefixEnd_3726940 637903863489251187936707 := by
  unfold tailWord_3726940
  simp only [CollatzResearch.WordTrace]
  refine ⟨67966334558970182760953137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90621779411960243681270849 67966334558970182760953137)
  ·
    refine ⟨50974750919227637070714853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67966334558970182760953137 50974750919227637070714853)
    ·
      refine ⟨9557765797355181950759035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50974750919227637070714853 9557765797355181950759035)
      ·
        refine ⟨14336648696032772926138553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9557765797355181950759035 14336648696032772926138553)
        ·
          refine ⟨10752486522024579694603915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14336648696032772926138553 10752486522024579694603915)
          ·
            refine ⟨16128729783036869541905873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10752486522024579694603915 16128729783036869541905873)
            ·
              refine ⟨12096547337277652156429405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16128729783036869541905873 12096547337277652156429405)
              ·
                refine ⟨4536205251479119558661027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12096547337277652156429405 4536205251479119558661027)
                ·
                  refine ⟨6804307877218679337991541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4536205251479119558661027 6804307877218679337991541)
                  ·
                    refine ⟨637903863489251187936707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6804307877218679337991541 637903863489251187936707)
                    ·
                      rfl

theorem cell23_3726940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_3726940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726940 prefixEnd_3726940 := by exact prefixLift 3726940
  have htrace : WordTrace (prefixWord ++ tailWord_3726940) baseStart_3726940 baseEnd_3726940 := by
    simpa [prefixWord, tailWord_3726940, baseEnd_3726940] using wordTrace_append hprefix tailTrace_3726940
  have hstable : (prefixWord ++ tailWord_3726940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726940).length < 2 ^ (prefixWord ++ tailWord_3726940).sum := by decide
  have hdescent : baseEnd_3726940 < baseStart_3726940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726953 : List Nat := [1, 2, 1, 1, 1, 4, 4, 1, 4, 4]
def baseStart_3726953 : Nat := 118140960795 + 3726953 * 2 ^ 59
def prefixEnd_3726953 : Nat := 4983230072969 + 3 ^ 40 * 3726953 * 2
def baseEnd_3726953 : Nat := 637906088572087337649187

theorem tailTrace_3726953 : CollatzResearch.WordTrace tailWord_3726953 prefixEnd_3726953 637906088572087337649187 := by
  unfold tailWord_3726953
  simp only [CollatzResearch.WordTrace]
  refine ⟨135933143266893268742129513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90622095511262179161419675 135933143266893268742129513)
  ·
    refine ⟨101949857450169951556597135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135933143266893268742129513 101949857450169951556597135)
    ·
      refine ⟨152924786175254927334895703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101949857450169951556597135 152924786175254927334895703)
      ·
        refine ⟨229387179262882391002343555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152924786175254927334895703 229387179262882391002343555)
        ·
          refine ⟨344080768894323586503515333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229387179262882391002343555 344080768894323586503515333)
          ·
            refine ⟨64515144167685672469409125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 344080768894323586503515333 64515144167685672469409125)
            ·
              refine ⟨12096589531441063588014211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64515144167685672469409125 12096589531441063588014211)
              ·
                refine ⟨18144884297161595382021317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12096589531441063588014211 18144884297161595382021317)
                ·
                  refine ⟨3402165805717799134128997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18144884297161595382021317 3402165805717799134128997)
                  ·
                    refine ⟨637906088572087337649187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3402165805717799134128997 637906088572087337649187)
                    ·
                      rfl

theorem cell23_3726953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4, 4].length) (baseStart_3726953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726953 prefixEnd_3726953 := by exact prefixLift 3726953
  have htrace : WordTrace (prefixWord ++ tailWord_3726953) baseStart_3726953 baseEnd_3726953 := by
    simpa [prefixWord, tailWord_3726953, baseEnd_3726953] using wordTrace_append hprefix tailTrace_3726953
  have hstable : (prefixWord ++ tailWord_3726953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726953).length < 2 ^ (prefixWord ++ tailWord_3726953).sum := by decide
  have hdescent : baseEnd_3726953 < baseStart_3726953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726973 : List Nat := [1, 4, 1, 1, 4, 1, 2, 1, 1, 1, 6]
def baseStart_3726973 : Nat := 118140960795 + 3726973 * 2 ^ 59
def prefixEnd_3726973 : Nat := 4983230072969 + 3 ^ 40 * 3726973 * 2
def baseEnd_3726973 : Nat := 1913728535329351934697469

theorem tailTrace_3726973 : CollatzResearch.WordTrace tailWord_3726973 prefixEnd_3726973 1913728535329351934697469 := by
  unfold tailWord_3726973
  simp only [CollatzResearch.WordTrace]
  refine ⟨135933872726820812157857573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90622581817880541438571715 135933872726820812157857573)
  ·
    refine ⟨25487601136278902279598295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135933872726820812157857573 25487601136278902279598295)
    ·
      refine ⟨38231401704418353419397443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25487601136278902279598295 38231401704418353419397443)
      ·
        refine ⟨57347102556627530129096165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38231401704418353419397443 57347102556627530129096165)
        ·
          refine ⟨10752581729367661899205531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57347102556627530129096165 10752581729367661899205531)
          ·
            refine ⟨16128872594051492848808297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10752581729367661899205531 16128872594051492848808297)
            ·
              refine ⟨12096654445538619636606223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16128872594051492848808297 12096654445538619636606223)
              ·
                refine ⟨18144981668307929454909335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12096654445538619636606223 18144981668307929454909335)
                ·
                  refine ⟨27217472502461894182364003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18144981668307929454909335 27217472502461894182364003)
                  ·
                    refine ⟨40826208753692841273546005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27217472502461894182364003 40826208753692841273546005)
                    ·
                      refine ⟨1913728535329351934697469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40826208753692841273546005 1913728535329351934697469)
                      ·
                        rfl

theorem cell23_3726973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_3726973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726973 prefixEnd_3726973 := by exact prefixLift 3726973
  have htrace : WordTrace (prefixWord ++ tailWord_3726973) baseStart_3726973 baseEnd_3726973 := by
    simpa [prefixWord, tailWord_3726973, baseEnd_3726973] using wordTrace_append hprefix tailTrace_3726973
  have hstable : (prefixWord ++ tailWord_3726973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726973).length < 2 ^ (prefixWord ++ tailWord_3726973).sum := by decide
  have hdescent : baseEnd_3726973 < baseStart_3726973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726977 : List Nat := [1, 2, 4, 2, 1, 4, 1, 2, 1, 1, 4]
def baseStart_3726977 : Nat := 118140960795 + 3726977 * 2 ^ 59
def prefixEnd_3726977 : Nat := 4983230072969 + 3 ^ 40 * 3726977 * 2
def baseEnd_3726977 : Nat := 1913730589251969919047451

theorem tailTrace_3726977 : CollatzResearch.WordTrace tailWord_3726977 prefixEnd_3726977 1913730589251969919047451 := by
  unfold tailWord_3726977
  simp only [CollatzResearch.WordTrace]
  refine ⟨135934018618806320841003185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90622679079204213894002123 135934018618806320841003185)
  ·
    refine ⟨101950513964104740630752389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135934018618806320841003185 101950513964104740630752389)
    ·
      refine ⟨19115721368269638868266073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101950513964104740630752389 19115721368269638868266073)
      ·
        refine ⟨14336791026202229151199555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19115721368269638868266073 14336791026202229151199555)
        ·
          refine ⟨21505186539303343726799333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14336791026202229151199555 21505186539303343726799333)
          ·
            refine ⟨4032222476119376948774875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21505186539303343726799333 4032222476119376948774875)
            ·
              refine ⟨6048333714179065423162313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4032222476119376948774875 6048333714179065423162313)
              ·
                refine ⟨4536250285634299067371735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6048333714179065423162313 4536250285634299067371735)
                ·
                  refine ⟨6804375428451448601057603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4536250285634299067371735 6804375428451448601057603)
                  ·
                    refine ⟨10206563142677172901586405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6804375428451448601057603 10206563142677172901586405)
                    ·
                      refine ⟨1913730589251969919047451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10206563142677172901586405 1913730589251969919047451)
                      ·
                        rfl

theorem cell23_3726977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_3726977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726977 prefixEnd_3726977 := by exact prefixLift 3726977
  have htrace : WordTrace (prefixWord ++ tailWord_3726977) baseStart_3726977 baseEnd_3726977 := by
    simpa [prefixWord, tailWord_3726977, baseEnd_3726977] using wordTrace_append hprefix tailTrace_3726977
  have hstable : (prefixWord ++ tailWord_3726977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726977).length < 2 ^ (prefixWord ++ tailWord_3726977).sum := by decide
  have hdescent : baseEnd_3726977 < baseStart_3726977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726990 : List Nat := [4, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4]
def baseStart_3726990 : Nat := 118140960795 + 3726990 * 2 ^ 59
def prefixEnd_3726990 : Nat := 4983230072969 + 3 ^ 40 * 3726990 * 2
def baseEnd_3726990 : Nat := 1913737264500478368184891

theorem tailTrace_3726990 : CollatzResearch.WordTrace tailWord_3726990 prefixEnd_3726990 1913737264500478368184891 := by
  unfold tailWord_3726990
  simp only [CollatzResearch.WordTrace]
  refine ⟨16991811595969903007653303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90622995178506149374150949 16991811595969903007653303)
  ·
    refine ⟨25487717393954854511479955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16991811595969903007653303 25487717393954854511479955)
    ·
      refine ⟨38231576090932281767219933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25487717393954854511479955 38231576090932281767219933)
      ·
        refine ⟨14336841034099605662707475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38231576090932281767219933 14336841034099605662707475)
        ·
          refine ⟨21505261551149408494061213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14336841034099605662707475 21505261551149408494061213)
          ·
            refine ⟨8064473081681028185272955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21505261551149408494061213 8064473081681028185272955)
            ·
              refine ⟨12096709622521542277909433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8064473081681028185272955 12096709622521542277909433)
              ·
                refine ⟨9072532216891156708432075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12096709622521542277909433 9072532216891156708432075)
                ·
                  refine ⟨13608798325336735062648113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9072532216891156708432075 13608798325336735062648113)
                  ·
                    refine ⟨10206598744002551296986085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13608798325336735062648113 10206598744002551296986085)
                    ·
                      refine ⟨1913737264500478368184891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10206598744002551296986085 1913737264500478368184891)
                      ·
                        rfl

theorem cell23_3726990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_3726990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726990 prefixEnd_3726990 := by exact prefixLift 3726990
  have htrace : WordTrace (prefixWord ++ tailWord_3726990) baseStart_3726990 baseEnd_3726990 := by
    simpa [prefixWord, tailWord_3726990, baseEnd_3726990] using wordTrace_append hprefix tailTrace_3726990
  have hstable : (prefixWord ++ tailWord_3726990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726990).length < 2 ^ (prefixWord ++ tailWord_3726990).sum := by decide
  have hdescent : baseEnd_3726990 < baseStart_3726990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3726994 : List Nat := [3, 2, 3, 1, 3, 1, 3, 1, 1, 1, 4]
def baseStart_3726994 : Nat := 118140960795 + 3726994 * 2 ^ 59
def prefixEnd_3726994 : Nat := 4983230072969 + 3 ^ 40 * 3726994 * 2
def baseEnd_3726994 : Nat := 1913739318423096352534873

theorem tailTrace_3726994 : CollatzResearch.WordTrace tailWord_3726994 prefixEnd_3726994 1913739318423096352534873 := by
  unfold tailWord_3726994
  simp only [CollatzResearch.WordTrace]
  refine ⟨33983659664936183186093009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90623092439829821829581357 33983659664936183186093009)
  ·
    refine ⟨25487744748702137389569757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33983659664936183186093009 25487744748702137389569757)
    ·
      refine ⟨9557904280763301521088659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25487744748702137389569757 9557904280763301521088659)
      ·
        refine ⟨14336856421144952281632989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9557904280763301521088659 14336856421144952281632989)
        ·
          refine ⟨5376321157929357105612371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14336856421144952281632989 5376321157929357105612371)
          ·
            refine ⟨8064481736894035658418557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5376321157929357105612371 8064481736894035658418557)
            ·
              refine ⟨3024180651335263371906959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8064481736894035658418557 3024180651335263371906959)
              ·
                refine ⟨4536270977002895057860439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3024180651335263371906959 4536270977002895057860439)
                ·
                  refine ⟨6804406465504342586790659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4536270977002895057860439 6804406465504342586790659)
                  ·
                    refine ⟨10206609698256513880185989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6804406465504342586790659 10206609698256513880185989)
                    ·
                      refine ⟨1913739318423096352534873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10206609698256513880185989 1913739318423096352534873)
                      ·
                        rfl

theorem cell23_3726994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_3726994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3726994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3726994 prefixEnd_3726994 := by exact prefixLift 3726994
  have htrace : WordTrace (prefixWord ++ tailWord_3726994) baseStart_3726994 baseEnd_3726994 := by
    simpa [prefixWord, tailWord_3726994, baseEnd_3726994] using wordTrace_append hprefix tailTrace_3726994
  have hstable : (prefixWord ++ tailWord_3726994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3726994).length < 2 ^ (prefixWord ++ tailWord_3726994).sum := by decide
  have hdescent : baseEnd_3726994 < baseStart_3726994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3726994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727037 : List Nat := [1, 4, 1, 2, 1, 2, 2, 4, 1, 3, 2]
def baseStart_3727037 : Nat := 118140960795 + 3727037 * 2 ^ 59
def prefixEnd_3727037 : Nat := 4983230072969 + 3 ^ 40 * 3727037 * 2
def baseEnd_3727037 : Nat := 1913761398091239684297175

theorem tailTrace_3727037 : CollatzResearch.WordTrace tailWord_3727037 prefixEnd_3727037 1913761398091239684297175 := by
  unfold tailWord_3727037
  simp only [CollatzResearch.WordTrace]
  refine ⟨135936206998588951088187365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90624137999059300725458243 135936206998588951088187365)
  ·
    refine ⟨25488038812235428329035131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135936206998588951088187365 25488038812235428329035131)
    ·
      refine ⟨38232058218353142493552697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25488038812235428329035131 38232058218353142493552697)
      ·
        refine ⟨28674043663764856870164523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38232058218353142493552697 28674043663764856870164523)
        ·
          refine ⟨43011065495647285305246785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28674043663764856870164523 43011065495647285305246785)
          ·
            refine ⟨32258299121735463978935089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43011065495647285305246785 32258299121735463978935089)
            ·
              refine ⟨24193724341301597984201317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32258299121735463978935089 24193724341301597984201317)
              ·
                refine ⟨4536323313994049622037747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24193724341301597984201317 4536323313994049622037747)
                ·
                  refine ⟨6804484970991074433056621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4536323313994049622037747 6804484970991074433056621)
                  ·
                    refine ⟨2551681864121652912396233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6804484970991074433056621 2551681864121652912396233)
                    ·
                      refine ⟨1913761398091239684297175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2551681864121652912396233 1913761398091239684297175)
                      ·
                        rfl

theorem cell23_3727037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_3727037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727037 prefixEnd_3727037 := by exact prefixLift 3727037
  have htrace : WordTrace (prefixWord ++ tailWord_3727037) baseStart_3727037 baseEnd_3727037 := by
    simpa [prefixWord, tailWord_3727037, baseEnd_3727037] using wordTrace_append hprefix tailTrace_3727037
  have hstable : (prefixWord ++ tailWord_3727037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727037).length < 2 ^ (prefixWord ++ tailWord_3727037).sum := by decide
  have hdescent : baseEnd_3727037 < baseStart_3727037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727060 : List Nat := [2, 4, 1, 3, 1, 1, 1, 2, 2, 6]
def baseStart_3727060 : Nat := 118140960795 + 3727060 * 2 ^ 59
def prefixEnd_3727060 : Nat := 4983230072969 + 3 ^ 40 * 3727060 * 2
def baseEnd_3727060 : Nat := 637924402715431031436523

theorem tailTrace_3727060 : CollatzResearch.WordTrace tailWord_3727060 prefixEnd_3727060 637924402715431031436523 := by
  unfold tailWord_3727060
  simp only [CollatzResearch.WordTrace]
  refine ⟨67968522938752813008137317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90624697251670417344183089 67968522938752813008137317)
  ·
    refine ⟨12744098051016152439025747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67968522938752813008137317 12744098051016152439025747)
    ·
      refine ⟨19116147076524228658538621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12744098051016152439025747 19116147076524228658538621)
      ·
        refine ⟨7168555153696585746951983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19116147076524228658538621 7168555153696585746951983)
        ·
          refine ⟨10752832730544878620427975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7168555153696585746951983 10752832730544878620427975)
          ·
            refine ⟨16129249095817317930641963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10752832730544878620427975 16129249095817317930641963)
            ·
              refine ⟨24193873643725976895962945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16129249095817317930641963 24193873643725976895962945)
              ·
                refine ⟨18145405232794482671972209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24193873643725976895962945 18145405232794482671972209)
                ·
                  refine ⟨13609053924595862003979157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18145405232794482671972209 13609053924595862003979157)
                  ·
                    refine ⟨637924402715431031436523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13609053924595862003979157 637924402715431031436523)
                    ·
                      rfl

theorem cell23_3727060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_3727060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727060 prefixEnd_3727060 := by exact prefixLift 3727060
  have htrace : WordTrace (prefixWord ++ tailWord_3727060) baseStart_3727060 baseEnd_3727060 := by
    simpa [prefixWord, tailWord_3727060, baseEnd_3727060] using wordTrace_append hprefix tailTrace_3727060
  have hstable : (prefixWord ++ tailWord_3727060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727060).length < 2 ^ (prefixWord ++ tailWord_3727060).sum := by decide
  have hdescent : baseEnd_3727060 < baseStart_3727060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727063 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 4]
def baseStart_3727063 : Nat := 118140960795 + 3727063 * 2 ^ 59
def prefixEnd_3727063 : Nat := 4983230072969 + 3 ^ 40 * 3727063 * 2
def baseEnd_3727063 : Nat := 1913774748588256582572055

theorem tailTrace_3727063 : CollatzResearch.WordTrace tailWord_3727063 prefixEnd_3727063 1913774748588256582572055 := by
  unfold tailWord_3727063
  simp only [CollatzResearch.WordTrace]
  refine ⟨135937155296494757528633843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90624770197663171685755895 135937155296494757528633843)
  ·
    refine ⟨203905732944742136292950765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135937155296494757528633843 203905732944742136292950765)
    ·
      refine ⟨76464649854278301109856537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203905732944742136292950765 76464649854278301109856537)
      ·
        refine ⟨57348487390708725832392403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76464649854278301109856537 57348487390708725832392403)
        ·
          refine ⟨86022731086063088748588605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57348487390708725832392403 86022731086063088748588605)
          ·
            refine ⟨32258524157273658280720727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86022731086063088748588605 32258524157273658280720727)
            ·
              refine ⟨48387786235910487421081091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32258524157273658280720727 48387786235910487421081091)
              ·
                refine ⟨72581679353865731131621637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48387786235910487421081091 72581679353865731131621637)
                ·
                  refine ⟨13609064878849824587179057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72581679353865731131621637 13609064878849824587179057)
                  ·
                    refine ⟨10206798659137368440384293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13609064878849824587179057 10206798659137368440384293)
                    ·
                      refine ⟨1913774748588256582572055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10206798659137368440384293 1913774748588256582572055)
                      ·
                        rfl

theorem cell23_3727063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_3727063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727063 prefixEnd_3727063 := by exact prefixLift 3727063
  have htrace : WordTrace (prefixWord ++ tailWord_3727063) baseStart_3727063 baseEnd_3727063 := by
    simpa [prefixWord, tailWord_3727063, baseEnd_3727063] using wordTrace_append hprefix tailTrace_3727063
  have hstable : (prefixWord ++ tailWord_3727063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727063).length < 2 ^ (prefixWord ++ tailWord_3727063).sum := by decide
  have hdescent : baseEnd_3727063 < baseStart_3727063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727080 : List Nat := [2, 1, 4, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_3727080 : Nat := 118140960795 + 3727080 * 2 ^ 59
def prefixEnd_3727080 : Nat := 4983230072969 + 3 ^ 40 * 3727080 * 2
def baseEnd_3727080 : Nat := 1913783477759383016059477

theorem tailTrace_3727080 : CollatzResearch.WordTrace tailWord_3727080 prefixEnd_3727080 1913783477759383016059477 := by
  unfold tailWord_3727080
  simp only [CollatzResearch.WordTrace]
  refine ⟨67968887668716584716001347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90625183558288779621335129 67968887668716584716001347)
  ·
    refine ⟨101953331503074877074002021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67968887668716584716001347 101953331503074877074002021)
    ·
      refine ⟨19116249656826539451375379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101953331503074877074002021 19116249656826539451375379)
      ·
        refine ⟨28674374485239809177063069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19116249656826539451375379 28674374485239809177063069)
        ·
          refine ⟨10752890431964928441398651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28674374485239809177063069 10752890431964928441398651)
          ·
            refine ⟨16129335647947392662097977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10752890431964928441398651 16129335647947392662097977)
            ·
              refine ⟨12097001735960544496573483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16129335647947392662097977 12097001735960544496573483)
              ·
                refine ⟨18145502603940816744860225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12097001735960544496573483 18145502603940816744860225)
                ·
                  refine ⟨13609126952955612558645169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18145502603940816744860225 13609126952955612558645169)
                  ·
                    refine ⟨10206845214716709418983877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13609126952955612558645169 10206845214716709418983877)
                    ·
                      refine ⟨1913783477759383016059477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10206845214716709418983877 1913783477759383016059477)
                      ·
                        rfl

theorem cell23_3727080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_3727080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727080 prefixEnd_3727080 := by exact prefixLift 3727080
  have htrace : WordTrace (prefixWord ++ tailWord_3727080) baseStart_3727080 baseEnd_3727080 := by
    simpa [prefixWord, tailWord_3727080, baseEnd_3727080] using wordTrace_append hprefix tailTrace_3727080
  have hstable : (prefixWord ++ tailWord_3727080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727080).length < 2 ^ (prefixWord ++ tailWord_3727080).sum := by decide
  have hdescent : baseEnd_3727080 < baseStart_3727080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727103 : List Nat := [1, 1, 2, 2, 1, 3, 4, 1, 1, 7]
def baseStart_3727103 : Nat := 118140960795 + 3727103 * 2 ^ 59
def prefixEnd_3727103 : Nat := 4983230072969 + 3 ^ 40 * 3727103 * 2
def baseEnd_3727103 : Nat := 637931762604812142023957

theorem tailTrace_3727103 : CollatzResearch.WordTrace tailWord_3727103 prefixEnd_3727103 637931762604812142023957 := by
  unfold tailWord_3727103
  simp only [CollatzResearch.WordTrace]
  refine ⟨135938614216349844360089963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90625742810899896240059975 135938614216349844360089963)
  ·
    refine ⟨203907921324524766540134945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135938614216349844360089963 203907921324524766540134945)
    ·
      refine ⟨152930940993393574905101209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203907921324524766540134945 152930940993393574905101209)
      ·
        refine ⟨114698205745045181178825907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152930940993393574905101209 114698205745045181178825907)
        ·
          refine ⟨172047308617567771768238861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114698205745045181178825907 172047308617567771768238861)
          ·
            refine ⟨64517740731587914413089573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172047308617567771768238861 64517740731587914413089573)
            ·
              refine ⟨12097076387172733952454295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64517740731587914413089573 12097076387172733952454295)
              ·
                refine ⟨18145614580759100928681443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12097076387172733952454295 18145614580759100928681443)
                ·
                  refine ⟨27218421871138651393022165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18145614580759100928681443 27218421871138651393022165)
                  ·
                    refine ⟨637931762604812142023957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27218421871138651393022165 637931762604812142023957)
                    ·
                      rfl

theorem cell23_3727103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 7].length) (baseStart_3727103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727103 prefixEnd_3727103 := by exact prefixLift 3727103
  have htrace : WordTrace (prefixWord ++ tailWord_3727103) baseStart_3727103 baseEnd_3727103 := by
    simpa [prefixWord, tailWord_3727103, baseEnd_3727103] using wordTrace_append hprefix tailTrace_3727103
  have hstable : (prefixWord ++ tailWord_3727103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727103).length < 2 ^ (prefixWord ++ tailWord_3727103).sum := by decide
  have hdescent : baseEnd_3727103 < baseStart_3727103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727113 : List Nat := [1, 2, 1, 1, 3, 2, 1, 4, 1, 2, 5]
def baseStart_3727113 : Nat := 118140960795 + 3727113 * 2 ^ 59
def prefixEnd_3727113 : Nat := 4983230072969 + 3 ^ 40 * 3727113 * 2
def baseEnd_3727113 : Nat := 1913800422620981386946825

theorem tailTrace_3727113 : CollatzResearch.WordTrace tailWord_3727113 prefixEnd_3727113 1913800422620981386946825 := by
  unfold tailWord_3727113
  simp only [CollatzResearch.WordTrace]
  refine ⟨135938978946313616067953993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90625985964209077378635995 135938978946313616067953993)
  ·
    refine ⟨101954234209735212050965495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135938978946313616067953993 101954234209735212050965495)
    ·
      refine ⟨152931351314602818076448243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101954234209735212050965495 152931351314602818076448243)
      ·
        refine ⟨229397026971904227114672365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152931351314602818076448243 229397026971904227114672365)
        ·
          refine ⟨86023885114464085168002137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229397026971904227114672365 86023885114464085168002137)
          ·
            refine ⟨64517913835848063876001603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86023885114464085168002137 64517913835848063876001603)
            ·
              refine ⟨96776870753772095814002405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64517913835848063876001603 96776870753772095814002405)
              ·
                refine ⟨18145663266332267965125451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96776870753772095814002405 18145663266332267965125451)
                ·
                  refine ⟨27218494899498401947688177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18145663266332267965125451 27218494899498401947688177)
                  ·
                    refine ⟨20413871174623801460766133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27218494899498401947688177 20413871174623801460766133)
                    ·
                      refine ⟨1913800422620981386946825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20413871174623801460766133 1913800422620981386946825)
                      ·
                        rfl

theorem cell23_3727113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 2, 5].length) (baseStart_3727113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727113 prefixEnd_3727113 := by exact prefixLift 3727113
  have htrace : WordTrace (prefixWord ++ tailWord_3727113) baseStart_3727113 baseEnd_3727113 := by
    simpa [prefixWord, tailWord_3727113, baseEnd_3727113] using wordTrace_append hprefix tailTrace_3727113
  have hstable : (prefixWord ++ tailWord_3727113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727113).length < 2 ^ (prefixWord ++ tailWord_3727113).sum := by decide
  have hdescent : baseEnd_3727113 < baseStart_3727113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727123 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 4]
def baseStart_3727123 : Nat := 118140960795 + 3727123 * 2 ^ 59
def prefixEnd_3727123 : Nat := 4983230072969 + 3 ^ 40 * 3727123 * 2
def baseEnd_3727123 : Nat := 1913805557427526347821779

theorem tailTrace_3727123 : CollatzResearch.WordTrace tailWord_3727123 prefixEnd_3727123 1913805557427526347821779 := by
  unfold tailWord_3727123
  simp only [CollatzResearch.WordTrace]
  refine ⟨135939343676277387775818023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90626229117518258517212015 135939343676277387775818023)
  ·
    refine ⟨203909015514416081663727035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135939343676277387775818023 203909015514416081663727035)
    ·
      refine ⟨305863523271624122495590553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203909015514416081663727035 305863523271624122495590553)
      ·
        refine ⟨229397642453718091871692915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305863523271624122495590553 229397642453718091871692915)
        ·
          refine ⟨344096463680577137807539373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229397642453718091871692915 344096463680577137807539373)
          ·
            refine ⟨129036173880216426677827265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344096463680577137807539373 129036173880216426677827265)
            ·
              refine ⟨96777130410162320008370449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129036173880216426677827265 96777130410162320008370449)
              ·
                refine ⟨72582847807621740006277837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96777130410162320008370449 72582847807621740006277837)
                ·
                  refine ⟨27218567927858152502354189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72582847807621740006277837 27218567927858152502354189)
                  ·
                    refine ⟨10206962972946807188382821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27218567927858152502354189 10206962972946807188382821)
                    ·
                      refine ⟨1913805557427526347821779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10206962972946807188382821 1913805557427526347821779)
                      ·
                        rfl

theorem cell23_3727123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 4].length) (baseStart_3727123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727123 prefixEnd_3727123 := by exact prefixLift 3727123
  have htrace : WordTrace (prefixWord ++ tailWord_3727123) baseStart_3727123 baseEnd_3727123 := by
    simpa [prefixWord, tailWord_3727123, baseEnd_3727123] using wordTrace_append hprefix tailTrace_3727123
  have hstable : (prefixWord ++ tailWord_3727123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727123).length < 2 ^ (prefixWord ++ tailWord_3727123).sum := by decide
  have hdescent : baseEnd_3727123 < baseStart_3727123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727130 : List Nat := [3, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5]
def baseStart_3727130 : Nat := 118140960795 + 3727130 * 2 ^ 59
def prefixEnd_3727130 : Nat := 4983230072969 + 3 ^ 40 * 3727130 * 2
def baseEnd_3727130 : Nat := 1913809151792107820434247

theorem tailTrace_3727130 : CollatzResearch.WordTrace tailWord_3727130 prefixEnd_3727130 1913809151792107820434247 := by
  unfold tailWord_3727130
  simp only [CollatzResearch.WordTrace]
  refine ⟨33984899746813006992830711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90626399324834685314215229 33984899746813006992830711)
  ·
    refine ⟨50977349620219510489246067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33984899746813006992830711 50977349620219510489246067)
    ·
      refine ⟨76466024430329265733869101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50977349620219510489246067 76466024430329265733869101)
      ·
        refine ⟨28674759161373474650200913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76466024430329265733869101 28674759161373474650200913)
        ·
          refine ⟨21506069371030105987650685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28674759161373474650200913 21506069371030105987650685)
          ·
            refine ⟨8064776014136289745369007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21506069371030105987650685 8064776014136289745369007)
            ·
              refine ⟨12097164021204434618053511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8064776014136289745369007 12097164021204434618053511)
              ·
                refine ⟨18145746031806651927080267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12097164021204434618053511 18145746031806651927080267)
                ·
                  refine ⟨27218619047709977890620401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18145746031806651927080267 27218619047709977890620401)
                  ·
                    refine ⟨20413964285782483417965301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27218619047709977890620401 20413964285782483417965301)
                    ·
                      refine ⟨1913809151792107820434247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20413964285782483417965301 1913809151792107820434247)
                      ·
                        rfl

theorem cell23_3727130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_3727130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727130 prefixEnd_3727130 := by exact prefixLift 3727130
  have htrace : WordTrace (prefixWord ++ tailWord_3727130) baseStart_3727130 baseEnd_3727130 := by
    simpa [prefixWord, tailWord_3727130, baseEnd_3727130] using wordTrace_append hprefix tailTrace_3727130
  have hstable : (prefixWord ++ tailWord_3727130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727130).length < 2 ^ (prefixWord ++ tailWord_3727130).sum := by decide
  have hdescent : baseEnd_3727130 < baseStart_3727130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727217 : List Nat := [1, 2, 2, 2, 1, 3, 3, 1, 1, 5, 2]
def baseStart_3727217 : Nat := 118140960795 + 3727217 * 2 ^ 59
def prefixEnd_3727217 : Nat := 4983230072969 + 3 ^ 40 * 3727217 * 2
def baseEnd_3727217 : Nat := 1913853824609048980046347

theorem tailTrace_3727217 : CollatzResearch.WordTrace tailWord_3727217 prefixEnd_3727217 1913853824609048980046347 := by
  unfold tailWord_3727217
  simp only [CollatzResearch.WordTrace]
  refine ⟨135942772137936841829739905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90628514758624561219826603 135942772137936841829739905)
  ·
    refine ⟨101957079103452631372304929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135942772137936841829739905 101957079103452631372304929)
    ·
      refine ⟨76467809327589473529228697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101957079103452631372304929 76467809327589473529228697)
      ·
        refine ⟨57350856995692105146921523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76467809327589473529228697 57350856995692105146921523)
        ·
          refine ⟨86026285493538157720382285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57350856995692105146921523 86026285493538157720382285)
          ·
            refine ⟨32259857060076809145143357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86026285493538157720382285 32259857060076809145143357)
            ·
              refine ⟨12097446397528803429428759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32259857060076809145143357 12097446397528803429428759)
              ·
                refine ⟨18146169596293205144143139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12097446397528803429428759 18146169596293205144143139)
                ·
                  refine ⟨27219254394439807716214709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18146169596293205144143139 27219254394439807716214709)
                  ·
                    refine ⟨2551805099478731973395129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27219254394439807716214709 2551805099478731973395129)
                    ·
                      refine ⟨1913853824609048980046347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2551805099478731973395129 1913853824609048980046347)
                      ·
                        rfl

theorem cell23_3727217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 5, 2].length) (baseStart_3727217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727217 prefixEnd_3727217 := by exact prefixLift 3727217
  have htrace : WordTrace (prefixWord ++ tailWord_3727217) baseStart_3727217 baseEnd_3727217 := by
    simpa [prefixWord, tailWord_3727217, baseEnd_3727217] using wordTrace_append hprefix tailTrace_3727217
  have hstable : (prefixWord ++ tailWord_3727217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727217).length < 2 ^ (prefixWord ++ tailWord_3727217).sum := by decide
  have hdescent : baseEnd_3727217 < baseStart_3727217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727257 : List Nat := [1, 2, 1, 2, 1, 3, 2, 5, 2, 4]
def baseStart_3727257 : Nat := 118140960795 + 3727257 * 2 ^ 59
def prefixEnd_3727257 : Nat := 4983230072969 + 3 ^ 40 * 3727257 * 2
def baseEnd_3727257 : Nat := 637958121278409607848721

theorem tailTrace_3727257 : CollatzResearch.WordTrace tailWord_3727257 prefixEnd_3727257 637958121278409607848721 := by
  unfold tailWord_3727257
  simp only [CollatzResearch.WordTrace]
  refine ⟨135944231057791928661196025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90629487371861285774130683 135944231057791928661196025)
  ·
    refine ⟨101958173293343946495897019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135944231057791928661196025 101958173293343946495897019)
    ·
      refine ⟨152937259940015919743845529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101958173293343946495897019 152937259940015919743845529)
      ·
        refine ⟨114702944955011939807884147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152937259940015919743845529 114702944955011939807884147)
        ·
          refine ⟨172054417432517909711826221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114702944955011939807884147 172054417432517909711826221)
          ·
            refine ⟨64520406537194216141934833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172054417432517909711826221 64520406537194216141934833)
            ·
              refine ⟨48390304902895662106451125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64520406537194216141934833 48390304902895662106451125)
              ·
                refine ⟨4536591084646468322479793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48390304902895662106451125 4536591084646468322479793)
                ·
                  refine ⟨3402443313484851241859845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4536591084646468322479793 3402443313484851241859845)
                  ·
                    refine ⟨637958121278409607848721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3402443313484851241859845 637958121278409607848721)
                    ·
                      rfl

theorem cell23_3727257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2, 4].length) (baseStart_3727257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727257 prefixEnd_3727257 := by exact prefixLift 3727257
  have htrace : WordTrace (prefixWord ++ tailWord_3727257) baseStart_3727257 baseEnd_3727257 := by
    simpa [prefixWord, tailWord_3727257, baseEnd_3727257] using wordTrace_append hprefix tailTrace_3727257
  have hstable : (prefixWord ++ tailWord_3727257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727257).length < 2 ^ (prefixWord ++ tailWord_3727257).sum := by decide
  have hdescent : baseEnd_3727257 < baseStart_3727257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727357 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 2, 4, 3]
def baseStart_3727357 : Nat := 118140960795 + 3727357 * 2 ^ 59
def prefixEnd_3727357 : Nat := 4983230072969 + 3 ^ 40 * 3727357 * 2
def baseEnd_3727357 : Nat := 1913925711900678432295703

theorem tailTrace_3727357 : CollatzResearch.WordTrace tailWord_3727357 prefixEnd_3727357 1913925711900678432295703 := by
  unfold tailWord_3727357
  simp only [CollatzResearch.WordTrace]
  refine ⟨135947878357429645739836325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90631918904953097159890883 135947878357429645739836325)
  ·
    refine ⟨25490227192018058576219311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135947878357429645739836325 25490227192018058576219311)
    ·
      refine ⟨38235340788027087864328967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25490227192018058576219311 38235340788027087864328967)
      ·
        refine ⟨57353011182040631796493451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38235340788027087864328967 57353011182040631796493451)
        ·
          refine ⟨86029516773060947694740177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57353011182040631796493451 86029516773060947694740177)
          ·
            refine ⟨64522137579795710771055133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86029516773060947694740177 64522137579795710771055133)
            ·
              refine ⟨24195801592423391539145675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64522137579795710771055133 24195801592423391539145675)
              ·
                refine ⟨36293702388635087308718513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24195801592423391539145675 36293702388635087308718513)
                ·
                  refine ⟨27220276791476315481538885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36293702388635087308718513 27220276791476315481538885)
                  ·
                    refine ⟨5103801898401809152788541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27220276791476315481538885 5103801898401809152788541)
                    ·
                      refine ⟨1913925711900678432295703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5103801898401809152788541 1913925711900678432295703)
                      ·
                        rfl

theorem cell23_3727357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_3727357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727357 prefixEnd_3727357 := by exact prefixLift 3727357
  have htrace : WordTrace (prefixWord ++ tailWord_3727357) baseStart_3727357 baseEnd_3727357 := by
    simpa [prefixWord, tailWord_3727357, baseEnd_3727357] using wordTrace_append hprefix tailTrace_3727357
  have hstable : (prefixWord ++ tailWord_3727357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727357).length < 2 ^ (prefixWord ++ tailWord_3727357).sum := by decide
  have hdescent : baseEnd_3727357 < baseStart_3727357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727367 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 4]
def baseStart_3727367 : Nat := 118140960795 + 3727367 * 2 ^ 59
def prefixEnd_3727367 : Nat := 4983230072969 + 3 ^ 40 * 3727367 * 2
def baseEnd_3727367 : Nat := 1913930846707223393170657

theorem tailTrace_3727367 : CollatzResearch.WordTrace tailWord_3727367 prefixEnd_3727367 1913930846707223393170657 := by
  unfold tailWord_3727367
  simp only [CollatzResearch.WordTrace]
  refine ⟨135948243087393417447700355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90632162058262278298466903 135948243087393417447700355)
  ·
    refine ⟨203922364631090126171550533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135948243087393417447700355 203922364631090126171550533)
    ·
      refine ⟨38235443368329398657165725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203922364631090126171550533 38235443368329398657165725)
      ·
        refine ⟨14338291263123524496437147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38235443368329398657165725 14338291263123524496437147)
        ·
          refine ⟨21507436894685286744655721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14338291263123524496437147 21507436894685286744655721)
          ·
            refine ⟨16130577671013965058491791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21507436894685286744655721 16130577671013965058491791)
            ·
              refine ⟨24195866506520947587737687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16130577671013965058491791 24195866506520947587737687)
              ·
                refine ⟨36293799759781421381606531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24195866506520947587737687 36293799759781421381606531)
                ·
                  refine ⟨54440699639672132072409797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36293799759781421381606531 54440699639672132072409797)
                  ·
                    refine ⟨10207631182438524763576837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54440699639672132072409797 10207631182438524763576837)
                    ·
                      refine ⟨1913930846707223393170657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10207631182438524763576837 1913930846707223393170657)
                      ·
                        rfl

theorem cell23_3727367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_3727367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727367 prefixEnd_3727367 := by exact prefixLift 3727367
  have htrace : WordTrace (prefixWord ++ tailWord_3727367) baseStart_3727367 baseEnd_3727367 := by
    simpa [prefixWord, tailWord_3727367, baseEnd_3727367] using wordTrace_append hprefix tailTrace_3727367
  have hstable : (prefixWord ++ tailWord_3727367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727367).length < 2 ^ (prefixWord ++ tailWord_3727367).sum := by decide
  have hdescent : baseEnd_3727367 < baseStart_3727367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727371 : List Nat := [1, 1, 1, 1, 6, 1, 1, 5, 2, 2, 2]
def baseStart_3727371 : Nat := 118140960795 + 3727371 * 2 ^ 59
def prefixEnd_3727371 : Nat := 4983230072969 + 3 ^ 40 * 3727371 * 2
def baseEnd_3727371 : Nat := 1913932900629841377520639

theorem tailTrace_3727371 : CollatzResearch.WordTrace tailWord_3727371 prefixEnd_3727371 1913932900629841377520639 := by
  unfold tailWord_3727371
  simp only [CollatzResearch.WordTrace]
  refine ⟨135948388979378926130845967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90632259319585950753897311 135948388979378926130845967)
  ·
    refine ⟨203922583469068389196268951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135948388979378926130845967 203922583469068389196268951)
    ·
      refine ⟨305883875203602583794403427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203922583469068389196268951 305883875203602583794403427)
      ·
        refine ⟨458825812805403875691605141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305883875203602583794403427 458825812805403875691605141)
        ·
          refine ⟨21507459975253306673043991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 458825812805403875691605141 21507459975253306673043991)
          ·
            refine ⟨32261189962879960009565987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21507459975253306673043991 32261189962879960009565987)
            ·
              refine ⟨48391784944319940014348981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32261189962879960009565987 48391784944319940014348981)
              ·
                refine ⟨4536729838529994376345217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48391784944319940014348981 4536729838529994376345217)
                ·
                  refine ⟨3402547378897495782258913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4536729838529994376345217 3402547378897495782258913)
                  ·
                    refine ⟨2551910534173121836694185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3402547378897495782258913 2551910534173121836694185)
                    ·
                      refine ⟨1913932900629841377520639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2551910534173121836694185 1913932900629841377520639)
                      ·
                        rfl

theorem cell23_3727371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2, 2, 2].length) (baseStart_3727371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727371 prefixEnd_3727371 := by exact prefixLift 3727371
  have htrace : WordTrace (prefixWord ++ tailWord_3727371) baseStart_3727371 baseEnd_3727371 := by
    simpa [prefixWord, tailWord_3727371, baseEnd_3727371] using wordTrace_append hprefix tailTrace_3727371
  have hstable : (prefixWord ++ tailWord_3727371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727371).length < 2 ^ (prefixWord ++ tailWord_3727371).sum := by decide
  have hdescent : baseEnd_3727371 < baseStart_3727371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727422 : List Nat := [4, 2, 1, 3, 2, 1, 3, 1, 2, 2, 2]
def baseStart_3727422 : Nat := 118140960795 + 3727422 * 2 ^ 59
def prefixEnd_3727422 : Nat := 4983230072969 + 3 ^ 40 * 3727422 * 2
def baseEnd_3727422 : Nat := 1913959088143220677982905

theorem tailTrace_3727422 : CollatzResearch.WordTrace tailWord_3727422 prefixEnd_3727422 1913959088143220677982905 := by
  unfold tailWord_3727422
  simp only [CollatzResearch.WordTrace]
  refine ⟨16993781137774270230119065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90633499401462774560635013 16993781137774270230119065)
  ·
    refine ⟨12745335853330702672589299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16993781137774270230119065 12745335853330702672589299)
    ·
      refine ⟨19118003779996054008883949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12745335853330702672589299 19118003779996054008883949)
      ·
        refine ⟨7169251417498520253331481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19118003779996054008883949 7169251417498520253331481)
        ·
          refine ⟨5376938563123890189998611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7169251417498520253331481 5376938563123890189998611)
          ·
            refine ⟨8065407844685835284997917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5376938563123890189998611 8065407844685835284997917)
            ·
              refine ⟨3024527941757188231874219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8065407844685835284997917 3024527941757188231874219)
              ·
                refine ⟨4536791912635782347811329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3024527941757188231874219 4536791912635782347811329)
                ·
                  refine ⟨3402593934476836760858497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4536791912635782347811329 3402593934476836760858497)
                  ·
                    refine ⟨2551945450857627570643873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3402593934476836760858497 2551945450857627570643873)
                    ·
                      refine ⟨1913959088143220677982905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2551945450857627570643873 1913959088143220677982905)
                      ·
                        rfl

theorem cell23_3727422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_3727422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727422 prefixEnd_3727422 := by exact prefixLift 3727422
  have htrace : WordTrace (prefixWord ++ tailWord_3727422) baseStart_3727422 baseEnd_3727422 := by
    simpa [prefixWord, tailWord_3727422, baseEnd_3727422] using wordTrace_append hprefix tailTrace_3727422
  have hstable : (prefixWord ++ tailWord_3727422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727422).length < 2 ^ (prefixWord ++ tailWord_3727422).sum := by decide
  have hdescent : baseEnd_3727422 < baseStart_3727422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727427 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 4]
def baseStart_3727427 : Nat := 118140960795 + 3727427 * 2 ^ 59
def prefixEnd_3727427 : Nat := 4983230072969 + 3 ^ 40 * 3727427 * 2
def baseEnd_3727427 : Nat := 1913961655546493158420381

theorem tailTrace_3727427 : CollatzResearch.WordTrace tailWord_3727427 prefixEnd_3727427 1913961655546493158420381 := by
  unfold tailWord_3727427
  simp only [CollatzResearch.WordTrace]
  refine ⟨135950431467176047694884535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90633620978117365129923023 135950431467176047694884535)
  ·
    refine ⟨203925647200764071542326803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135950431467176047694884535 203925647200764071542326803)
    ·
      refine ⟨305888470801146107313490205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203925647200764071542326803 305888470801146107313490205)
      ·
        refine ⟨114708176550429790242558827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305888470801146107313490205 114708176550429790242558827)
        ·
          refine ⟨172062264825644685363838241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114708176550429790242558827 172062264825644685363838241)
          ·
            refine ⟨129046698619233514022878681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172062264825644685363838241 129046698619233514022878681)
            ·
              refine ⟨96785023964425135517159011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129046698619233514022878681 96785023964425135517159011)
              ·
                refine ⟨145177535946637703275738517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96785023964425135517159011 145177535946637703275738517)
                ·
                  refine ⟨6805196997498642341050243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 145177535946637703275738517 6805196997498642341050243)
                  ·
                    refine ⟨10207795496247963511575365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6805196997498642341050243 10207795496247963511575365)
                    ·
                      refine ⟨1913961655546493158420381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10207795496247963511575365 1913961655546493158420381)
                      ·
                        rfl

theorem cell23_3727427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_3727427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727427 prefixEnd_3727427 := by exact prefixLift 3727427
  have htrace : WordTrace (prefixWord ++ tailWord_3727427) baseStart_3727427 baseEnd_3727427 := by
    simpa [prefixWord, tailWord_3727427, baseEnd_3727427] using wordTrace_append hprefix tailTrace_3727427
  have hstable : (prefixWord ++ tailWord_3727427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727427).length < 2 ^ (prefixWord ++ tailWord_3727427).sum := by decide
  have hdescent : baseEnd_3727427 < baseStart_3727427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727444 : List Nat := [2, 4, 1, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_3727444 : Nat := 118140960795 + 3727444 * 2 ^ 59
def prefixEnd_3727444 : Nat := 4983230072969 + 3 ^ 40 * 3727444 * 2
def baseEnd_3727444 : Nat := 1913970384717619591907803

theorem tailTrace_3727444 : CollatzResearch.WordTrace tailWord_3727444 prefixEnd_3727444 1913970384717619591907803 := by
  unfold tailWord_3727444
  simp only [CollatzResearch.WordTrace]
  refine ⟨67975525754057229799126693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90634034338742973065502257 67975525754057229799126693)
  ·
    refine ⟨12745411078885730587336255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67975525754057229799126693 12745411078885730587336255)
    ·
      refine ⟨19118116618328595881004383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12745411078885730587336255 19118116618328595881004383)
      ·
        refine ⟨28677174927492893821506575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19118116618328595881004383 28677174927492893821506575)
        ·
          refine ⟨43015762391239340732259863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28677174927492893821506575 43015762391239340732259863)
          ·
            refine ⟨64523643586859011098389795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43015762391239340732259863 64523643586859011098389795)
            ·
              refine ⟨96785465380288516647584693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64523643586859011098389795 96785465380288516647584693)
              ·
                refine ⟨9073637379402048435711065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96785465380288516647584693 9073637379402048435711065)
                ·
                  refine ⟨6805228034551536326783299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9073637379402048435711065 6805228034551536326783299)
                  ·
                    refine ⟨10207842051827304490174949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6805228034551536326783299 10207842051827304490174949)
                    ·
                      refine ⟨1913970384717619591907803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10207842051827304490174949 1913970384717619591907803)
                      ·
                        rfl

theorem cell23_3727444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_3727444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727444 prefixEnd_3727444 := by exact prefixLift 3727444
  have htrace : WordTrace (prefixWord ++ tailWord_3727444) baseStart_3727444 baseEnd_3727444 := by
    simpa [prefixWord, tailWord_3727444, baseEnd_3727444] using wordTrace_append hprefix tailTrace_3727444
  have hstable : (prefixWord ++ tailWord_3727444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727444).length < 2 ^ (prefixWord ++ tailWord_3727444).sum := by decide
  have hdescent : baseEnd_3727444 < baseStart_3727444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727471 : List Nat := [1, 1, 2, 1, 3, 6, 1, 1, 3, 4]
def baseStart_3727471 : Nat := 118140960795 + 3727471 * 2 ^ 59
def prefixEnd_3727471 : Nat := 4983230072969 + 3 ^ 40 * 3727471 * 2
def baseEnd_3727471 : Nat := 637994749565096995423393

theorem tailTrace_3727471 : CollatzResearch.WordTrace tailWord_3727471 prefixEnd_3727471 637994749565096995423393 := by
  unfold tailWord_3727471
  simp only [CollatzResearch.WordTrace]
  refine ⟨135952036279016643209486267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90634690852677762139657511 135952036279016643209486267)
  ·
    refine ⟨203928054418524964814229401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135952036279016643209486267 203928054418524964814229401)
    ·
      refine ⟨152946040813893723610672051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203928054418524964814229401 152946040813893723610672051)
      ·
        refine ⟨229419061220840585416008077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152946040813893723610672051 229419061220840585416008077)
        ·
          refine ⟨86032147957815219531003029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229419061220840585416008077 86032147957815219531003029)
          ·
            refine ⟨4032756935522588415515767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 86032147957815219531003029 4032756935522588415515767)
            ·
              refine ⟨6049135403283882623273651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4032756935522588415515767 6049135403283882623273651)
              ·
                refine ⟨9073703104925823934910477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6049135403283882623273651 9073703104925823934910477)
                ·
                  refine ⟨3402638664347183975591429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9073703104925823934910477 3402638664347183975591429)
                  ·
                    refine ⟨637994749565096995423393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3402638664347183975591429 637994749565096995423393)
                    ·
                      rfl

theorem cell23_3727471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3, 4].length) (baseStart_3727471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727471 prefixEnd_3727471 := by exact prefixLift 3727471
  have htrace : WordTrace (prefixWord ++ tailWord_3727471) baseStart_3727471 baseEnd_3727471 := by
    simpa [prefixWord, tailWord_3727471, baseEnd_3727471] using wordTrace_append hprefix tailTrace_3727471
  have hstable : (prefixWord ++ tailWord_3727471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727471).length < 2 ^ (prefixWord ++ tailWord_3727471).sum := by decide
  have hdescent : baseEnd_3727471 < baseStart_3727471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727484 : List Nat := [2, 2, 2, 1, 1, 5, 1, 3, 6]
def baseStart_3727484 : Nat := 118140960795 + 3727484 * 2 ^ 59
def prefixEnd_3727484 : Nat := 4983230072969 + 3 ^ 40 * 3727484 * 2
def baseEnd_3727484 : Nat := 212665658215977715045291

theorem tailTrace_3727484 : CollatzResearch.WordTrace tailWord_3727484 prefixEnd_3727484 212665658215977715045291 := by
  unfold tailWord_3727484
  simp only [CollatzResearch.WordTrace]
  refine ⟨67976255213984773214854753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90635006951979697619806337 67976255213984773214854753)
  ·
    refine ⟨50982191410488579911141065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67976255213984773214854753 50982191410488579911141065)
    ·
      refine ⟨38236643557866434933355799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50982191410488579911141065 38236643557866434933355799)
      ·
        refine ⟨57354965336799652400033699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38236643557866434933355799 57354965336799652400033699)
        ·
          refine ⟨86032448005199478600050549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57354965336799652400033699 86032448005199478600050549)
          ·
            refine ⟨8065542000487451118754739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86032448005199478600050549 8065542000487451118754739)
            ·
              refine ⟨12098313000731176678132109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8065542000487451118754739 12098313000731176678132109)
              ·
                refine ⟨4536867375274191254299541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12098313000731176678132109 4536867375274191254299541)
                ·
                  refine ⟨212665658215977715045291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4536867375274191254299541 212665658215977715045291)
                  ·
                    rfl

theorem cell23_3727484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 6].length) (baseStart_3727484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727484 prefixEnd_3727484 := by exact prefixLift 3727484
  have htrace : WordTrace (prefixWord ++ tailWord_3727484) baseStart_3727484 baseEnd_3727484 := by
    simpa [prefixWord, tailWord_3727484, baseEnd_3727484] using wordTrace_append hprefix tailTrace_3727484
  have hstable : (prefixWord ++ tailWord_3727484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727484).length < 2 ^ (prefixWord ++ tailWord_3727484).sum := by decide
  have hdescent : baseEnd_3727484 < baseStart_3727484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727518 : List Nat := [4, 3, 1, 1, 3, 1, 2, 2, 6]
def baseStart_3727518 : Nat := 118140960795 + 3727518 * 2 ^ 59
def prefixEnd_3727518 : Nat := 4983230072969 + 3 ^ 40 * 3727518 * 2
def baseEnd_3727518 : Nat := 212667598031783589153607

theorem tailTrace_3727518 : CollatzResearch.WordTrace tailWord_3727518 prefixEnd_3727518 212667598031783589153607 := by
  unfold tailWord_3727518
  simp only [CollatzResearch.WordTrace]
  refine ⟨16994218813730796279555901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90635833673230913490964805 16994218813730796279555901)
  ·
    refine ⟨6372832055149048604833463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16994218813730796279555901 6372832055149048604833463)
    ·
      refine ⟨9559248082723572907250195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6372832055149048604833463 9559248082723572907250195)
      ·
        refine ⟨14338872124085359360875293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9559248082723572907250195 14338872124085359360875293)
        ·
          refine ⟨5377077046532009760328235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14338872124085359360875293 5377077046532009760328235)
          ·
            refine ⟨8065615569798014640492353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5377077046532009760328235 8065615569798014640492353)
            ·
              refine ⟨6049211677348510980369265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8065615569798014640492353 6049211677348510980369265)
              ·
                refine ⟨4536908758011383235276949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6049211677348510980369265 4536908758011383235276949)
                ·
                  refine ⟨212667598031783589153607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4536908758011383235276949 212667598031783589153607)
                  ·
                    rfl

theorem cell23_3727518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_3727518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727518 prefixEnd_3727518 := by exact prefixLift 3727518
  have htrace : WordTrace (prefixWord ++ tailWord_3727518) baseStart_3727518 baseEnd_3727518 := by
    simpa [prefixWord, tailWord_3727518, baseEnd_3727518] using wordTrace_append hprefix tailTrace_3727518
  have hstable : (prefixWord ++ tailWord_3727518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727518).length < 2 ^ (prefixWord ++ tailWord_3727518).sum := by decide
  have hdescent : baseEnd_3727518 < baseStart_3727518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727522 : List Nat := [3, 3, 1, 3, 1, 3, 2, 2, 1, 4]
def baseStart_3727522 : Nat := 118140960795 + 3727522 * 2 ^ 59
def prefixEnd_3727522 : Nat := 4983230072969 + 3 ^ 40 * 3727522 * 2
def baseEnd_3727522 : Nat := 638003478736223428910815

theorem tailTrace_3727522 : CollatzResearch.WordTrace tailWord_3727522 prefixEnd_3727522 638003478736223428910815 := by
  unfold tailWord_3727522
  simp only [CollatzResearch.WordTrace]
  refine ⟨33988474100457969729898205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90635930934554585946395213 33988474100457969729898205)
  ·
    refine ⟨12745677787671738648711827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33988474100457969729898205 12745677787671738648711827)
    ·
      refine ⟨19118516681507607973067741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12745677787671738648711827 19118516681507607973067741)
      ·
        refine ⟨7169443755565352989900403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19118516681507607973067741 7169443755565352989900403)
        ·
          refine ⟨10754165633348029484850605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7169443755565352989900403 10754165633348029484850605)
          ·
            refine ⟨4032812112505511056818977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10754165633348029484850605 4032812112505511056818977)
            ·
              refine ⟨3024609084379133292614233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4032812112505511056818977 3024609084379133292614233)
              ·
                refine ⟨2268456813284349969460675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3024609084379133292614233 2268456813284349969460675)
                ·
                  refine ⟨3402685219926524954191013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2268456813284349969460675 3402685219926524954191013)
                  ·
                    refine ⟨638003478736223428910815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3402685219926524954191013 638003478736223428910815)
                    ·
                      rfl

theorem cell23_3727522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_3727522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727522 prefixEnd_3727522 := by exact prefixLift 3727522
  have htrace : WordTrace (prefixWord ++ tailWord_3727522) baseStart_3727522 baseEnd_3727522 := by
    simpa [prefixWord, tailWord_3727522, baseEnd_3727522] using wordTrace_append hprefix tailTrace_3727522
  have hstable : (prefixWord ++ tailWord_3727522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727522).length < 2 ^ (prefixWord ++ tailWord_3727522).sum := by decide
  have hdescent : baseEnd_3727522 < baseStart_3727522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727544 : List Nat := [2, 1, 2, 1, 2, 1, 6, 1, 1, 6]
def baseStart_3727544 : Nat := 118140960795 + 3727544 * 2 ^ 59
def prefixEnd_3727544 : Nat := 4983230072969 + 3 ^ 40 * 3727544 * 2
def baseEnd_3727544 : Nat := 638007244261023066885781

theorem tailTrace_3727544 : CollatzResearch.WordTrace tailWord_3727544 prefixEnd_3727544 638007244261023066885781 := by
  unfold tailWord_3727544
  simp only [CollatzResearch.WordTrace]
  refine ⟨67977349403876088338446843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90636465871834784451262457 67977349403876088338446843)
  ·
    refine ⟨101966024105814132507670265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67977349403876088338446843 101966024105814132507670265)
    ·
      refine ⟨76474518079360599380752699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101966024105814132507670265 76474518079360599380752699)
      ·
        refine ⟨114711777119040899071129049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76474518079360599380752699 114711777119040899071129049)
        ·
          refine ⟨86033832839280674303346787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114711777119040899071129049 86033832839280674303346787)
          ·
            refine ⟨129050749258921011455020181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86033832839280674303346787 129050749258921011455020181)
            ·
              refine ⟨6049253871511922411954071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129050749258921011455020181 6049253871511922411954071)
              ·
                refine ⟨9073880807267883617931107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6049253871511922411954071 9073880807267883617931107)
                ·
                  refine ⟨13610821210901825426896661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9073880807267883617931107 13610821210901825426896661)
                  ·
                    refine ⟨638007244261023066885781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13610821210901825426896661 638007244261023066885781)
                    ·
                      rfl

theorem cell23_3727544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 1, 6].length) (baseStart_3727544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727544 prefixEnd_3727544 := by exact prefixLift 3727544
  have htrace : WordTrace (prefixWord ++ tailWord_3727544) baseStart_3727544 baseEnd_3727544 := by
    simpa [prefixWord, tailWord_3727544, baseEnd_3727544] using wordTrace_append hprefix tailTrace_3727544
  have hstable : (prefixWord ++ tailWord_3727544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727544).length < 2 ^ (prefixWord ++ tailWord_3727544).sum := by decide
  have hdescent : baseEnd_3727544 < baseStart_3727544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727557 : List Nat := [1, 3, 1, 1, 1, 1, 4, 11]
def baseStart_3727557 : Nat := 118140960795 + 3727557 * 2 ^ 59
def prefixEnd_3727557 : Nat := 4983230072969 + 3 ^ 40 * 3727557 * 2
def baseEnd_3727557 : Nat := 70889941038206579622029

theorem tailTrace_3727557 : CollatzResearch.WordTrace tailWord_3727557 prefixEnd_3727557 70889941038206579622029 := by
  unfold tailWord_3727557
  simp only [CollatzResearch.WordTrace]
  refine ⟨135955172956705079897116925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90636781971136719931411283 135955172956705079897116925)
  ·
    refine ⟨50983189858764404961418847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135955172956705079897116925 50983189858764404961418847)
    ·
      refine ⟨76474784788146607442128271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50983189858764404961418847 76474784788146607442128271)
      ·
        refine ⟨114712177182219911163192407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76474784788146607442128271 114712177182219911163192407)
        ·
          refine ⟨172068265773329866744788611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114712177182219911163192407 172068265773329866744788611)
          ·
            refine ⟨258102398659994800117182917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172068265773329866744788611 258102398659994800117182917)
            ·
              refine ⟨48394199748749025021971797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 258102398659994800117182917 48394199748749025021971797)
              ·
                refine ⟨70889941038206579622029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 48394199748749025021971797 70889941038206579622029)
                ·
                  rfl

theorem cell23_3727557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 11].length) (baseStart_3727557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727557 prefixEnd_3727557 := by exact prefixLift 3727557
  have htrace : WordTrace (prefixWord ++ tailWord_3727557) baseStart_3727557 baseEnd_3727557 := by
    simpa [prefixWord, tailWord_3727557, baseEnd_3727557] using wordTrace_append hprefix tailTrace_3727557
  have hstable : (prefixWord ++ tailWord_3727557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727557).length < 2 ^ (prefixWord ++ tailWord_3727557).sum := by decide
  have hdescent : baseEnd_3727557 < baseStart_3727557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727585 : List Nat := [1, 2, 3, 1, 3, 1, 1, 6, 1, 2, 2]
def baseStart_3727585 : Nat := 118140960795 + 3727585 * 2 ^ 59
def prefixEnd_3727585 : Nat := 4983230072969 + 3 ^ 40 * 3727585 * 2
def baseEnd_3727585 : Nat := 1914042785489903540244655

theorem tailTrace_3727585 : CollatzResearch.WordTrace tailWord_3727585 prefixEnd_3727585 1914042785489903540244655 := by
  unfold tailWord_3727585
  simp only [CollatzResearch.WordTrace]
  refine ⟨135956194200603640679136209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90637462800402427119424139 135956194200603640679136209)
  ·
    refine ⟨101967145650452730509352157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135956194200603640679136209 101967145650452730509352157)
    ·
      refine ⟨38237679618919773941007059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101967145650452730509352157 38237679618919773941007059)
      ·
        refine ⟨57356519428379660911510589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38237679618919773941007059 57356519428379660911510589)
        ·
          refine ⟨21508694785642372841816471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57356519428379660911510589 21508694785642372841816471)
          ·
            refine ⟨32263042178463559262724707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21508694785642372841816471 32263042178463559262724707)
            ·
              refine ⟨48394563267695338894087061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32263042178463559262724707 48394563267695338894087061)
              ·
                refine ⟨2268495153173219010660331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48394563267695338894087061 2268495153173219010660331)
                ·
                  refine ⟨3402742729759828515990497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2268495153173219010660331 3402742729759828515990497)
                  ·
                    refine ⟨2552057047319871386992873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3402742729759828515990497 2552057047319871386992873)
                    ·
                      refine ⟨1914042785489903540244655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2552057047319871386992873 1914042785489903540244655)
                      ·
                        rfl

theorem cell23_3727585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6, 1, 2, 2].length) (baseStart_3727585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727585 prefixEnd_3727585 := by exact prefixLift 3727585
  have htrace : WordTrace (prefixWord ++ tailWord_3727585) baseStart_3727585 baseEnd_3727585 := by
    simpa [prefixWord, tailWord_3727585, baseEnd_3727585] using wordTrace_append hprefix tailTrace_3727585
  have hstable : (prefixWord ++ tailWord_3727585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727585).length < 2 ^ (prefixWord ++ tailWord_3727585).sum := by decide
  have hdescent : baseEnd_3727585 < baseStart_3727585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727601 : List Nat := [1, 2, 2, 2, 2, 1, 5, 1, 1, 3, 3]
def baseStart_3727601 : Nat := 118140960795 + 3727601 * 2 ^ 59
def prefixEnd_3727601 : Nat := 4983230072969 + 3 ^ 40 * 3727601 * 2
def baseEnd_3727601 : Nat := 1914051001180375477644581

theorem tailTrace_3727601 : CollatzResearch.WordTrace tailWord_3727601 prefixEnd_3727601 1914051001180375477644581 := by
  unfold tailWord_3727601
  simp only [CollatzResearch.WordTrace]
  refine ⟨135956777768545675411718657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90637851845697116941145771 135956777768545675411718657)
  ·
    refine ⟨101967583326409256558788993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135956777768545675411718657 101967583326409256558788993)
    ·
      refine ⟨76475687494806942419091745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101967583326409256558788993 76475687494806942419091745)
      ·
        refine ⟨57356765621105206814318809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76475687494806942419091745 57356765621105206814318809)
        ·
          refine ⟨43017574215828905110739107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57356765621105206814318809 43017574215828905110739107)
          ·
            refine ⟨64526361323743357666108661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43017574215828905110739107 64526361323743357666108661)
            ·
              refine ⟨6049346374100939781197687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64526361323743357666108661 6049346374100939781197687)
              ·
                refine ⟨9074019561151409671796531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6049346374100939781197687 9074019561151409671796531)
                ·
                  refine ⟨13611029341727114507694797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9074019561151409671796531 13611029341727114507694797)
                  ·
                    refine ⟨5104136003147667940385549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13611029341727114507694797 5104136003147667940385549)
                    ·
                      refine ⟨1914051001180375477644581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5104136003147667940385549 1914051001180375477644581)
                      ·
                        rfl

theorem cell23_3727601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_3727601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727601 prefixEnd_3727601 := by exact prefixLift 3727601
  have htrace : WordTrace (prefixWord ++ tailWord_3727601) baseStart_3727601 baseEnd_3727601 := by
    simpa [prefixWord, tailWord_3727601, baseEnd_3727601] using wordTrace_append hprefix tailTrace_3727601
  have hstable : (prefixWord ++ tailWord_3727601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727601).length < 2 ^ (prefixWord ++ tailWord_3727601).sum := by decide
  have hdescent : baseEnd_3727601 < baseStart_3727601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727628 : List Nat := [2, 2, 1, 2, 2, 2, 1, 5, 1, 3, 2]
def baseStart_3727628 : Nat := 118140960795 + 3727628 * 2 ^ 59
def prefixEnd_3727628 : Nat := 4983230072969 + 3 ^ 40 * 3727628 * 2
def baseEnd_3727628 : Nat := 1914064865158046872006957

theorem tailTrace_3727628 : CollatzResearch.WordTrace tailWord_3727628 prefixEnd_3727628 1914064865158046872006957 := by
  unfold tailWord_3727628
  simp only [CollatzResearch.WordTrace]
  refine ⟨67978881269723929511475769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90638508359631906015301025 67978881269723929511475769)
  ·
    refine ⟨50984160952292947133606827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67978881269723929511475769 50984160952292947133606827)
    ·
      refine ⟨76476241428439420700410241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50984160952292947133606827 76476241428439420700410241)
      ·
        refine ⟨57357181071329565525307681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76476241428439420700410241 57357181071329565525307681)
        ·
          refine ⟨43017885803497174143980761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57357181071329565525307681 43017885803497174143980761)
          ·
            refine ⟨32263414352622880607985571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43017885803497174143980761 32263414352622880607985571)
            ·
              refine ⟨48395121528934320911978357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32263414352622880607985571 48395121528934320911978357)
              ·
                refine ⟨4537042643337592585497971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48395121528934320911978357 4537042643337592585497971)
                ·
                  refine ⟨6805563965006388878246957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4537042643337592585497971 6805563965006388878246957)
                  ·
                    refine ⟨2552086486877395829342609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6805563965006388878246957 2552086486877395829342609)
                    ·
                      refine ⟨1914064865158046872006957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2552086486877395829342609 1914064865158046872006957)
                      ·
                        rfl

theorem cell23_3727628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 1, 3, 2].length) (baseStart_3727628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727628 prefixEnd_3727628 := by exact prefixLift 3727628
  have htrace : WordTrace (prefixWord ++ tailWord_3727628) baseStart_3727628 baseEnd_3727628 := by
    simpa [prefixWord, tailWord_3727628, baseEnd_3727628] using wordTrace_append hprefix tailTrace_3727628
  have hstable : (prefixWord ++ tailWord_3727628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727628).length < 2 ^ (prefixWord ++ tailWord_3727628).sum := by decide
  have hdescent : baseEnd_3727628 < baseStart_3727628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727644 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_3727644 : Nat := 118140960795 + 3727644 * 2 ^ 59
def prefixEnd_3727644 : Nat := 4983230072969 + 3 ^ 40 * 3727644 * 2
def baseEnd_3727644 : Nat := 1914073080848518809406883

theorem tailTrace_3727644 : CollatzResearch.WordTrace tailWord_3727644 prefixEnd_3727644 1914073080848518809406883 := by
  unfold tailWord_3727644
  simp only [CollatzResearch.WordTrace]
  refine ⟨67979173053694946877766993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90638897404926595837022657 67979173053694946877766993)
  ·
    refine ⟨50984379790271210158325245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67979173053694946877766993 50984379790271210158325245)
    ·
      refine ⟨19119142421351703809371967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50984379790271210158325245 19119142421351703809371967)
      ·
        refine ⟨28678713632027555714057951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19119142421351703809371967 28678713632027555714057951)
        ·
          refine ⟨43018070448041333571086927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28678713632027555714057951 43018070448041333571086927)
          ·
            refine ⟨64527105672062000356630391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43018070448041333571086927 64527105672062000356630391)
            ·
              refine ⟨96790658508093000534945587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64527105672062000356630391 96790658508093000534945587)
              ·
                refine ⟨145185987762139500802418381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96790658508093000534945587 145185987762139500802418381)
                ·
                  refine ⟨54444745410802312800906893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145185987762139500802418381 54444745410802312800906893)
                  ·
                    refine ⟨20416779529050867300340085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54444745410802312800906893 20416779529050867300340085)
                    ·
                      refine ⟨1914073080848518809406883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20416779529050867300340085 1914073080848518809406883)
                      ·
                        rfl

theorem cell23_3727644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_3727644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727644 prefixEnd_3727644 := by exact prefixLift 3727644
  have htrace : WordTrace (prefixWord ++ tailWord_3727644) baseStart_3727644 baseEnd_3727644 := by
    simpa [prefixWord, tailWord_3727644, baseEnd_3727644] using wordTrace_append hprefix tailTrace_3727644
  have hstable : (prefixWord ++ tailWord_3727644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727644).length < 2 ^ (prefixWord ++ tailWord_3727644).sum := by decide
  have hdescent : baseEnd_3727644 < baseStart_3727644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727652 : List Nat := [2, 3, 1, 3, 1, 4, 2, 1, 2, 1, 3]
def baseStart_3727652 : Nat := 118140960795 + 3727652 * 2 ^ 59
def prefixEnd_3727652 : Nat := 4983230072969 + 3 ^ 40 * 3727652 * 2
def baseEnd_3727652 : Nat := 1914077188693754778106847

theorem tailTrace_3727652 : CollatzResearch.WordTrace tailWord_3727652 prefixEnd_3727652 1914077188693754778106847 := by
  unfold tailWord_3727652
  simp only [CollatzResearch.WordTrace]
  refine ⟨67979318945680455560912605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90639091927573940747883473 67979318945680455560912605)
  ·
    refine ⟨25492244604630170835342227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67979318945680455560912605 25492244604630170835342227)
    ·
      refine ⟨38238366906945256253013341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25492244604630170835342227 38238366906945256253013341)
      ·
        refine ⟨14339387590104471094880003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38238366906945256253013341 14339387590104471094880003)
        ·
          refine ⟨21509081385156706642320005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14339387590104471094880003 21509081385156706642320005)
          ·
            refine ⟨4032952759716882495435001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21509081385156706642320005 4032952759716882495435001)
            ·
              refine ⟨3024714569787661871576251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4032952759716882495435001 3024714569787661871576251)
              ·
                refine ⟨4537071854681492807364377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3024714569787661871576251 4537071854681492807364377)
                ·
                  refine ⟨3402803891011119605523283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4537071854681492807364377 3402803891011119605523283)
                  ·
                    refine ⟨5104205836516679408284925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3402803891011119605523283 5104205836516679408284925)
                    ·
                      refine ⟨1914077188693754778106847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5104205836516679408284925 1914077188693754778106847)
                      ·
                        rfl

theorem cell23_3727652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_3727652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727652 prefixEnd_3727652 := by exact prefixLift 3727652
  have htrace : WordTrace (prefixWord ++ tailWord_3727652) baseStart_3727652 baseEnd_3727652 := by
    simpa [prefixWord, tailWord_3727652, baseEnd_3727652] using wordTrace_append hprefix tailTrace_3727652
  have hstable : (prefixWord ++ tailWord_3727652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727652).length < 2 ^ (prefixWord ++ tailWord_3727652).sum := by decide
  have hdescent : baseEnd_3727652 < baseStart_3727652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727662 : List Nat := [4, 1, 3, 3, 1, 1, 1, 1, 3, 3, 2]
def baseStart_3727662 : Nat := 118140960795 + 3727662 * 2 ^ 59
def prefixEnd_3727662 : Nat := 4983230072969 + 3 ^ 40 * 3727662 * 2
def baseEnd_3727662 : Nat := 1914082323500299738981801

theorem tailTrace_3727662 : CollatzResearch.WordTrace tailWord_3727662 prefixEnd_3727662 1914082323500299738981801 := by
  unfold tailWord_3727662
  simp only [CollatzResearch.WordTrace]
  refine ⟨16994875327665585353711155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90639335080883121886459493 16994875327665585353711155)
  ·
    refine ⟨25492312991498378030566733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16994875327665585353711155 25492312991498378030566733)
    ·
      refine ⟨9559617371811891761462525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25492312991498378030566733 9559617371811891761462525)
      ·
        refine ⟨3584856514429459410548447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9559617371811891761462525 3584856514429459410548447)
        ·
          refine ⟨5377284771644189115822671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3584856514429459410548447 5377284771644189115822671)
          ·
            refine ⟨8065927157466283673734007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5377284771644189115822671 8065927157466283673734007)
            ·
              refine ⟨12098890736199425510601011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8065927157466283673734007 12098890736199425510601011)
              ·
                refine ⟨18148336104299138265901517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12098890736199425510601011 18148336104299138265901517)
                ·
                  refine ⟨6805626039112176849713069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18148336104299138265901517 6805626039112176849713069)
                  ·
                    refine ⟨2552109764667066318642401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6805626039112176849713069 2552109764667066318642401)
                    ·
                      refine ⟨1914082323500299738981801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2552109764667066318642401 1914082323500299738981801)
                      ·
                        rfl

theorem cell23_3727662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_3727662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727662 prefixEnd_3727662 := by exact prefixLift 3727662
  have htrace : WordTrace (prefixWord ++ tailWord_3727662) baseStart_3727662 baseEnd_3727662 := by
    simpa [prefixWord, tailWord_3727662, baseEnd_3727662] using wordTrace_append hprefix tailTrace_3727662
  have hstable : (prefixWord ++ tailWord_3727662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727662).length < 2 ^ (prefixWord ++ tailWord_3727662).sum := by decide
  have hdescent : baseEnd_3727662 < baseStart_3727662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727704 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 1, 1, 7]
def baseStart_3727704 : Nat := 118140960795 + 3727704 * 2 ^ 59
def prefixEnd_3727704 : Nat := 4983230072969 + 3 ^ 40 * 3727704 * 2
def baseEnd_3727704 : Nat := 1914103889687788574656607

theorem tailTrace_3727704 : CollatzResearch.WordTrace tailWord_3727704 prefixEnd_3727704 1914103889687788574656607 := by
  unfold tailWord_3727704
  simp only [CollatzResearch.WordTrace]
  refine ⟨67980267243586262001359083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90640356324781682668478777 67980267243586262001359083)
  ·
    refine ⟨101970400865379393002038625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67980267243586262001359083 101970400865379393002038625)
    ·
      refine ⟨76477800649034544751528969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101970400865379393002038625 76477800649034544751528969)
      ·
        refine ⟨57358350486775908563646727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76477800649034544751528969 57358350486775908563646727)
        ·
          refine ⟨86037525730163862845470091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57358350486775908563646727 86037525730163862845470091)
          ·
            refine ⟨129056288595245794268205137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86037525730163862845470091 129056288595245794268205137)
            ·
              refine ⟨96792216446434345701153853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129056288595245794268205137 96792216446434345701153853)
              ·
                refine ⟨36297081167412879637932695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96792216446434345701153853 36297081167412879637932695)
                ·
                  refine ⟨54445621751119319456899043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36297081167412879637932695 54445621751119319456899043)
                  ·
                    refine ⟨81668432626678979185348565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54445621751119319456899043 81668432626678979185348565)
                    ·
                      refine ⟨1914103889687788574656607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 81668432626678979185348565 1914103889687788574656607)
                      ·
                        rfl

theorem cell23_3727704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_3727704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727704 prefixEnd_3727704 := by exact prefixLift 3727704
  have htrace : WordTrace (prefixWord ++ tailWord_3727704) baseStart_3727704 baseEnd_3727704 := by
    simpa [prefixWord, tailWord_3727704, baseEnd_3727704] using wordTrace_append hprefix tailTrace_3727704
  have hstable : (prefixWord ++ tailWord_3727704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727704).length < 2 ^ (prefixWord ++ tailWord_3727704).sum := by decide
  have hdescent : baseEnd_3727704 < baseStart_3727704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727728 : List Nat := [2, 1, 1, 1, 4, 5, 1, 1, 2, 5]
def baseStart_3727728 : Nat := 118140960795 + 3727728 * 2 ^ 59
def prefixEnd_3727728 : Nat := 4983230072969 + 3 ^ 40 * 3727728 * 2
def baseEnd_3727728 : Nat := 638038737741165493585499

theorem tailTrace_3727728 : CollatzResearch.WordTrace tailWord_3727728 prefixEnd_3727728 638038737741165493585499 := by
  unfold tailWord_3727728
  simp only [CollatzResearch.WordTrace]
  refine ⟨67980704919542788050795919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90640939892723717401061225 67980704919542788050795919)
  ·
    refine ⟨101971057379314182076193879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67980704919542788050795919 101971057379314182076193879)
    ·
      refine ⟨152956586068971273114290819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101971057379314182076193879 152956586068971273114290819)
      ·
        refine ⟨229434879103456909671436229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152956586068971273114290819 229434879103456909671436229)
        ·
          refine ⟨43019039831898170563394293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229434879103456909671436229 43019039831898170563394293)
          ·
            refine ⟨4033034984240453490318215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43019039831898170563394293 4033034984240453490318215)
            ·
              refine ⟨6049552476360680235477323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4033034984240453490318215 6049552476360680235477323)
              ·
                refine ⟨9074328714541020353215985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6049552476360680235477323 9074328714541020353215985)
                ·
                  refine ⟨6805746535905765264911989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9074328714541020353215985 6805746535905765264911989)
                  ·
                    refine ⟨638038737741165493585499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6805746535905765264911989 638038737741165493585499)
                    ·
                      rfl

theorem cell23_3727728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 2, 5].length) (baseStart_3727728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727728 prefixEnd_3727728 := by exact prefixLift 3727728
  have htrace : WordTrace (prefixWord ++ tailWord_3727728) baseStart_3727728 baseEnd_3727728 := by
    simpa [prefixWord, tailWord_3727728, baseEnd_3727728] using wordTrace_append hprefix tailTrace_3727728
  have hstable : (prefixWord ++ tailWord_3727728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727728).length < 2 ^ (prefixWord ++ tailWord_3727728).sum := by decide
  have hdescent : baseEnd_3727728 < baseStart_3727728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727748 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 4, 4, 2]
def baseStart_3727748 : Nat := 118140960795 + 3727748 * 2 ^ 59
def prefixEnd_3727748 : Nat := 4983230072969 + 3 ^ 40 * 3727748 * 2
def baseEnd_3727748 : Nat := 1914126482836586402506405

theorem tailTrace_3727748 : CollatzResearch.WordTrace tailWord_3727748 prefixEnd_3727748 1914126482836586402506405 := by
  unfold tailWord_3727748
  simp only [CollatzResearch.WordTrace]
  refine ⟨67981069649506559758659949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90641426199342079678213265 67981069649506559758659949)
  ·
    refine ⟨25492901118564959909497481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67981069649506559758659949 25492901118564959909497481)
    ·
      refine ⟨19119675838923719932123111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25492901118564959909497481 19119675838923719932123111)
      ·
        refine ⟨28679513758385579898184667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19119675838923719932123111 28679513758385579898184667)
        ·
          refine ⟨43019270637578369847277001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28679513758385579898184667 43019270637578369847277001)
          ·
            refine ⟨32264452978183777385457751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43019270637578369847277001 32264452978183777385457751)
            ·
              refine ⟨48396679467275666078186627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32264452978183777385457751 48396679467275666078186627)
              ·
                refine ⟨72595019200913499117279941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48396679467275666078186627 72595019200913499117279941)
                ·
                  refine ⟨13611566100171281084489989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72595019200913499117279941 13611566100171281084489989)
                  ·
                    refine ⟨2552168643782115203341873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13611566100171281084489989 2552168643782115203341873)
                    ·
                      refine ⟨1914126482836586402506405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2552168643782115203341873 1914126482836586402506405)
                      ·
                        rfl

theorem cell23_3727748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_3727748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727748 prefixEnd_3727748 := by exact prefixLift 3727748
  have htrace : WordTrace (prefixWord ++ tailWord_3727748) baseStart_3727748 baseEnd_3727748 := by
    simpa [prefixWord, tailWord_3727748, baseEnd_3727748] using wordTrace_append hprefix tailTrace_3727748
  have hstable : (prefixWord ++ tailWord_3727748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727748).length < 2 ^ (prefixWord ++ tailWord_3727748).sum := by decide
  have hdescent : baseEnd_3727748 < baseStart_3727748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727768 : List Nat := [2, 1, 2, 5, 1, 1, 1, 2, 1, 4, 3]
def baseStart_3727768 : Nat := 118140960795 + 3727768 * 2 ^ 59
def prefixEnd_3727768 : Nat := 4983230072969 + 3 ^ 40 * 3727768 * 2
def baseEnd_3727768 : Nat := 1914136752449676324256313

theorem tailTrace_3727768 : CollatzResearch.WordTrace tailWord_3727768 prefixEnd_3727768 1914136752449676324256313 := by
  unfold tailWord_3727768
  simp only [CollatzResearch.WordTrace]
  refine ⟨67981434379470331466523979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90641912505960441955365305 67981434379470331466523979)
  ·
    refine ⟨101972151569205497199785969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67981434379470331466523979 101972151569205497199785969)
    ·
      refine ⟨76479113676904122899839477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101972151569205497199785969 76479113676904122899839477)
      ·
        refine ⟨7169916907209761521859951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76479113676904122899839477 7169916907209761521859951)
        ·
          refine ⟨10754875360814642282789927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7169916907209761521859951 10754875360814642282789927)
          ·
            refine ⟨16132313041221963424184891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10754875360814642282789927 16132313041221963424184891)
            ·
              refine ⟨24198469561832945136277337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16132313041221963424184891 24198469561832945136277337)
              ·
                refine ⟨18148852171374708852208003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24198469561832945136277337 18148852171374708852208003)
                ·
                  refine ⟨27223278257062063278312005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18148852171374708852208003 27223278257062063278312005)
                  ·
                    refine ⟨5104364673199136864683501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27223278257062063278312005 5104364673199136864683501)
                    ·
                      refine ⟨1914136752449676324256313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5104364673199136864683501 1914136752449676324256313)
                      ·
                        rfl

theorem cell23_3727768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_3727768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727768 prefixEnd_3727768 := by exact prefixLift 3727768
  have htrace : WordTrace (prefixWord ++ tailWord_3727768) baseStart_3727768 baseEnd_3727768 := by
    simpa [prefixWord, tailWord_3727768, baseEnd_3727768] using wordTrace_append hprefix tailTrace_3727768
  have hstable : (prefixWord ++ tailWord_3727768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727768).length < 2 ^ (prefixWord ++ tailWord_3727768).sum := by decide
  have hdescent : baseEnd_3727768 < baseStart_3727768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727781 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 2, 5, 3]
def baseStart_3727781 : Nat := 118140960795 + 3727781 * 2 ^ 59
def prefixEnd_3727781 : Nat := 4983230072969 + 3 ^ 40 * 3727781 * 2
def baseEnd_3727781 : Nat := 1914143427698184773393753

theorem tailTrace_3727781 : CollatzResearch.WordTrace tailWord_3727781 prefixEnd_3727781 1914143427698184773393753 := by
  unfold tailWord_3727781
  simp only [CollatzResearch.WordTrace]
  refine ⟨135963342907893566153271197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90642228605262377435514131 135963342907893566153271197)
  ·
    refine ⟨50986253590460087307476699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135963342907893566153271197 50986253590460087307476699)
    ·
      refine ⟨76479380385690130961215049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50986253590460087307476699 76479380385690130961215049)
      ·
        refine ⟨57359535289267598220911287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76479380385690130961215049 57359535289267598220911287)
        ·
          refine ⟨86039302933901397331366931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57359535289267598220911287 86039302933901397331366931)
          ·
            refine ⟨129058954400852095997050397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86039302933901397331366931 129058954400852095997050397)
            ·
              refine ⟨48397107900319535998893899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129058954400852095997050397 48397107900319535998893899)
              ·
                refine ⟨72595661850479303998340849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48397107900319535998893899 72595661850479303998340849)
                ·
                  refine ⟨54446746387859477998755637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72595661850479303998340849 54446746387859477998755637)
                  ·
                    refine ⟨5104382473861826062383341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54446746387859477998755637 5104382473861826062383341)
                    ·
                      refine ⟨1914143427698184773393753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5104382473861826062383341 1914143427698184773393753)
                      ·
                        rfl

theorem cell23_3727781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_3727781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727781 prefixEnd_3727781 := by exact prefixLift 3727781
  have htrace : WordTrace (prefixWord ++ tailWord_3727781) baseStart_3727781 baseEnd_3727781 := by
    simpa [prefixWord, tailWord_3727781, baseEnd_3727781] using wordTrace_append hprefix tailTrace_3727781
  have hstable : (prefixWord ++ tailWord_3727781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727781).length < 2 ^ (prefixWord ++ tailWord_3727781).sum := by decide
  have hdescent : baseEnd_3727781 < baseStart_3727781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727815 : List Nat := [1, 1, 4, 1, 1, 4, 3, 1, 3, 1, 3]
def baseStart_3727815 : Nat := 118140960795 + 3727815 * 2 ^ 59
def prefixEnd_3727815 : Nat := 4983230072969 + 3 ^ 40 * 3727815 * 2
def baseEnd_3727815 : Nat := 1914160886040437640368597

theorem tailTrace_3727815 : CollatzResearch.WordTrace tailWord_3727815 prefixEnd_3727815 1914160886040437640368597 := by
  unfold tailWord_3727815
  simp only [CollatzResearch.WordTrace]
  refine ⟨135964582989770389960008899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90643055326513593306672599 135964582989770389960008899)
  ·
    refine ⟨203946874484655584940013349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135964582989770389960008899 203946874484655584940013349)
    ·
      refine ⟨38240038965872922176252503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203946874484655584940013349 38240038965872922176252503)
      ·
        refine ⟨57360058448809383264378755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38240038965872922176252503 57360058448809383264378755)
        ·
          refine ⟨86040087673214074896568133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57360058448809383264378755 86040087673214074896568133)
          ·
            refine ⟨16132516438727639043106525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86040087673214074896568133 16132516438727639043106525)
            ·
              refine ⟨6049693664522864641164947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16132516438727639043106525 6049693664522864641164947)
              ·
                refine ⟨9074540496784296961747421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6049693664522864641164947 9074540496784296961747421)
                ·
                  refine ⟨3402952686294111360655283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9074540496784296961747421 3402952686294111360655283)
                  ·
                    refine ⟨5104429029441167040982925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3402952686294111360655283 5104429029441167040982925)
                    ·
                      refine ⟨1914160886040437640368597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5104429029441167040982925 1914160886040437640368597)
                      ·
                        rfl

theorem cell23_3727815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_3727815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727815 prefixEnd_3727815 := by exact prefixLift 3727815
  have htrace : WordTrace (prefixWord ++ tailWord_3727815) baseStart_3727815 baseEnd_3727815 := by
    simpa [prefixWord, tailWord_3727815, baseEnd_3727815] using wordTrace_append hprefix tailTrace_3727815
  have hstable : (prefixWord ++ tailWord_3727815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727815).length < 2 ^ (prefixWord ++ tailWord_3727815).sum := by decide
  have hdescent : baseEnd_3727815 < baseStart_3727815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727848 : List Nat := [2, 1, 4, 1, 1, 4, 1, 2, 1, 6]
def baseStart_3727848 : Nat := 118140960795 + 3727848 * 2 ^ 59
def prefixEnd_3727848 : Nat := 4983230072969 + 3 ^ 40 * 3727848 * 2
def baseEnd_3727848 : Nat := 638059276967345337085315

theorem tailTrace_3727848 : CollatzResearch.WordTrace tailWord_3727848 prefixEnd_3727848 638059276967345337085315 := by
  unfold tailWord_3727848
  simp only [CollatzResearch.WordTrace]
  refine ⟨67982893299325418297980099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90643857732433891063973465 67982893299325418297980099)
  ·
    refine ⟨101974339948988127446970149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67982893299325418297980099 101974339948988127446970149)
    ·
      refine ⟨19120188740435273896306903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101974339948988127446970149 19120188740435273896306903)
      ·
        refine ⟨28680283110652910844460355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19120188740435273896306903 28680283110652910844460355)
        ·
          refine ⟨43020424665979366266690533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28680283110652910844460355 43020424665979366266690533)
          ·
            refine ⟨8066329624871131175004475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43020424665979366266690533 8066329624871131175004475)
            ·
              refine ⟨12099494437306696762506713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8066329624871131175004475 12099494437306696762506713)
              ·
                refine ⟨9074620827980022571880035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12099494437306696762506713 9074620827980022571880035)
                ·
                  refine ⟨13611931241970033857820053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9074620827980022571880035 13611931241970033857820053)
                  ·
                    refine ⟨638059276967345337085315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13611931241970033857820053 638059276967345337085315)
                    ·
                      rfl

theorem cell23_3727848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_3727848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727848 prefixEnd_3727848 := by exact prefixLift 3727848
  have htrace : WordTrace (prefixWord ++ tailWord_3727848) baseStart_3727848 baseEnd_3727848 := by
    simpa [prefixWord, tailWord_3727848, baseEnd_3727848] using wordTrace_append hprefix tailTrace_3727848
  have hstable : (prefixWord ++ tailWord_3727848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727848).length < 2 ^ (prefixWord ++ tailWord_3727848).sum := by decide
  have hdescent : baseEnd_3727848 < baseStart_3727848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727891 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 2, 7]
def baseStart_3727891 : Nat := 118140960795 + 3727891 * 2 ^ 59
def prefixEnd_3727891 : Nat := 4983230072969 + 3 ^ 40 * 3727891 * 2
def baseEnd_3727891 : Nat := 638066636856726447672749

theorem tailTrace_3727891 : CollatzResearch.WordTrace tailWord_3727891 prefixEnd_3727891 638066636856726447672749 := by
  unfold tailWord_3727891
  simp only [CollatzResearch.WordTrace]
  refine ⟨135967354937495054939775527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90644903291663369959850351 135967354937495054939775527)
  ·
    refine ⟨203951032406242582409663291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135967354937495054939775527 203951032406242582409663291)
    ·
      refine ⟨305926548609363873614494937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203951032406242582409663291 305926548609363873614494937)
      ·
        refine ⟨229444911457022905210871203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305926548609363873614494937 229444911457022905210871203)
        ·
          refine ⟨344167367185534357816306805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229444911457022905210871203 344167367185534357816306805)
          ·
            refine ⟨32265690673643846045278763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 344167367185534357816306805 32265690673643846045278763)
            ·
              refine ⟨48398536010465769067918145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32265690673643846045278763 48398536010465769067918145)
              ·
                refine ⟨36298902007849326800938609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48398536010465769067918145 36298902007849326800938609)
                ·
                  refine ⟨27224176505886995100703957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36298902007849326800938609 27224176505886995100703957)
                  ·
                    refine ⟨638066636856726447672749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27224176505886995100703957 638066636856726447672749)
                    ·
                      rfl

theorem cell23_3727891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 7].length) (baseStart_3727891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727891 prefixEnd_3727891 := by exact prefixLift 3727891
  have htrace : WordTrace (prefixWord ++ tailWord_3727891) baseStart_3727891 baseEnd_3727891 := by
    simpa [prefixWord, tailWord_3727891, baseEnd_3727891] using wordTrace_append hprefix tailTrace_3727891
  have hstable : (prefixWord ++ tailWord_3727891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727891).length < 2 ^ (prefixWord ++ tailWord_3727891).sum := by decide
  have hdescent : baseEnd_3727891 < baseStart_3727891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727892 : List Nat := [2, 4, 3, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_3727892 : Nat := 118140960795 + 3727892 * 2 ^ 59
def prefixEnd_3727892 : Nat := 4983230072969 + 3 ^ 40 * 3727892 * 2
def baseEnd_3727892 : Nat := 1914200424050833839105743

theorem tailTrace_3727892 : CollatzResearch.WordTrace tailWord_3727892 prefixEnd_3727892 1914200424050833839105743 := by
  unfold tailWord_3727892
  simp only [CollatzResearch.WordTrace]
  refine ⟨67983695705245716055280965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90644927606994288073707953 67983695705245716055280965)
  ·
    refine ⟨12746942944733571760365181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67983695705245716055280965 12746942944733571760365181)
    ·
      refine ⟨4780103604275089410136943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12746942944733571760365181 4780103604275089410136943)
      ·
        refine ⟨7170155406412634115205415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4780103604275089410136943 7170155406412634115205415)
        ·
          refine ⟨10755233109618951172808123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7170155406412634115205415 10755233109618951172808123)
          ·
            refine ⟨16132849664428426759212185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10755233109618951172808123 16132849664428426759212185)
            ·
              refine ⟨12099637248321320069409139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16132849664428426759212185 12099637248321320069409139)
              ·
                refine ⟨18149455872481980104113709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12099637248321320069409139 18149455872481980104113709)
                ·
                  refine ⟨6806045952180742539042641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18149455872481980104113709 6806045952180742539042641)
                  ·
                    refine ⟨5104534464135556904281981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6806045952180742539042641 5104534464135556904281981)
                    ·
                      refine ⟨1914200424050833839105743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5104534464135556904281981 1914200424050833839105743)
                      ·
                        rfl

theorem cell23_3727892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_3727892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727892 prefixEnd_3727892 := by exact prefixLift 3727892
  have htrace : WordTrace (prefixWord ++ tailWord_3727892) baseStart_3727892 baseEnd_3727892 := by
    simpa [prefixWord, tailWord_3727892, baseEnd_3727892] using wordTrace_append hprefix tailTrace_3727892
  have hstable : (prefixWord ++ tailWord_3727892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727892).length < 2 ^ (prefixWord ++ tailWord_3727892).sum := by decide
  have hdescent : baseEnd_3727892 < baseStart_3727892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727905 : List Nat := [1, 2, 3, 2, 2, 1, 2, 2, 4, 1, 3]
def baseStart_3727905 : Nat := 118140960795 + 3727905 * 2 ^ 59
def prefixEnd_3727905 : Nat := 4983230072969 + 3 ^ 40 * 3727905 * 2
def baseEnd_3727905 : Nat := 1914207099299342288243183

theorem tailTrace_3727905 : CollatzResearch.WordTrace tailWord_3727905 prefixEnd_3727905 1914207099299342288243183 := by
  unfold tailWord_3727905
  simp only [CollatzResearch.WordTrace]
  refine ⟨135967865559444335330785169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90645243706296223553856779 135967865559444335330785169)
  ·
    refine ⟨101975899169583251498088877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135967865559444335330785169 101975899169583251498088877)
    ·
      refine ⟨38240962188593719311783329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101975899169583251498088877 38240962188593719311783329)
      ·
        refine ⟨28680721641445289483837497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38240962188593719311783329 28680721641445289483837497)
        ·
          refine ⟨21510541231083967112878123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28680721641445289483837497 21510541231083967112878123)
          ·
            refine ⟨32265811846625950669317185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21510541231083967112878123 32265811846625950669317185)
            ·
              refine ⟨24199358884969463001987889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32265811846625950669317185 24199358884969463001987889)
              ·
                refine ⟨18149519163727097251490917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24199358884969463001987889 18149519163727097251490917)
                ·
                  refine ⟨3403034843198830734654547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18149519163727097251490917 3403034843198830734654547)
                  ·
                    refine ⟨5104552264798246101981821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3403034843198830734654547 5104552264798246101981821)
                    ·
                      refine ⟨1914207099299342288243183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5104552264798246101981821 1914207099299342288243183)
                      ·
                        rfl

theorem cell23_3727905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_3727905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727905 prefixEnd_3727905 := by exact prefixLift 3727905
  have htrace : WordTrace (prefixWord ++ tailWord_3727905) baseStart_3727905 baseEnd_3727905 := by
    simpa [prefixWord, tailWord_3727905, baseEnd_3727905] using wordTrace_append hprefix tailTrace_3727905
  have hstable : (prefixWord ++ tailWord_3727905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727905).length < 2 ^ (prefixWord ++ tailWord_3727905).sum := by decide
  have hdescent : baseEnd_3727905 < baseStart_3727905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727922 : List Nat := [3, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3]
def baseStart_3727922 : Nat := 118140960795 + 3727922 * 2 ^ 59
def prefixEnd_3727922 : Nat := 4983230072969 + 3 ^ 40 * 3727922 * 2
def baseEnd_3727922 : Nat := 1914215828470468721730605

theorem tailTrace_3727922 : CollatzResearch.WordTrace tailWord_3727922 prefixEnd_3727922 1914215828470468721730605 := by
  unfold tailWord_3727922
  simp only [CollatzResearch.WordTrace]
  refine ⟨33992121400095686808538505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90645657066921831489436013 33992121400095686808538505)
  ·
    refine ⟨25494091050071765106403879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33992121400095686808538505 25494091050071765106403879)
    ·
      refine ⟨38241136575107647659605819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25494091050071765106403879 38241136575107647659605819)
      ·
        refine ⟨57361704862661471489408729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38241136575107647659605819 57361704862661471489408729)
        ·
          refine ⟨43021278646996103617056547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57361704862661471489408729 43021278646996103617056547)
          ·
            refine ⟨64531917970494155425584821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43021278646996103617056547 64531917970494155425584821)
            ·
              refine ⟨6049867309733827071148577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64531917970494155425584821 6049867309733827071148577)
              ·
                refine ⟨4537400482300370303361433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6049867309733827071148577 4537400482300370303361433)
                ·
                  refine ⟨3403050361725277727521075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4537400482300370303361433 3403050361725277727521075)
                  ·
                    refine ⟨5104575542587916591281613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3403050361725277727521075 5104575542587916591281613)
                    ·
                      refine ⟨1914215828470468721730605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5104575542587916591281613 1914215828470468721730605)
                      ·
                        rfl

theorem cell23_3727922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_3727922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727922 prefixEnd_3727922 := by exact prefixLift 3727922
  have htrace : WordTrace (prefixWord ++ tailWord_3727922) baseStart_3727922 baseEnd_3727922 := by
    simpa [prefixWord, tailWord_3727922, baseEnd_3727922] using wordTrace_append hprefix tailTrace_3727922
  have hstable : (prefixWord ++ tailWord_3727922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727922).length < 2 ^ (prefixWord ++ tailWord_3727922).sum := by decide
  have hdescent : baseEnd_3727922 < baseStart_3727922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727948 : List Nat := [2, 2, 1, 3, 1, 2, 2, 2, 2, 1, 5]
def baseStart_3727948 : Nat := 118140960795 + 3727948 * 2 ^ 59
def prefixEnd_3727948 : Nat := 4983230072969 + 3 ^ 40 * 3727948 * 2
def baseEnd_3727948 : Nat := 1914229178967485620005485

theorem tailTrace_3727948 : CollatzResearch.WordTrace tailWord_3727948 prefixEnd_3727948 1914229178967485620005485 := by
  unfold tailWord_3727948
  simp only [CollatzResearch.WordTrace]
  refine ⟨67984716949144276837300249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90646289265525702449733665 67984716949144276837300249)
  ·
    refine ⟨50988537711858207627975187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67984716949144276837300249 50988537711858207627975187)
    ·
      refine ⟨76482806567787311441962781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50988537711858207627975187 76482806567787311441962781)
      ·
        refine ⟨28681052462920241790736043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76482806567787311441962781 28681052462920241790736043)
        ·
          refine ⟨43021578694380362686104065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28681052462920241790736043 43021578694380362686104065)
          ·
            refine ⟨32266184020785272014578049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43021578694380362686104065 32266184020785272014578049)
            ·
              refine ⟨24199638015588954010933537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32266184020785272014578049 24199638015588954010933537)
              ·
                refine ⟨18149728511691715508200153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24199638015588954010933537 18149728511691715508200153)
                ·
                  refine ⟨13612296383768786631150115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18149728511691715508200153 13612296383768786631150115)
                  ·
                    refine ⟨20418444575653179946725173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13612296383768786631150115 20418444575653179946725173)
                    ·
                      refine ⟨1914229178967485620005485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20418444575653179946725173 1914229178967485620005485)
                      ·
                        rfl

theorem cell23_3727948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_3727948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727948 prefixEnd_3727948 := by exact prefixLift 3727948
  have htrace : WordTrace (prefixWord ++ tailWord_3727948) baseStart_3727948 baseEnd_3727948 := by
    simpa [prefixWord, tailWord_3727948, baseEnd_3727948] using wordTrace_append hprefix tailTrace_3727948
  have hstable : (prefixWord ++ tailWord_3727948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727948).length < 2 ^ (prefixWord ++ tailWord_3727948).sum := by decide
  have hdescent : baseEnd_3727948 < baseStart_3727948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727949 : List Nat := [1, 6, 1, 1, 2, 1, 1, 4, 1, 3, 2]
def baseStart_3727949 : Nat := 118140960795 + 3727949 * 2 ^ 59
def prefixEnd_3727949 : Nat := 4983230072969 + 3 ^ 40 * 3727949 * 2
def baseEnd_3727949 : Nat := 1914229692448140116092981

theorem tailTrace_3727949 : CollatzResearch.WordTrace tailWord_3727949 prefixEnd_3727949 1914229692448140116092981 := by
  unfold tailWord_3727949
  simp only [CollatzResearch.WordTrace]
  refine ⟨135969470371284930845386901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90646313580856620563591267 135969470371284930845386901)
  ·
    refine ⟨6373568923653981133377511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 135969470371284930845386901 6373568923653981133377511)
    ·
      refine ⟨9560353385480971700066267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6373568923653981133377511 9560353385480971700066267)
      ·
        refine ⟨14340530078221457550099401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9560353385480971700066267 14340530078221457550099401)
        ·
          refine ⟨10755397558666093162574551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14340530078221457550099401 10755397558666093162574551)
          ·
            refine ⟨16133096337999139743861827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10755397558666093162574551 16133096337999139743861827)
            ·
              refine ⟨24199644506998709615792741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16133096337999139743861827 24199644506998709615792741)
              ·
                refine ⟨4537433345062258052961139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24199644506998709615792741 4537433345062258052961139)
                ·
                  refine ⟨6806150017593387079441709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4537433345062258052961139 6806150017593387079441709)
                  ·
                    refine ⟨2552306256597520154790641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6806150017593387079441709 2552306256597520154790641)
                    ·
                      refine ⟨1914229692448140116092981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2552306256597520154790641 1914229692448140116092981)
                      ·
                        rfl

theorem cell23_3727949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_3727949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727949 prefixEnd_3727949 := by exact prefixLift 3727949
  have htrace : WordTrace (prefixWord ++ tailWord_3727949) baseStart_3727949 baseEnd_3727949 := by
    simpa [prefixWord, tailWord_3727949, baseEnd_3727949] using wordTrace_append hprefix tailTrace_3727949
  have hstable : (prefixWord ++ tailWord_3727949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727949).length < 2 ^ (prefixWord ++ tailWord_3727949).sum := by decide
  have hdescent : baseEnd_3727949 < baseStart_3727949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3727978 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_3727978 : Nat := 118140960795 + 3727978 * 2 ^ 59
def prefixEnd_3727978 : Nat := 4983230072969 + 3 ^ 40 * 3727978 * 2
def baseEnd_3727978 : Nat := 1914244583387120502630347

theorem tailTrace_3727978 : CollatzResearch.WordTrace tailWord_3727978 prefixEnd_3727978 1914244583387120502630347 := by
  unfold tailWord_3727978
  simp only [CollatzResearch.WordTrace]
  refine ⟨33992632022044967199548147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90647018725453245865461725 33992632022044967199548147)
  ·
    refine ⟨50988948033067450799322221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33992632022044967199548147 50988948033067450799322221)
    ·
      refine ⟨19120855512400294049745833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50988948033067450799322221 19120855512400294049745833)
      ·
        refine ⟨14340641634300220537309375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19120855512400294049745833 14340641634300220537309375)
        ·
          refine ⟨21510962451450330805964063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14340641634300220537309375 21510962451450330805964063)
          ·
            refine ⟨32266443677175496208946095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21510962451450330805964063 32266443677175496208946095)
            ·
              refine ⟨48399665515763244313419143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32266443677175496208946095 48399665515763244313419143)
              ·
                refine ⟨72599498273644866470128715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48399665515763244313419143 72599498273644866470128715)
                ·
                  refine ⟨108899247410467299705193073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72599498273644866470128715 108899247410467299705193073)
                  ·
                    refine ⟨81674435557850474778894805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108899247410467299705193073 81674435557850474778894805)
                    ·
                      refine ⟨1914244583387120502630347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 81674435557850474778894805 1914244583387120502630347)
                      ·
                        rfl

theorem cell23_3727978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_3727978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3727978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3727978 prefixEnd_3727978 := by exact prefixLift 3727978
  have htrace : WordTrace (prefixWord ++ tailWord_3727978) baseStart_3727978 baseEnd_3727978 := by
    simpa [prefixWord, tailWord_3727978, baseEnd_3727978] using wordTrace_append hprefix tailTrace_3727978
  have hstable : (prefixWord ++ tailWord_3727978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3727978).length < 2 ^ (prefixWord ++ tailWord_3727978).sum := by decide
  have hdescent : baseEnd_3727978 < baseStart_3727978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3727978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728048 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 4]
def baseStart_3728048 : Nat := 118140960795 + 3728048 * 2 ^ 59
def prefixEnd_3728048 : Nat := 4983230072969 + 3 ^ 40 * 3728048 * 2
def baseEnd_3728048 : Nat := 1914280527032935228755025

theorem tailTrace_3728048 : CollatzResearch.WordTrace tailWord_3728048 prefixEnd_3728048 1914280527032935228755025 := by
  unfold tailWord_3728048
  simp only [CollatzResearch.WordTrace]
  refine ⟨67986540598963135376620399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90648720798617513835493865 67986540598963135376620399)
  ·
    refine ⟨101979810898444703064930599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67986540598963135376620399 101979810898444703064930599)
    ·
      refine ⟨152969716347667054597395899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101979810898444703064930599 152969716347667054597395899)
      ·
        refine ⟨229454574521500581896093849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152969716347667054597395899 229454574521500581896093849)
        ·
          refine ⟨172090930891125436422070387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229454574521500581896093849 172090930891125436422070387)
          ·
            refine ⟨258136396336688154633105581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172090930891125436422070387 258136396336688154633105581)
            ·
              refine ⟨96801148626258057987414593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258136396336688154633105581 96801148626258057987414593)
              ·
                refine ⟨72600861469693543490560945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96801148626258057987414593 72600861469693543490560945)
                ·
                  refine ⟨54450646102270157617920709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72600861469693543490560945 54450646102270157617920709)
                  ·
                    refine ⟨10209496144175654553360133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54450646102270157617920709 10209496144175654553360133)
                    ·
                      refine ⟨1914280527032935228755025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10209496144175654553360133 1914280527032935228755025)
                      ·
                        rfl

theorem cell23_3728048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 4].length) (baseStart_3728048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728048 prefixEnd_3728048 := by exact prefixLift 3728048
  have htrace : WordTrace (prefixWord ++ tailWord_3728048) baseStart_3728048 baseEnd_3728048 := by
    simpa [prefixWord, tailWord_3728048, baseEnd_3728048] using wordTrace_append hprefix tailTrace_3728048
  have hstable : (prefixWord ++ tailWord_3728048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728048).length < 2 ^ (prefixWord ++ tailWord_3728048).sum := by decide
  have hdescent : baseEnd_3728048 < baseStart_3728048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728062 : List Nat := [4, 2, 1, 1, 2, 1, 3, 2, 3, 4]
def baseStart_3728062 : Nat := 118140960795 + 3728062 * 2 ^ 59
def prefixEnd_3728062 : Nat := 4983230072969 + 3 ^ 40 * 3728062 * 2
def baseEnd_3728062 : Nat := 638095905254032724659987

theorem tailTrace_3728062 : CollatzResearch.WordTrace tailWord_3728062 prefixEnd_3728062 638095905254032724659987 := by
  unfold tailWord_3728062
  simp only [CollatzResearch.WordTrace]
  refine ⟨16996698977484443893031305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90649061213250367429500293 16996698977484443893031305)
  ·
    refine ⟨12747524233113332919773479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16996698977484443893031305 12747524233113332919773479)
    ·
      refine ⟨19121286349669999379660219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12747524233113332919773479 19121286349669999379660219)
      ·
        refine ⟨28681929524504999069490329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19121286349669999379660219 28681929524504999069490329)
        ·
          refine ⟨21511447143378749302117747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28681929524504999069490329 21511447143378749302117747)
          ·
            refine ⟨32267170715068123953176621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21511447143378749302117747 32267170715068123953176621)
            ·
              refine ⟨12100189018150546482441233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32267170715068123953176621 12100189018150546482441233)
              ·
                refine ⟨9075141763612909861830925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12100189018150546482441233 9075141763612909861830925)
                ·
                  refine ⟨3403178161354841198186597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9075141763612909861830925 3403178161354841198186597)
                  ·
                    refine ⟨638095905254032724659987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3403178161354841198186597 638095905254032724659987)
                    ·
                      rfl

theorem cell23_3728062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_3728062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728062 prefixEnd_3728062 := by exact prefixLift 3728062
  have htrace : WordTrace (prefixWord ++ tailWord_3728062) baseStart_3728062 baseEnd_3728062 := by
    simpa [prefixWord, tailWord_3728062, baseEnd_3728062] using wordTrace_append hprefix tailTrace_3728062
  have hstable : (prefixWord ++ tailWord_3728062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728062).length < 2 ^ (prefixWord ++ tailWord_3728062).sum := by decide
  have hdescent : baseEnd_3728062 < baseStart_3728062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728072 : List Nat := [2, 1, 3, 1, 2, 3, 3, 1, 2, 2, 3]
def baseStart_3728072 : Nat := 118140960795 + 3728072 * 2 ^ 59
def prefixEnd_3728072 : Nat := 4983230072969 + 3 ^ 40 * 3728072 * 2
def baseEnd_3728072 : Nat := 1914292850568643134854915

theorem tailTrace_3728072 : CollatzResearch.WordTrace tailWord_3728072 prefixEnd_3728072 1914292850568643134854915 := by
  unfold tailWord_3728072
  simp only [CollatzResearch.WordTrace]
  refine ⟨67986978274919661426057235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90649304366559548568076313 67986978274919661426057235)
  ·
    refine ⟨101980467412379492139085853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67986978274919661426057235 101980467412379492139085853)
    ·
      refine ⟨38242675279642309552157195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101980467412379492139085853 38242675279642309552157195)
      ·
        refine ⟨57364012919463464328235793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38242675279642309552157195 57364012919463464328235793)
        ·
          refine ⟨43023009689597598246176845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57364012919463464328235793 43023009689597598246176845)
          ·
            refine ⟨16133628633599099342316317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43023009689597598246176845 16133628633599099342316317)
            ·
              refine ⟨6050110737599662253368619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16133628633599099342316317 6050110737599662253368619)
              ·
                refine ⟨9075166106399493380052929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6050110737599662253368619 9075166106399493380052929)
                ·
                  refine ⟨6806374579799620035039697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9075166106399493380052929 6806374579799620035039697)
                  ·
                    refine ⟨5104780934849715026279773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6806374579799620035039697 5104780934849715026279773)
                    ·
                      refine ⟨1914292850568643134854915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5104780934849715026279773 1914292850568643134854915)
                      ·
                        rfl

theorem cell23_3728072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_3728072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728072 prefixEnd_3728072 := by exact prefixLift 3728072
  have htrace : WordTrace (prefixWord ++ tailWord_3728072) baseStart_3728072 baseEnd_3728072 := by
    simpa [prefixWord, tailWord_3728072, baseEnd_3728072] using wordTrace_append hprefix tailTrace_3728072
  have hstable : (prefixWord ++ tailWord_3728072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728072).length < 2 ^ (prefixWord ++ tailWord_3728072).sum := by decide
  have hdescent : baseEnd_3728072 < baseStart_3728072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728092 : List Nat := [2, 2, 5, 1, 1, 2, 1, 1, 8]
def baseStart_3728092 : Nat := 118140960795 + 3728092 * 2 ^ 59
def prefixEnd_3728092 : Nat := 4983230072969 + 3 ^ 40 * 3728092 * 2
def baseEnd_3728092 : Nat := 212700346686859228511647

theorem tailTrace_3728092 : CollatzResearch.WordTrace tailWord_3728092 prefixEnd_3728092 212700346686859228511647 := by
  unfold tailWord_3728092
  simp only [CollatzResearch.WordTrace]
  refine ⟨67987343004883433133921265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90649790673177910845228353 67987343004883433133921265)
  ·
    refine ⟨50990507253662574850440949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67987343004883433133921265 50990507253662574850440949)
    ·
      refine ⟨4780360055030866392228839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50990507253662574850440949 4780360055030866392228839)
      ·
        refine ⟨7170540082546299588343259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4780360055030866392228839 7170540082546299588343259)
        ·
          refine ⟨10755810123819449382514889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7170540082546299588343259 10755810123819449382514889)
          ·
            refine ⟨8066857592864587036886167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10755810123819449382514889 8066857592864587036886167)
            ·
              refine ⟨12100286389296880555329251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8066857592864587036886167 12100286389296880555329251)
              ·
                refine ⟨18150429583945320832993877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12100286389296880555329251 18150429583945320832993877)
                ·
                  refine ⟨212700346686859228511647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18150429583945320832993877 212700346686859228511647)
                  ·
                    rfl

theorem cell23_3728092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 8].length) (baseStart_3728092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728092 prefixEnd_3728092 := by exact prefixLift 3728092
  have htrace : WordTrace (prefixWord ++ tailWord_3728092) baseStart_3728092 baseEnd_3728092 := by
    simpa [prefixWord, tailWord_3728092, baseEnd_3728092] using wordTrace_append hprefix tailTrace_3728092
  have hstable : (prefixWord ++ tailWord_3728092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728092).length < 2 ^ (prefixWord ++ tailWord_3728092).sum := by decide
  have hdescent : baseEnd_3728092 < baseStart_3728092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728136 : List Nat := [2, 1, 3, 2, 2, 2, 3, 3, 1, 1, 3]
def baseStart_3728136 : Nat := 118140960795 + 3728136 * 2 ^ 59
def prefixEnd_3728136 : Nat := 4983230072969 + 3 ^ 40 * 3728136 * 2
def baseEnd_3728136 : Nat := 1914325713330530884454621

theorem tailTrace_3728136 : CollatzResearch.WordTrace tailWord_3728136 prefixEnd_3728136 1914325713330530884454621 := by
  unfold tailWord_3728136
  simp only [CollatzResearch.WordTrace]
  refine ⟨67988145410803730891222131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90650860547738307854962841 67988145410803730891222131)
  ·
    refine ⟨101982218116205596336833197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67988145410803730891222131 101982218116205596336833197)
    ·
      refine ⟨38243331793577098626312449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101982218116205596336833197 38243331793577098626312449)
      ·
        refine ⟨28682498845182823969734337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38243331793577098626312449 28682498845182823969734337)
        ·
          refine ⟨21511874133887117977300753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28682498845182823969734337 21511874133887117977300753)
          ·
            refine ⟨16133905600415338482975565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21511874133887117977300753 16133905600415338482975565)
            ·
              refine ⟨6050214600155751931115837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16133905600415338482975565 6050214600155751931115837)
              ·
                refine ⟨2268830475058406974168439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6050214600155751931115837 2268830475058406974168439)
                ·
                  refine ⟨3403245712587610461252659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2268830475058406974168439 3403245712587610461252659)
                  ·
                    refine ⟨5104868568881415691878989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3403245712587610461252659 5104868568881415691878989)
                    ·
                      refine ⟨1914325713330530884454621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5104868568881415691878989 1914325713330530884454621)
                      ·
                        rfl

theorem cell23_3728136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_3728136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728136 prefixEnd_3728136 := by exact prefixLift 3728136
  have htrace : WordTrace (prefixWord ++ tailWord_3728136) baseStart_3728136 baseEnd_3728136 := by
    simpa [prefixWord, tailWord_3728136, baseEnd_3728136] using wordTrace_append hprefix tailTrace_3728136
  have hstable : (prefixWord ++ tailWord_3728136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728136).length < 2 ^ (prefixWord ++ tailWord_3728136).sum := by decide
  have hdescent : baseEnd_3728136 < baseStart_3728136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728145 : List Nat := [1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 5]
def baseStart_3728145 : Nat := 118140960795 + 3728145 * 2 ^ 59
def prefixEnd_3728145 : Nat := 4983230072969 + 3 ^ 40 * 3728145 * 2
def baseEnd_3728145 : Nat := 1914330334656421349242079

theorem tailTrace_3728145 : CollatzResearch.WordTrace tailWord_3728145 prefixEnd_3728145 1914330334656421349242079 := by
  unfold tailWord_3728145
  simp only [CollatzResearch.WordTrace]
  refine ⟨135976619078574856319521889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90651079385716570879681259 135976619078574856319521889)
  ·
    refine ⟨101982464308931142239641417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135976619078574856319521889 101982464308931142239641417)
    ·
      refine ⟨76486848231698356679731063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101982464308931142239641417 76486848231698356679731063)
      ·
        refine ⟨114730272347547535019596595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76486848231698356679731063 114730272347547535019596595)
        ·
          refine ⟨172095408521321302529394893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114730272347547535019596595 172095408521321302529394893)
          ·
            refine ⟨64535778195495488448523085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172095408521321302529394893 64535778195495488448523085)
            ·
              refine ⟨24200916823310808168196157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64535778195495488448523085 24200916823310808168196157)
              ·
                refine ⟨9075343808741553063073559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24200916823310808168196157 9075343808741553063073559)
                ·
                  refine ⟨13613015713112329594610339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9075343808741553063073559 13613015713112329594610339)
                  ·
                    refine ⟨20419523569668494391915509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13613015713112329594610339 20419523569668494391915509)
                    ·
                      refine ⟨1914330334656421349242079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20419523569668494391915509 1914330334656421349242079)
                      ·
                        rfl

theorem cell23_3728145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_3728145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728145 prefixEnd_3728145 := by exact prefixLift 3728145
  have htrace : WordTrace (prefixWord ++ tailWord_3728145) baseStart_3728145 baseEnd_3728145 := by
    simpa [prefixWord, tailWord_3728145, baseEnd_3728145] using wordTrace_append hprefix tailTrace_3728145
  have hstable : (prefixWord ++ tailWord_3728145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728145).length < 2 ^ (prefixWord ++ tailWord_3728145).sum := by decide
  have hdescent : baseEnd_3728145 < baseStart_3728145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728152 : List Nat := [2, 1, 2, 3, 1, 1, 1, 6, 2, 4]
def baseStart_3728152 : Nat := 118140960795 + 3728152 * 2 ^ 59
def prefixEnd_3728152 : Nat := 4983230072969 + 3 ^ 40 * 3728152 * 2
def baseEnd_3728152 : Nat := 638111309673667607284849

theorem tailTrace_3728152 : CollatzResearch.WordTrace tailWord_3728152 prefixEnd_3728152 638111309673667607284849 := by
  unfold tailWord_3728152
  simp only [CollatzResearch.WordTrace]
  refine ⟨67988437194774748257513355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90651249593032997676684473 67988437194774748257513355)
  ·
    refine ⟨101982655792162122386270033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67988437194774748257513355 101982655792162122386270033)
    ·
      refine ⟨76486991844121591789702525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101982655792162122386270033 76486991844121591789702525)
      ·
        refine ⟨28682621941545596921138447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76486991844121591789702525 28682621941545596921138447)
        ·
          refine ⟨43023932912318395381707671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28682621941545596921138447 43023932912318395381707671)
          ·
            refine ⟨64535899368477593072561507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43023932912318395381707671 64535899368477593072561507)
            ·
              refine ⟨96803849052716389608842261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64535899368477593072561507 96803849052716389608842261)
              ·
                refine ⟨4537680424346080762914481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96803849052716389608842261 4537680424346080762914481)
                ·
                  refine ⟨3403260318259560572185861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4537680424346080762914481 3403260318259560572185861)
                  ·
                    refine ⟨638111309673667607284849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3403260318259560572185861 638111309673667607284849)
                    ·
                      rfl

theorem cell23_3728152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 2, 4].length) (baseStart_3728152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728152 prefixEnd_3728152 := by exact prefixLift 3728152
  have htrace : WordTrace (prefixWord ++ tailWord_3728152) baseStart_3728152 baseEnd_3728152 := by
    simpa [prefixWord, tailWord_3728152, baseEnd_3728152] using wordTrace_append hprefix tailTrace_3728152
  have hstable : (prefixWord ++ tailWord_3728152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728152).length < 2 ^ (prefixWord ++ tailWord_3728152).sum := by decide
  have hdescent : baseEnd_3728152 < baseStart_3728152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728162 : List Nat := [3, 3, 1, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_3728162 : Nat := 118140960795 + 3728162 * 2 ^ 59
def prefixEnd_3728162 : Nat := 4983230072969 + 3 ^ 40 * 3728162 * 2
def baseEnd_3728162 : Nat := 1914339063827547782729501

theorem tailTrace_3728162 : CollatzResearch.WordTrace tailWord_3728162 prefixEnd_3728162 1914339063827547782729501 := by
  unfold tailWord_3728162
  simp only [CollatzResearch.WordTrace]
  refine ⟨33994309779878317055722685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90651492746342178815260493 33994309779878317055722685)
  ·
    refine ⟨12747866167454368895896007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33994309779878317055722685 12747866167454368895896007)
    ·
      refine ⟨19121799251181553343844011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12747866167454368895896007 19121799251181553343844011)
      ·
        refine ⟨28682698876772330015766017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19121799251181553343844011 28682698876772330015766017)
        ·
          refine ⟨21512024157579247511824513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28682698876772330015766017 21512024157579247511824513)
          ·
            refine ⟨16134018118184435633868385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21512024157579247511824513 16134018118184435633868385)
            ·
              refine ⟨12100513588638326725401289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16134018118184435633868385 12100513588638326725401289)
              ·
                refine ⟨9075385191478745044050967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12100513588638326725401289 9075385191478745044050967)
                ·
                  refine ⟨13613077787218117566076451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9075385191478745044050967 13613077787218117566076451)
                  ·
                    refine ⟨20419616680827176349114677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13613077787218117566076451 20419616680827176349114677)
                    ·
                      refine ⟨1914339063827547782729501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20419616680827176349114677 1914339063827547782729501)
                      ·
                        rfl

theorem cell23_3728162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_3728162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728162 prefixEnd_3728162 := by exact prefixLift 3728162
  have htrace : WordTrace (prefixWord ++ tailWord_3728162) baseStart_3728162 baseEnd_3728162 := by
    simpa [prefixWord, tailWord_3728162, baseEnd_3728162] using wordTrace_append hprefix tailTrace_3728162
  have hstable : (prefixWord ++ tailWord_3728162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728162).length < 2 ^ (prefixWord ++ tailWord_3728162).sum := by decide
  have hdescent : baseEnd_3728162 < baseStart_3728162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728165 : List Nat := [1, 3, 1, 2, 3, 1, 4, 8]
def baseStart_3728165 : Nat := 118140960795 + 3728165 * 2 ^ 59
def prefixEnd_3728165 : Nat := 4983230072969 + 3 ^ 40 * 3728165 * 2
def baseEnd_3728165 : Nat := 70901503861833750777481

theorem tailTrace_3728165 : CollatzResearch.WordTrace tailWord_3728165 prefixEnd_3728165 70901503861833750777481 := by
  unfold tailWord_3728165
  simp only [CollatzResearch.WordTrace]
  refine ⟨135977348538502399735249949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90651565692334933156833299 135977348538502399735249949)
  ·
    refine ⟨50991505701938399900718731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135977348538502399735249949 50991505701938399900718731)
    ·
      refine ⟨76487258552907599851078097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50991505701938399900718731 76487258552907599851078097)
      ·
        refine ⟨57365443914680699888308573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76487258552907599851078097 57365443914680699888308573)
        ·
          refine ⟨21512041468005262458115715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57365443914680699888308573 21512041468005262458115715)
          ·
            refine ⟨32268062202007893687173573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21512041468005262458115715 32268062202007893687173573)
            ·
              refine ⟨6050261662876480066345045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32268062202007893687173573 6050261662876480066345045)
              ·
                refine ⟨70901503861833750777481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6050261662876480066345045 70901503861833750777481)
                ·
                  rfl

theorem cell23_3728165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 8].length) (baseStart_3728165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728165 prefixEnd_3728165 := by exact prefixLift 3728165
  have htrace : WordTrace (prefixWord ++ tailWord_3728165) baseStart_3728165 baseEnd_3728165 := by
    simpa [prefixWord, tailWord_3728165, baseEnd_3728165] using wordTrace_append hprefix tailTrace_3728165
  have hstable : (prefixWord ++ tailWord_3728165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728165).length < 2 ^ (prefixWord ++ tailWord_3728165).sum := by decide
  have hdescent : baseEnd_3728165 < baseStart_3728165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728173 : List Nat := [1, 5, 3, 2, 1, 2, 1, 2, 1, 5]
def baseStart_3728173 : Nat := 118140960795 + 3728173 * 2 ^ 59
def prefixEnd_3728173 : Nat := 4983230072969 + 3 ^ 40 * 3728173 * 2
def baseEnd_3728173 : Nat := 638114904038249079897317

theorem tailTrace_3728173 : CollatzResearch.WordTrace tailWord_3728173 prefixEnd_3728173 638114904038249079897317 := by
  unfold tailWord_3728173
  simp only [CollatzResearch.WordTrace]
  refine ⟨135977640322473417101541173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90651760214982278067694115 135977640322473417101541173)
  ·
    refine ⟨12747903780231882853269485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135977640322473417101541173 12747903780231882853269485)
    ·
      refine ⟨4780463917586956069976057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12747903780231882853269485 4780463917586956069976057)
      ·
        refine ⟨3585347938190217052482043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4780463917586956069976057 3585347938190217052482043)
        ·
          refine ⟨5378021907285325578723065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3585347938190217052482043 5378021907285325578723065)
          ·
            refine ⟨4033516430463994184042299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5378021907285325578723065 4033516430463994184042299)
            ·
              refine ⟨6050274645695991276063449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4033516430463994184042299 6050274645695991276063449)
              ·
                refine ⟨4537705984271993457047587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6050274645695991276063449 4537705984271993457047587)
                ·
                  refine ⟨6806558976407990185571381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4537705984271993457047587 6806558976407990185571381)
                  ·
                    refine ⟨638114904038249079897317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6806558976407990185571381 638114904038249079897317)
                    ·
                      rfl

theorem cell23_3728173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_3728173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728173 prefixEnd_3728173 := by exact prefixLift 3728173
  have htrace : WordTrace (prefixWord ++ tailWord_3728173) baseStart_3728173 baseEnd_3728173 := by
    simpa [prefixWord, tailWord_3728173, baseEnd_3728173] using wordTrace_append hprefix tailTrace_3728173
  have hstable : (prefixWord ++ tailWord_3728173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728173).length < 2 ^ (prefixWord ++ tailWord_3728173).sum := by decide
  have hdescent : baseEnd_3728173 < baseStart_3728173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728179 : List Nat := [1, 1, 1, 2, 6, 1, 3, 2, 1, 2, 3]
def baseStart_3728179 : Nat := 118140960795 + 3728179 * 2 ^ 59
def prefixEnd_3728179 : Nat := 4983230072969 + 3 ^ 40 * 3728179 * 2
def baseEnd_3728179 : Nat := 1914347792998674216216923

theorem tailTrace_3728179 : CollatzResearch.WordTrace tailWord_3728179 prefixEnd_3728179 1914347792998674216216923 := by
  unfold tailWord_3728179
  simp only [CollatzResearch.WordTrace]
  refine ⟨135977859160451680126259591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90651906106967786750839727 135977859160451680126259591)
  ·
    refine ⟨203966788740677520189389387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135977859160451680126259591 203966788740677520189389387)
    ·
      refine ⟨305950183111016280284084081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203966788740677520189389387 305950183111016280284084081)
      ·
        refine ⟨229462637333262210213063061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305950183111016280284084081 229462637333262210213063061)
        ·
          refine ⟨10756061124996666103737331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 229462637333262210213063061 10756061124996666103737331)
          ·
            refine ⟨16134091687494999155605997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10756061124996666103737331 16134091687494999155605997)
            ·
              refine ⟨6050284382810624683352249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16134091687494999155605997 6050284382810624683352249)
              ·
                refine ⟨4537713287107968512514187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6050284382810624683352249 4537713287107968512514187)
                ·
                  refine ⟨6806569930661952768771281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4537713287107968512514187 6806569930661952768771281)
                  ·
                    refine ⟨5104927447996464576578461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6806569930661952768771281 5104927447996464576578461)
                    ·
                      refine ⟨1914347792998674216216923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5104927447996464576578461 1914347792998674216216923)
                      ·
                        rfl

theorem cell23_3728179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 2, 3].length) (baseStart_3728179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728179 prefixEnd_3728179 := by exact prefixLift 3728179
  have htrace : WordTrace (prefixWord ++ tailWord_3728179) baseStart_3728179 baseEnd_3728179 := by
    simpa [prefixWord, tailWord_3728179, baseEnd_3728179] using wordTrace_append hprefix tailTrace_3728179
  have hstable : (prefixWord ++ tailWord_3728179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728179).length < 2 ^ (prefixWord ++ tailWord_3728179).sum := by decide
  have hdescent : baseEnd_3728179 < baseStart_3728179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728189 : List Nat := [1, 4, 1, 4, 2, 1, 1, 2, 1, 2, 4]
def baseStart_3728189 : Nat := 118140960795 + 3728189 * 2 ^ 59
def prefixEnd_3728189 : Nat := 4983230072969 + 3 ^ 40 * 3728189 * 2
def baseEnd_3728189 : Nat := 1914352927805219177091877

theorem tailTrace_3728189 : CollatzResearch.WordTrace tailWord_3728189 prefixEnd_3728189 1914352927805219177091877 := by
  unfold tailWord_3728189
  simp only [CollatzResearch.WordTrace]
  refine ⟨135978223890415451834123621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90652149260276967889415747 135978223890415451834123621)
  ·
    refine ⟨25495916979452897218898179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135978223890415451834123621 25495916979452897218898179)
    ·
      refine ⟨38243875469179345828347269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25495916979452897218898179 38243875469179345828347269)
      ·
        refine ⟨7170726650471127342815113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38243875469179345828347269 7170726650471127342815113)
        ·
          refine ⟨5378044987853345507111335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7170726650471127342815113 5378044987853345507111335)
          ·
            refine ⟨8067067481780018260667003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5378044987853345507111335 8067067481780018260667003)
            ·
              refine ⟨12100601222670027391000505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8067067481780018260667003 12100601222670027391000505)
              ·
                refine ⟨9075450917002520543250379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12100601222670027391000505 9075450917002520543250379)
                ·
                  refine ⟨13613176375503780814875569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9075450917002520543250379 13613176375503780814875569)
                  ·
                    refine ⟨10209882281627835611156677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13613176375503780814875569 10209882281627835611156677)
                    ·
                      refine ⟨1914352927805219177091877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10209882281627835611156677 1914352927805219177091877)
                      ·
                        rfl

theorem cell23_3728189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_3728189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728189 prefixEnd_3728189 := by exact prefixLift 3728189
  have htrace : WordTrace (prefixWord ++ tailWord_3728189) baseStart_3728189 baseEnd_3728189 := by
    simpa [prefixWord, tailWord_3728189, baseEnd_3728189] using wordTrace_append hprefix tailTrace_3728189
  have hstable : (prefixWord ++ tailWord_3728189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728189).length < 2 ^ (prefixWord ++ tailWord_3728189).sum := by decide
  have hdescent : baseEnd_3728189 < baseStart_3728189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728192 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 6, 1, 3]
def baseStart_3728192 : Nat := 118140960795 + 3728192 * 2 ^ 59
def prefixEnd_3728192 : Nat := 4983230072969 + 3 ^ 40 * 3728192 * 2
def baseEnd_3728192 : Nat := 1914354468247182665354363

theorem tailTrace_3728192 : CollatzResearch.WordTrace tailWord_3728192 prefixEnd_3728192 1914354468247182665354363 := by
  unfold tailWord_3728192
  simp only [CollatzResearch.WordTrace]
  refine ⟨67989166654702291673241415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90652222206269722230988553 67989166654702291673241415)
  ·
    refine ⟨101983749982053437509862123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67989166654702291673241415 101983749982053437509862123)
    ·
      refine ⟨152975624973080156264793185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101983749982053437509862123 152975624973080156264793185)
      ·
        refine ⟨114731718729810117198594889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152975624973080156264793185 114731718729810117198594889)
        ·
          refine ⟨86048789047357587898946167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114731718729810117198594889 86048789047357587898946167)
          ·
            refine ⟨129073183571036381848419251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86048789047357587898946167 129073183571036381848419251)
            ·
              refine ⟨193609775356554572772628877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129073183571036381848419251 193609775356554572772628877)
              ·
                refine ⟨72603665758707964789735829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193609775356554572772628877 72603665758707964789735829)
                ·
                  refine ⟨3403296832439435849518867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72603665758707964789735829 3403296832439435849518867)
                  ·
                    refine ⟨5104945248659153774278301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3403296832439435849518867 5104945248659153774278301)
                    ·
                      refine ⟨1914354468247182665354363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5104945248659153774278301 1914354468247182665354363)
                      ·
                        rfl

theorem cell23_3728192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 6, 1, 3].length) (baseStart_3728192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728192 prefixEnd_3728192 := by exact prefixLift 3728192
  have htrace : WordTrace (prefixWord ++ tailWord_3728192) baseStart_3728192 baseEnd_3728192 := by
    simpa [prefixWord, tailWord_3728192, baseEnd_3728192] using wordTrace_append hprefix tailTrace_3728192
  have hstable : (prefixWord ++ tailWord_3728192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728192).length < 2 ^ (prefixWord ++ tailWord_3728192).sum := by decide
  have hdescent : baseEnd_3728192 < baseStart_3728192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728193 : List Nat := [1, 2, 5, 3, 1, 1, 3, 1, 1, 1, 4]
def baseStart_3728193 : Nat := 118140960795 + 3728193 * 2 ^ 59
def prefixEnd_3728193 : Nat := 4983230072969 + 3 ^ 40 * 3728193 * 2
def baseEnd_3728193 : Nat := 1914354981727837161441859

theorem tailTrace_3728193 : CollatzResearch.WordTrace tailWord_3728193 prefixEnd_3728193 1914354981727837161441859 := by
  unfold tailWord_3728193
  simp only [CollatzResearch.WordTrace]
  refine ⟨135978369782400960517269233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90652246521600640344846155 135978369782400960517269233)
  ·
    refine ⟨101983777336800720387951925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135978369782400960517269233 101983777336800720387951925)
    ·
      refine ⟨9560979125325067536370493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101983777336800720387951925 9560979125325067536370493)
      ·
        refine ⟨3585367171996900326138935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9560979125325067536370493 3585367171996900326138935)
        ·
          refine ⟨5378050757995350489208403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3585367171996900326138935 5378050757995350489208403)
          ·
            refine ⟨8067076136993025733812605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5378050757995350489208403 8067076136993025733812605)
            ·
              refine ⟨3025153551372384650179727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8067076136993025733812605 3025153551372384650179727)
              ·
                refine ⟨4537730327058576975269591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3025153551372384650179727 4537730327058576975269591)
                ·
                  refine ⟨6806595490587865462904387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4537730327058576975269591 6806595490587865462904387)
                  ·
                    refine ⟨10209893235881798194356581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6806595490587865462904387 10209893235881798194356581)
                    ·
                      refine ⟨1914354981727837161441859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10209893235881798194356581 1914354981727837161441859)
                      ·
                        rfl

theorem cell23_3728193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_3728193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728193 prefixEnd_3728193 := by exact prefixLift 3728193
  have htrace : WordTrace (prefixWord ++ tailWord_3728193) baseStart_3728193 baseEnd_3728193 := by
    simpa [prefixWord, tailWord_3728193, baseEnd_3728193] using wordTrace_append hprefix tailTrace_3728193
  have hstable : (prefixWord ++ tailWord_3728193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728193).length < 2 ^ (prefixWord ++ tailWord_3728193).sum := by decide
  have hdescent : baseEnd_3728193 < baseStart_3728193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728226 : List Nat := [3, 3, 2, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_3728226 : Nat := 118140960795 + 3728226 * 2 ^ 59
def prefixEnd_3728226 : Nat := 4983230072969 + 3 ^ 40 * 3728226 * 2
def baseEnd_3728226 : Nat := 1914371926589435532329207

theorem tailTrace_3728226 : CollatzResearch.WordTrace tailWord_3728226 prefixEnd_3728226 1914371926589435532329207 := by
  unfold tailWord_3728226
  simp only [CollatzResearch.WordTrace]
  refine ⟨33994893347820351788305133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90653048927520938102147021 33994893347820351788305133)
  ·
    refine ⟨12748085005432631920614425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33994893347820351788305133 12748085005432631920614425)
    ·
      refine ⟨9561063754074473940460819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12748085005432631920614425 9561063754074473940460819)
      ·
        refine ⟨14341595631111710910691229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9561063754074473940460819 14341595631111710910691229)
        ·
          refine ⟨5378098361666891591509211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14341595631111710910691229 5378098361666891591509211)
          ·
            refine ⟨8067147542500337387263817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5378098361666891591509211 8067147542500337387263817)
            ·
              refine ⟨6050360656875253040447863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8067147542500337387263817 6050360656875253040447863)
              ·
                refine ⟨9075540985312879560671795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6050360656875253040447863 9075540985312879560671795)
                ·
                  refine ⟨13613311477969319341007693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9075540985312879560671795 13613311477969319341007693)
                  ·
                    refine ⟨5104991804238494752877885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13613311477969319341007693 5104991804238494752877885)
                    ·
                      refine ⟨1914371926589435532329207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5104991804238494752877885 1914371926589435532329207)
                      ·
                        rfl

theorem cell23_3728226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_3728226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728226 prefixEnd_3728226 := by exact prefixLift 3728226
  have htrace : WordTrace (prefixWord ++ tailWord_3728226) baseStart_3728226 baseEnd_3728226 := by
    simpa [prefixWord, tailWord_3728226, baseEnd_3728226] using wordTrace_append hprefix tailTrace_3728226
  have hstable : (prefixWord ++ tailWord_3728226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728226).length < 2 ^ (prefixWord ++ tailWord_3728226).sum := by decide
  have hdescent : baseEnd_3728226 < baseStart_3728226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728235 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 5]
def baseStart_3728235 : Nat := 118140960795 + 3728235 * 2 ^ 59
def prefixEnd_3728235 : Nat := 4983230072969 + 3 ^ 40 * 3728235 * 2
def baseEnd_3728235 : Nat := 1914376547915325997116665

theorem tailTrace_3728235 : CollatzResearch.WordTrace tailWord_3728235 prefixEnd_3728235 1914376547915325997116665 := by
  unfold tailWord_3728235
  simp only [CollatzResearch.WordTrace]
  refine ⟨135979901648248801690298159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90653267765499201126865439 135979901648248801690298159)
  ·
    refine ⟨203969852472373202535447239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135979901648248801690298159 203969852472373202535447239)
    ·
      refine ⟨305954778708559803803170859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203969852472373202535447239 305954778708559803803170859)
      ·
        refine ⟨458932168062839705704756289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305954778708559803803170859 458932168062839705704756289)
        ·
          refine ⟨344199126047129779278567217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 458932168062839705704756289 344199126047129779278567217)
          ·
            refine ⟨258149344535347334458925413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344199126047129779278567217 258149344535347334458925413)
            ·
              refine ⟨48403002100377625211048515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 258149344535347334458925413 48403002100377625211048515)
              ·
                refine ⟨72604503150566437816572773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48403002100377625211048515 72604503150566437816572773)
                ·
                  refine ⟨13613344340731207090607395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72604503150566437816572773 13613344340731207090607395)
                  ·
                    refine ⟨20420016511096810635911093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13613344340731207090607395 20420016511096810635911093)
                    ·
                      refine ⟨1914376547915325997116665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20420016511096810635911093 1914376547915325997116665)
                      ·
                        rfl

theorem cell23_3728235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 5].length) (baseStart_3728235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728235 prefixEnd_3728235 := by exact prefixLift 3728235
  have htrace : WordTrace (prefixWord ++ tailWord_3728235) baseStart_3728235 baseEnd_3728235 := by
    simpa [prefixWord, tailWord_3728235, baseEnd_3728235] using wordTrace_append hprefix tailTrace_3728235
  have hstable : (prefixWord ++ tailWord_3728235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728235).length < 2 ^ (prefixWord ++ tailWord_3728235).sum := by decide
  have hdescent : baseEnd_3728235 < baseStart_3728235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728249 : List Nat := [1, 2, 1, 3, 2, 3, 2, 2, 1, 4, 2]
def baseStart_3728249 : Nat := 118140960795 + 3728249 * 2 ^ 59
def prefixEnd_3728249 : Nat := 4983230072969 + 3 ^ 40 * 3728249 * 2
def baseEnd_3728249 : Nat := 1914383736644488942341601

theorem tailTrace_3728249 : CollatzResearch.WordTrace tailWord_3728249 prefixEnd_3728249 1914383736644488942341601 := by
  unfold tailWord_3728249
  simp only [CollatzResearch.WordTrace]
  refine ⟨135980412270198082081307801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90653608180132054720871867 135980412270198082081307801)
  ·
    refine ⟨101985309202648561560980851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135980412270198082081307801 101985309202648561560980851)
    ·
      refine ⟨152977963803972842341471277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101985309202648561560980851 152977963803972842341471277)
      ·
        refine ⟨57366736426489815878051729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152977963803972842341471277 57366736426489815878051729)
        ·
          refine ⟨43025052319867361908538797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57366736426489815878051729 43025052319867361908538797)
          ·
            refine ⟨16134394619950260715702049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43025052319867361908538797 16134394619950260715702049)
            ·
              refine ⟨12100795964962695536776537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16134394619950260715702049 12100795964962695536776537)
              ·
                refine ⟨9075596973722021652582403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12100795964962695536776537 9075596973722021652582403)
                ·
                  refine ⟨13613395460583032478873605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9075596973722021652582403 13613395460583032478873605)
                  ·
                    refine ⟨2552511648859318589788801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13613395460583032478873605 2552511648859318589788801)
                    ·
                      refine ⟨1914383736644488942341601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2552511648859318589788801 1914383736644488942341601)
                      ·
                        rfl

theorem cell23_3728249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 4, 2].length) (baseStart_3728249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728249 prefixEnd_3728249 := by exact prefixLift 3728249
  have htrace : WordTrace (prefixWord ++ tailWord_3728249) baseStart_3728249 baseEnd_3728249 := by
    simpa [prefixWord, tailWord_3728249, baseEnd_3728249] using wordTrace_append hprefix tailTrace_3728249
  have hstable : (prefixWord ++ tailWord_3728249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728249).length < 2 ^ (prefixWord ++ tailWord_3728249).sum := by decide
  have hdescent : baseEnd_3728249 < baseStart_3728249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728315 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 4, 8]
def baseStart_3728315 : Nat := 118140960795 + 3728315 * 2 ^ 59
def prefixEnd_3728315 : Nat := 4983230072969 + 3 ^ 40 * 3728315 * 2
def baseEnd_3728315 : Nat := 638139208789228561372099

theorem tailTrace_3728315 : CollatzResearch.WordTrace tailWord_3728315 prefixEnd_3728315 638139208789228561372099 := by
  unfold tailWord_3728315
  simp only [CollatzResearch.WordTrace]
  refine ⟨135982819487958975353210399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90655212991972650235473599 135982819487958975353210399)
  ·
    refine ⟨203974229231938463029815599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135982819487958975353210399 203974229231938463029815599)
    ·
      refine ⟨305961343847907694544723399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203974229231938463029815599 305961343847907694544723399)
      ·
        refine ⟨458942015771861541817085099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305961343847907694544723399 458942015771861541817085099)
        ·
          refine ⟨688413023657792312725627649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458942015771861541817085099 688413023657792312725627649)
          ·
            refine ⟨516309767743344234544220737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 688413023657792312725627649 516309767743344234544220737)
            ·
              refine ⟨387232325807508175908165553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 516309767743344234544220737 387232325807508175908165553)
              ·
                refine ⟨290424244355631131931124165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387232325807508175908165553 290424244355631131931124165)
                ·
                  refine ⟨54454545816680837237085781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 290424244355631131931124165 54454545816680837237085781)
                  ·
                    refine ⟨638139208789228561372099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54454545816680837237085781 638139208789228561372099)
                    ·
                      rfl

theorem cell23_3728315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 8].length) (baseStart_3728315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728315 prefixEnd_3728315 := by exact prefixLift 3728315
  have htrace : WordTrace (prefixWord ++ tailWord_3728315) baseStart_3728315 baseEnd_3728315 := by
    simpa [prefixWord, tailWord_3728315, baseEnd_3728315] using wordTrace_append hprefix tailTrace_3728315
  have hstable : (prefixWord ++ tailWord_3728315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728315).length < 2 ^ (prefixWord ++ tailWord_3728315).sum := by decide
  have hdescent : baseEnd_3728315 < baseStart_3728315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728479 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 3, 3, 3]
def baseStart_3728479 : Nat := 118140960795 + 3728479 * 2 ^ 59
def prefixEnd_3728479 : Nat := 4983230072969 + 3 ^ 40 * 3728479 * 2
def baseEnd_3728479 : Nat := 1914501837195023042465543

theorem tailTrace_3728479 : CollatzResearch.WordTrace tailWord_3728479 prefixEnd_3728479 1914501837195023042465543 := by
  unfold tailWord_3728479
  simp only [CollatzResearch.WordTrace]
  refine ⟨135988801059364831362180491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90659200706243220908120327 135988801059364831362180491)
  ·
    refine ⟨203983201589047247043270737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135988801059364831362180491 203983201589047247043270737)
    ·
      refine ⟨152987401191785435282453053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203983201589047247043270737 152987401191785435282453053)
      ·
        refine ⟨57370275446919538230919895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152987401191785435282453053 57370275446919538230919895)
        ·
          refine ⟨86055413170379307346379843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57370275446919538230919895 86055413170379307346379843)
          ·
            refine ⟨129083119755568961019569765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86055413170379307346379843 129083119755568961019569765)
            ·
              refine ⟨24203084954169180191169331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129083119755568961019569765 24203084954169180191169331)
              ·
                refine ⟨36304627431253770286753997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24203084954169180191169331 36304627431253770286753997)
                ·
                  refine ⟨13614235286720163857532749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36304627431253770286753997 13614235286720163857532749)
                  ·
                    refine ⟨5105338232520061446574781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13614235286720163857532749 5105338232520061446574781)
                    ·
                      refine ⟨1914501837195023042465543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5105338232520061446574781 1914501837195023042465543)
                      ·
                        rfl

theorem cell23_3728479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_3728479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728479 prefixEnd_3728479 := by exact prefixLift 3728479
  have htrace : WordTrace (prefixWord ++ tailWord_3728479) baseStart_3728479 baseEnd_3728479 := by
    simpa [prefixWord, tailWord_3728479, baseEnd_3728479] using wordTrace_append hprefix tailTrace_3728479
  have hstable : (prefixWord ++ tailWord_3728479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728479).length < 2 ^ (prefixWord ++ tailWord_3728479).sum := by decide
  have hdescent : baseEnd_3728479 < baseStart_3728479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728496 : List Nat := [2, 1, 1, 1, 5, 1, 1, 3, 4, 1, 3]
def baseStart_3728496 : Nat := 118140960795 + 3728496 * 2 ^ 59
def prefixEnd_3728496 : Nat := 4983230072969 + 3 ^ 40 * 3728496 * 2
def baseEnd_3728496 : Nat := 1914510566366149475952965

theorem tailTrace_3728496 : CollatzResearch.WordTrace tailWord_3728496 prefixEnd_3728496 1914510566366149475952965 := by
  unfold tailWord_3728496
  simp only [CollatzResearch.WordTrace]
  refine ⟨67994710550151621632774671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90659614066868828843699561 67994710550151621632774671)
  ·
    refine ⟨101992065825227432449162007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67994710550151621632774671 101992065825227432449162007)
    ·
      refine ⟨152988098737841148673743011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101992065825227432449162007 152988098737841148673743011)
      ·
        refine ⟨229482148106761723010614517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152988098737841148673743011 229482148106761723010614517)
        ·
          refine ⟨21513951385008911532245111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 229482148106761723010614517 21513951385008911532245111)
          ·
            refine ⟨32270927077513367298367667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21513951385008911532245111 32270927077513367298367667)
            ·
              refine ⟨48406390616270050947551501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32270927077513367298367667 48406390616270050947551501)
              ·
                refine ⟨18152396481101269105331813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48406390616270050947551501 18152396481101269105331813)
                ·
                  refine ⟨3403574340206487957249715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18152396481101269105331813 3403574340206487957249715)
                  ·
                    refine ⟨5105361510309731935874573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3403574340206487957249715 5105361510309731935874573)
                    ·
                      refine ⟨1914510566366149475952965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5105361510309731935874573 1914510566366149475952965)
                      ·
                        rfl

theorem cell23_3728496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 4, 1, 3].length) (baseStart_3728496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728496 prefixEnd_3728496 := by exact prefixLift 3728496
  have htrace : WordTrace (prefixWord ++ tailWord_3728496) baseStart_3728496 baseEnd_3728496 := by
    simpa [prefixWord, tailWord_3728496, baseEnd_3728496] using wordTrace_append hprefix tailTrace_3728496
  have hstable : (prefixWord ++ tailWord_3728496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728496).length < 2 ^ (prefixWord ++ tailWord_3728496).sum := by decide
  have hdescent : baseEnd_3728496 < baseStart_3728496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728576 : List Nat := [2, 1, 1, 2, 6, 1, 1, 2, 7]
def baseStart_3728576 : Nat := 118140960795 + 3728576 * 2 ^ 59
def prefixEnd_3728576 : Nat := 4983230072969 + 3 ^ 40 * 3728576 * 2
def baseEnd_3728576 : Nat := 212727960535389906994733

theorem tailTrace_3728576 : CollatzResearch.WordTrace tailWord_3728576 prefixEnd_3728576 212727960535389906994733 := by
  unfold tailWord_3728576
  simp only [CollatzResearch.WordTrace]
  refine ⟨67996169470006708464230791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90661559293342277952307721 67996169470006708464230791)
  ·
    refine ⟨101994254205010062696346187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67996169470006708464230791 101994254205010062696346187)
    ·
      refine ⟨152991381307515094044519281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101994254205010062696346187 152991381307515094044519281)
      ·
        refine ⟨114743535980636320533389461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152991381307515094044519281 114743535980636320533389461)
        ·
          refine ⟨5378603249092327525002631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 114743535980636320533389461 5378603249092327525002631)
          ·
            refine ⟨8067904873638491287503947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5378603249092327525002631 8067904873638491287503947)
            ·
              refine ⟨12101857310457736931255921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8067904873638491287503947 12101857310457736931255921)
              ·
                refine ⟨9076392982843302698441941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12101857310457736931255921 9076392982843302698441941)
                ·
                  refine ⟨212727960535389906994733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9076392982843302698441941 212727960535389906994733)
                  ·
                    rfl

theorem cell23_3728576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 7].length) (baseStart_3728576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728576 prefixEnd_3728576 := by exact prefixLift 3728576
  have htrace : WordTrace (prefixWord ++ tailWord_3728576) baseStart_3728576 baseEnd_3728576 := by
    simpa [prefixWord, tailWord_3728576, baseEnd_3728576] using wordTrace_append hprefix tailTrace_3728576
  have hstable : (prefixWord ++ tailWord_3728576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728576).length < 2 ^ (prefixWord ++ tailWord_3728576).sum := by decide
  have hdescent : baseEnd_3728576 < baseStart_3728576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728599 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 5]
def baseStart_3728599 : Nat := 118140960795 + 3728599 * 2 ^ 59
def prefixEnd_3728599 : Nat := 4983230072969 + 3 ^ 40 * 3728599 * 2
def baseEnd_3728599 : Nat := 1914563454873562572964991

theorem tailTrace_3728599 : CollatzResearch.WordTrace tailWord_3728599 prefixEnd_3728599 1914563454873562572964991 := by
  unfold tailWord_3728599
  simp only [CollatzResearch.WordTrace]
  refine ⟨135993177818930091856548851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90662118545953394571032567 135993177818930091856548851)
  ·
    refine ⟨203989766728395137784823277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135993177818930091856548851 203989766728395137784823277)
    ·
      refine ⟨76496162523148176669308729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203989766728395137784823277 76496162523148176669308729)
      ·
        refine ⟨57372121892361132501981547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76496162523148176669308729 57372121892361132501981547)
        ·
          refine ⟨86058182838541698752972321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57372121892361132501981547 86058182838541698752972321)
          ·
            refine ⟨64543637128906274064729241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86058182838541698752972321 64543637128906274064729241)
            ·
              refine ⟨48407727846679705548546931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64543637128906274064729241 48407727846679705548546931)
              ·
                refine ⟨72611591770019558322820397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48407727846679705548546931 72611591770019558322820397)
                ·
                  refine ⟨27229346913757334371057649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72611591770019558322820397 27229346913757334371057649)
                  ·
                    refine ⟨20422010185318000778293237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27229346913757334371057649 20422010185318000778293237)
                    ·
                      refine ⟨1914563454873562572964991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20422010185318000778293237 1914563454873562572964991)
                      ·
                        rfl

theorem cell23_3728599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_3728599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728599 prefixEnd_3728599 := by exact prefixLift 3728599
  have htrace : WordTrace (prefixWord ++ tailWord_3728599) baseStart_3728599 baseEnd_3728599 := by
    simpa [prefixWord, tailWord_3728599, baseEnd_3728599] using wordTrace_append hprefix tailTrace_3728599
  have hstable : (prefixWord ++ tailWord_3728599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728599).length < 2 ^ (prefixWord ++ tailWord_3728599).sum := by decide
  have hdescent : baseEnd_3728599 < baseStart_3728599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728649 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 10]
def baseStart_3728649 : Nat := 118140960795 + 3728649 * 2 ^ 59
def prefixEnd_3728649 : Nat := 4983230072969 + 3 ^ 40 * 3728649 * 2
def baseEnd_3728649 : Nat := 212732125434031930815529

theorem tailTrace_3728649 : CollatzResearch.WordTrace tailWord_3728649 prefixEnd_3728649 212732125434031930815529 := by
  unfold tailWord_3728649
  simp only [CollatzResearch.WordTrace]
  refine ⟨135995001468748950395869001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90663334312499300263912667 135995001468748950395869001)
  ·
    refine ⟨101996251101561712796901751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135995001468748950395869001 101996251101561712796901751)
    ·
      refine ⟨152994376652342569195352627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101996251101561712796901751 152994376652342569195352627)
      ·
        refine ⟨229491564978513853793028941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152994376652342569195352627 229491564978513853793028941)
        ·
          refine ⟨86059336866942695172385853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229491564978513853793028941 86059336866942695172385853)
          ·
            refine ⟨32272251325103510689644695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86059336866942695172385853 32272251325103510689644695)
            ·
              refine ⟨48408376987655266034467043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32272251325103510689644695 48408376987655266034467043)
              ·
                refine ⟨72612565481482899051700565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48408376987655266034467043 72612565481482899051700565)
                ·
                  refine ⟨212732125434031930815529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 72612565481482899051700565 212732125434031930815529)
                  ·
                    rfl

theorem cell23_3728649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 10].length) (baseStart_3728649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728649 prefixEnd_3728649 := by exact prefixLift 3728649
  have htrace : WordTrace (prefixWord ++ tailWord_3728649) baseStart_3728649 baseEnd_3728649 := by
    simpa [prefixWord, tailWord_3728649, baseEnd_3728649] using wordTrace_append hprefix tailTrace_3728649
  have hstable : (prefixWord ++ tailWord_3728649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728649).length < 2 ^ (prefixWord ++ tailWord_3728649).sum := by decide
  have hdescent : baseEnd_3728649 < baseStart_3728649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728663 : List Nat := [1, 1, 3, 4, 1, 1, 3, 2, 2, 2, 3]
def baseStart_3728663 : Nat := 118140960795 + 3728663 * 2 ^ 59
def prefixEnd_3728663 : Nat := 4983230072969 + 3 ^ 40 * 3728663 * 2
def baseEnd_3728663 : Nat := 1914596317635450322564697

theorem tailTrace_3728663 : CollatzResearch.WordTrace tailWord_3728663 prefixEnd_3728663 1914596317635450322564697 := by
  unfold tailWord_3728663
  simp only [CollatzResearch.WordTrace]
  refine ⟨135995512090698230786878643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90663674727132153857919095 135995512090698230786878643)
  ·
    refine ⟨203993268136047346180317965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135995512090698230786878643 203993268136047346180317965)
    ·
      refine ⟨76497475551017754817619237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203993268136047346180317965 76497475551017754817619237)
      ·
        refine ⟨14343276665815829028303607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76497475551017754817619237 14343276665815829028303607)
        ·
          refine ⟨21514914998723743542455411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14343276665815829028303607 21514914998723743542455411)
          ·
            refine ⟨32272372498085615313683117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21514914998723743542455411 32272372498085615313683117)
            ·
              refine ⟨12102139686782105742631169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32272372498085615313683117 12102139686782105742631169)
              ·
                refine ⟨9076604765086579306973377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12102139686782105742631169 9076604765086579306973377)
                ·
                  refine ⟨6807453573814934480230033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9076604765086579306973377 6807453573814934480230033)
                  ·
                    refine ⟨5105590180361200860172525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6807453573814934480230033 5105590180361200860172525)
                    ·
                      refine ⟨1914596317635450322564697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5105590180361200860172525 1914596317635450322564697)
                      ·
                        rfl

theorem cell23_3728663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_3728663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728663 prefixEnd_3728663 := by exact prefixLift 3728663
  have htrace : WordTrace (prefixWord ++ tailWord_3728663) baseStart_3728663 baseEnd_3728663 := by
    simpa [prefixWord, tailWord_3728663, baseEnd_3728663] using wordTrace_append hprefix tailTrace_3728663
  have hstable : (prefixWord ++ tailWord_3728663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728663).length < 2 ^ (prefixWord ++ tailWord_3728663).sum := by decide
  have hdescent : baseEnd_3728663 < baseStart_3728663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728666 : List Nat := [3, 1, 1, 3, 3, 1, 2, 1, 8]
def baseStart_3728666 : Nat := 118140960795 + 3728666 * 2 ^ 59
def prefixEnd_3728666 : Nat := 4983230072969 + 3 ^ 40 * 3728666 * 2
def baseEnd_3728666 : Nat := 212733095341934867869687

theorem tailTrace_3728666 : CollatzResearch.WordTrace tailWord_3728666 prefixEnd_3728666 212733095341934867869687 := by
  unfold tailWord_3728666
  simp only [CollatzResearch.WordTrace]
  refine ⟨33998905377421840574809463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90663747673124908199491901 33998905377421840574809463)
  ·
    refine ⟨50998358066132760862214195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33998905377421840574809463 50998358066132760862214195)
    ·
      refine ⟨76497537099199141293321293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50998358066132760862214195 76497537099199141293321293)
      ·
        refine ⟨28686576412199677984995485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76497537099199141293321293 28686576412199677984995485)
        ·
          refine ⟨10757466154574879244373307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28686576412199677984995485 10757466154574879244373307)
          ·
            refine ⟨16136199231862318866559961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10757466154574879244373307 16136199231862318866559961)
            ·
              refine ⟨12102149423896739149919971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16136199231862318866559961 12102149423896739149919971)
              ·
                refine ⟨18153224135845108724879957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12102149423896739149919971 18153224135845108724879957)
                ·
                  refine ⟨212733095341934867869687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18153224135845108724879957 212733095341934867869687)
                  ·
                    rfl

theorem cell23_3728666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 8].length) (baseStart_3728666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728666 prefixEnd_3728666 := by exact prefixLift 3728666
  have htrace : WordTrace (prefixWord ++ tailWord_3728666) baseStart_3728666 baseEnd_3728666 := by
    simpa [prefixWord, tailWord_3728666, baseEnd_3728666] using wordTrace_append hprefix tailTrace_3728666
  have hstable : (prefixWord ++ tailWord_3728666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728666).length < 2 ^ (prefixWord ++ tailWord_3728666).sum := by decide
  have hdescent : baseEnd_3728666 < baseStart_3728666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728717 : List Nat := [1, 6, 1, 3, 1, 1, 2, 2, 6]
def baseStart_3728717 : Nat := 118140960795 + 3728717 * 2 ^ 59
def prefixEnd_3728717 : Nat := 4983230072969 + 3 ^ 40 * 3728717 * 2
def baseEnd_3728717 : Nat := 212736005065643679032161

theorem tailTrace_3728717 : CollatzResearch.WordTrace tailWord_3728717 prefixEnd_3728717 212736005065643679032161 := by
  unfold tailWord_3728717
  simp only [CollatzResearch.WordTrace]
  refine ⟨135997481632502598009344405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90664987755001732006229603 135997481632502598009344405)
  ·
    refine ⟨6374881951523559281688019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 135997481632502598009344405 6374881951523559281688019)
    ·
      refine ⟨9562322927285338922532029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6374881951523559281688019 9562322927285338922532029)
      ·
        refine ⟨3585871097732002095949511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9562322927285338922532029 3585871097732002095949511)
        ·
          refine ⟨5378806646598003143924267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3585871097732002095949511 5378806646598003143924267)
          ·
            refine ⟨8068209969897004715886401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5378806646598003143924267 8068209969897004715886401)
            ·
              refine ⟨6051157477422753536914801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8068209969897004715886401 6051157477422753536914801)
              ·
                refine ⟨4538368108067065152686101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6051157477422753536914801 4538368108067065152686101)
                ·
                  refine ⟨212736005065643679032161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4538368108067065152686101 212736005065643679032161)
                  ·
                    rfl

theorem cell23_3728717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_3728717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728717 prefixEnd_3728717 := by exact prefixLift 3728717
  have htrace : WordTrace (prefixWord ++ tailWord_3728717) baseStart_3728717 baseEnd_3728717 := by
    simpa [prefixWord, tailWord_3728717, baseEnd_3728717] using wordTrace_append hprefix tailTrace_3728717
  have hstable : (prefixWord ++ tailWord_3728717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728717).length < 2 ^ (prefixWord ++ tailWord_3728717).sum := by decide
  have hdescent : baseEnd_3728717 < baseStart_3728717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728727 : List Nat := [1, 1, 3, 2, 3, 3, 1, 4, 1, 1, 3]
def baseStart_3728727 : Nat := 118140960795 + 3728727 * 2 ^ 59
def prefixEnd_3728727 : Nat := 4983230072969 + 3 ^ 40 * 3728727 * 2
def baseEnd_3728727 : Nat := 1914629180397338072164403

theorem tailTrace_3728727 : CollatzResearch.WordTrace tailWord_3728727 prefixEnd_3728727 1914629180397338072164403 := by
  unfold tailWord_3728727
  simp only [CollatzResearch.WordTrace]
  refine ⟨135997846362466369717208435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90665230908310913144805623 135997846362466369717208435)
  ·
    refine ⟨203996769543699554575812653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135997846362466369717208435 203996769543699554575812653)
    ·
      refine ⟨76498788578887332965929745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203996769543699554575812653 76498788578887332965929745)
      ·
        refine ⟨57374091434165499724447309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76498788578887332965929745 57374091434165499724447309)
        ·
          refine ⟨21515284287812062396667741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57374091434165499724447309 21515284287812062396667741)
          ·
            refine ⟨8068231607929523398750403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21515284287812062396667741 8068231607929523398750403)
            ·
              refine ⟨12102347411894285098125605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8068231607929523398750403 12102347411894285098125605)
              ·
                refine ⟨2269190139730178455898551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12102347411894285098125605 2269190139730178455898551)
                ·
                  refine ⟨3403785209595267683847827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2269190139730178455898551 3403785209595267683847827)
                  ·
                    refine ⟨5105677814392901525771741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3403785209595267683847827 5105677814392901525771741)
                    ·
                      refine ⟨1914629180397338072164403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5105677814392901525771741 1914629180397338072164403)
                      ·
                        rfl

theorem cell23_3728727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4, 1, 1, 3].length) (baseStart_3728727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728727 prefixEnd_3728727 := by exact prefixLift 3728727
  have htrace : WordTrace (prefixWord ++ tailWord_3728727) baseStart_3728727 baseEnd_3728727 := by
    simpa [prefixWord, tailWord_3728727, baseEnd_3728727] using wordTrace_append hprefix tailTrace_3728727
  have hstable : (prefixWord ++ tailWord_3728727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728727).length < 2 ^ (prefixWord ++ tailWord_3728727).sum := by decide
  have hdescent : baseEnd_3728727 < baseStart_3728727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728753 : List Nat := [1, 2, 2, 2, 1, 2, 4, 1, 3, 2, 3]
def baseStart_3728753 : Nat := 118140960795 + 3728753 * 2 ^ 59
def prefixEnd_3728753 : Nat := 4983230072969 + 3 ^ 40 * 3728753 * 2
def baseEnd_3728753 : Nat := 1914642530894354970439283

theorem tailTrace_3728753 : CollatzResearch.WordTrace tailWord_3728753 prefixEnd_3728753 1914642530894354970439283 := by
  unfold tailWord_3728753
  simp only [CollatzResearch.WordTrace]
  refine ⟨135998794660372176157654913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90665863106914784105103275 135998794660372176157654913)
  ·
    refine ⟨101999095995279132118241185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135998794660372176157654913 101999095995279132118241185)
    ·
      refine ⟨76499321996459349088680889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101999095995279132118241185 76499321996459349088680889)
      ·
        refine ⟨57374491497344511816510667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76499321996459349088680889 57374491497344511816510667)
        ·
          refine ⟨86061737246016767724766001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57374491497344511816510667 86061737246016767724766001)
          ·
            refine ⟨64546302934512575793574501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86061737246016767724766001 64546302934512575793574501)
            ·
              refine ⟨12102431800221107961295219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64546302934512575793574501 12102431800221107961295219)
              ·
                refine ⟨18153647700331661941942829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12102431800221107961295219 18153647700331661941942829)
                ·
                  refine ⟨6807617887624373228228561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18153647700331661941942829 6807617887624373228228561)
                  ·
                    refine ⟨5105713415718279921171421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6807617887624373228228561 5105713415718279921171421)
                    ·
                      refine ⟨1914642530894354970439283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5105713415718279921171421 1914642530894354970439283)
                      ·
                        rfl

theorem cell23_3728753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_3728753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728753 prefixEnd_3728753 := by exact prefixLift 3728753
  have htrace : WordTrace (prefixWord ++ tailWord_3728753) baseStart_3728753 baseEnd_3728753 := by
    simpa [prefixWord, tailWord_3728753, baseEnd_3728753] using wordTrace_append hprefix tailTrace_3728753
  have hstable : (prefixWord ++ tailWord_3728753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728753).length < 2 ^ (prefixWord ++ tailWord_3728753).sum := by decide
  have hdescent : baseEnd_3728753 < baseStart_3728753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728777 : List Nat := [1, 2, 1, 1, 7, 2, 1, 2, 2, 4]
def baseStart_3728777 : Nat := 118140960795 + 3728777 * 2 ^ 59
def prefixEnd_3728777 : Nat := 4983230072969 + 3 ^ 40 * 3728777 * 2
def baseEnd_3728777 : Nat := 638218284810020958846391

theorem tailTrace_3728777 : CollatzResearch.WordTrace tailWord_3728777 prefixEnd_3728777 638218284810020958846391 := by
  unfold tailWord_3728777
  simp only [CollatzResearch.WordTrace]
  refine ⟨135999670012285228256528585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90666446674856818837685723 135999670012285228256528585)
  ·
    refine ⟨101999752509213921192396439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135999670012285228256528585 101999752509213921192396439)
    ·
      refine ⟨152999628763820881788594659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101999752509213921192396439 152999628763820881788594659)
      ·
        refine ⟨229499443145731322682891989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152999628763820881788594659 229499443145731322682891989)
        ·
          refine ⟨5378893198728077875380281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 229499443145731322682891989 5378893198728077875380281)
          ·
            refine ⟨4034169899046058406535211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5378893198728077875380281 4034169899046058406535211)
            ·
              refine ⟨6051254848569087609802817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4034169899046058406535211 6051254848569087609802817)
              ·
                refine ⟨4538441136426815707352113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6051254848569087609802817 4538441136426815707352113)
                ·
                  refine ⟨3403830852320111780514085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4538441136426815707352113 3403830852320111780514085)
                  ·
                    refine ⟨638218284810020958846391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3403830852320111780514085 638218284810020958846391)
                    ·
                      rfl

theorem cell23_3728777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2, 4].length) (baseStart_3728777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728777 prefixEnd_3728777 := by exact prefixLift 3728777
  have htrace : WordTrace (prefixWord ++ tailWord_3728777) baseStart_3728777 baseEnd_3728777 := by
    simpa [prefixWord, tailWord_3728777, baseEnd_3728777] using wordTrace_append hprefix tailTrace_3728777
  have hstable : (prefixWord ++ tailWord_3728777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728777).length < 2 ^ (prefixWord ++ tailWord_3728777).sum := by decide
  have hdescent : baseEnd_3728777 < baseStart_3728777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728816 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 4, 6]
def baseStart_3728816 : Nat := 118140960795 + 3728816 * 2 ^ 59
def prefixEnd_3728816 : Nat := 4983230072969 + 3 ^ 40 * 3728816 * 2
def baseEnd_3728816 : Nat := 638224960058529407983831

theorem tailTrace_3728816 : CollatzResearch.WordTrace tailWord_3728816 prefixEnd_3728816 638224960058529407983831 := by
  unfold tailWord_3728816
  simp only [CollatzResearch.WordTrace]
  refine ⟨68000546229571968958599151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90667394972762625278132201 68000546229571968958599151)
  ·
    refine ⟨102000819344357953437898727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68000546229571968958599151 102000819344357953437898727)
    ·
      refine ⟨153001229016536930156848091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102000819344357953437898727 153001229016536930156848091)
      ·
        refine ⟨229501843524805395235272137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153001229016536930156848091 229501843524805395235272137)
        ·
          refine ⟨172126382643604046426454103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229501843524805395235272137 172126382643604046426454103)
          ·
            refine ⟨258189573965406069639681155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172126382643604046426454103 258189573965406069639681155)
            ·
              refine ⟨387284360948109104459521733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258189573965406069639681155 387284360948109104459521733)
              ·
                refine ⟨72615817677770457086160325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 387284360948109104459521733 72615817677770457086160325)
                ·
                  refine ⟨13615465814581960703655061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72615817677770457086160325 13615465814581960703655061)
                  ·
                    refine ⟨638224960058529407983831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13615465814581960703655061 638224960058529407983831)
                    ·
                      rfl

theorem cell23_3728816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 4, 6].length) (baseStart_3728816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728816 prefixEnd_3728816 := by exact prefixLift 3728816
  have htrace : WordTrace (prefixWord ++ tailWord_3728816) baseStart_3728816 baseEnd_3728816 := by
    simpa [prefixWord, tailWord_3728816, baseEnd_3728816] using wordTrace_append hprefix tailTrace_3728816
  have hstable : (prefixWord ++ tailWord_3728816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728816).length < 2 ^ (prefixWord ++ tailWord_3728816).sum := by decide
  have hdescent : baseEnd_3728816 < baseStart_3728816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728853 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 1, 4, 4]
def baseStart_3728853 : Nat := 118140960795 + 3728853 * 2 ^ 59
def prefixEnd_3728853 : Nat := 4983230072969 + 3 ^ 40 * 3728853 * 2
def baseEnd_3728853 : Nat := 1914693878959804579188823

theorem tailTrace_3728853 : CollatzResearch.WordTrace tailWord_3728853 prefixEnd_3728853 1914693878959804579188823 := by
  unfold tailWord_3728853
  simp only [CollatzResearch.WordTrace]
  refine ⟨136002441960009893236295213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90668294640006595490863475 136002441960009893236295213)
  ·
    refine ⟨51000915735003709963610705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136002441960009893236295213 51000915735003709963610705)
    ·
      refine ⟨38250686801252782472708029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51000915735003709963610705 38250686801252782472708029)
      ·
        refine ⟨14344007550469793427265511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38250686801252782472708029 14344007550469793427265511)
        ·
          refine ⟨21516011325704690140898267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14344007550469793427265511 21516011325704690140898267)
          ·
            refine ⟨32274016988557035211347401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21516011325704690140898267 32274016988557035211347401)
            ·
              refine ⟨24205512741417776408510551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32274016988557035211347401 24205512741417776408510551)
              ·
                refine ⟨36308269112126664612765827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24205512741417776408510551 36308269112126664612765827)
                ·
                  refine ⟨54462403668189996919148741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36308269112126664612765827 54462403668189996919148741)
                  ·
                    refine ⟨10211700687785624422340389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54462403668189996919148741 10211700687785624422340389)
                    ·
                      refine ⟨1914693878959804579188823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10211700687785624422340389 1914693878959804579188823)
                      ·
                        rfl

theorem cell23_3728853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_3728853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728853 prefixEnd_3728853 := by exact prefixLift 3728853
  have htrace : WordTrace (prefixWord ++ tailWord_3728853) baseStart_3728853 baseEnd_3728853 := by
    simpa [prefixWord, tailWord_3728853, baseEnd_3728853] using wordTrace_append hprefix tailTrace_3728853
  have hstable : (prefixWord ++ tailWord_3728853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728853).length < 2 ^ (prefixWord ++ tailWord_3728853).sum := by decide
  have hdescent : baseEnd_3728853 < baseStart_3728853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728897 : List Nat := [1, 2, 4, 1, 4, 1, 1, 4, 5]
def baseStart_3728897 : Nat := 118140960795 + 3728897 * 2 ^ 59
def prefixEnd_3728897 : Nat := 4983230072969 + 3 ^ 40 * 3728897 * 2
def baseEnd_3728897 : Nat := 212746274678733600782069

theorem tailTrace_3728897 : CollatzResearch.WordTrace tailWord_3728897 prefixEnd_3728897 212746274678733600782069 := by
  unfold tailWord_3728897
  simp only [CollatzResearch.WordTrace]
  refine ⟨136004046771850488750896945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90669364514566992500597963 136004046771850488750896945)
  ·
    refine ⟨102003035078887866563172709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136004046771850488750896945 102003035078887866563172709)
    ·
      refine ⟨19125569077291474980594883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102003035078887866563172709 19125569077291474980594883)
      ·
        refine ⟨28688353615937212470892325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19125569077291474980594883 28688353615937212470892325)
        ·
          refine ⟨5379066302988227338292311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28688353615937212470892325 5379066302988227338292311)
          ·
            refine ⟨8068599454482341007438467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5379066302988227338292311 8068599454482341007438467)
            ·
              refine ⟨12102899181723511511157701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8068599454482341007438467 12102899181723511511157701)
              ·
                refine ⟨2269293596573158408342069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12102899181723511511157701 2269293596573158408342069)
                ·
                  refine ⟨212746274678733600782069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2269293596573158408342069 212746274678733600782069)
                  ·
                    rfl

theorem cell23_3728897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4, 5].length) (baseStart_3728897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728897 prefixEnd_3728897 := by exact prefixLift 3728897
  have htrace : WordTrace (prefixWord ++ tailWord_3728897) baseStart_3728897 baseEnd_3728897 := by
    simpa [prefixWord, tailWord_3728897, baseEnd_3728897] using wordTrace_append hprefix tailTrace_3728897
  have hstable : (prefixWord ++ tailWord_3728897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728897).length < 2 ^ (prefixWord ++ tailWord_3728897).sum := by decide
  have hdescent : baseEnd_3728897 < baseStart_3728897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728913 : List Nat := [1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 4]
def baseStart_3728913 : Nat := 118140960795 + 3728913 * 2 ^ 59
def prefixEnd_3728913 : Nat := 4983230072969 + 3 ^ 40 * 3728913 * 2
def baseEnd_3728913 : Nat := 1914724687799074344438547

theorem tailTrace_3728913 : CollatzResearch.WordTrace tailWord_3728913 prefixEnd_3728913 1914724687799074344438547 := by
  unfold tailWord_3728913
  simp only [CollatzResearch.WordTrace]
  refine ⟨136004630339792523483479393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90669753559861682322319595 136004630339792523483479393)
  ·
    refine ⟨102003472754844392612609545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136004630339792523483479393 102003472754844392612609545)
    ·
      refine ⟨76502604566133294459457159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102003472754844392612609545 76502604566133294459457159)
      ·
        refine ⟨114753906849199941689185739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76502604566133294459457159 114753906849199941689185739)
        ·
          refine ⟨172130860273799912533778609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114753906849199941689185739 172130860273799912533778609)
          ·
            refine ⟨129098145205349934400333957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172130860273799912533778609 129098145205349934400333957)
            ·
              refine ⟨24205902226003112700062617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129098145205349934400333957 24205902226003112700062617)
              ·
                refine ⟨18154426669502334525046963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24205902226003112700062617 18154426669502334525046963)
                ·
                  refine ⟨27231640004253501787570445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18154426669502334525046963 27231640004253501787570445)
                  ·
                    refine ⟨10211865001595063170338917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27231640004253501787570445 10211865001595063170338917)
                    ·
                      refine ⟨1914724687799074344438547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10211865001595063170338917 1914724687799074344438547)
                      ·
                        rfl

theorem cell23_3728913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_3728913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728913 prefixEnd_3728913 := by exact prefixLift 3728913
  have htrace : WordTrace (prefixWord ++ tailWord_3728913) baseStart_3728913 baseEnd_3728913 := by
    simpa [prefixWord, tailWord_3728913, baseEnd_3728913] using wordTrace_append hprefix tailTrace_3728913
  have hstable : (prefixWord ++ tailWord_3728913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728913).length < 2 ^ (prefixWord ++ tailWord_3728913).sum := by decide
  have hdescent : baseEnd_3728913 < baseStart_3728913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3728980 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 2, 5, 3]
def baseStart_3728980 : Nat := 118140960795 + 3728980 * 2 ^ 59
def prefixEnd_3728980 : Nat := 4983230072969 + 3 ^ 40 * 3728980 * 2
def baseEnd_3728980 : Nat := 1914759091002925582300739

theorem tailTrace_3728980 : CollatzResearch.WordTrace tailWord_3728980 prefixEnd_3728980 1914759091002925582300739 := by
  unfold tailWord_3728980
  simp only [CollatzResearch.WordTrace]
  refine ⟨68003537015274896963084197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90671382687033195950778929 68003537015274896963084197)
  ·
    refine ⟨12750663190364043180578287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68003537015274896963084197 12750663190364043180578287)
    ·
      refine ⟨19125994785546064770867431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12750663190364043180578287 19125994785546064770867431)
      ·
        refine ⟨28688992178319097156301147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19125994785546064770867431 28688992178319097156301147)
        ·
          refine ⟨43033488267478645734451721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28688992178319097156301147 43033488267478645734451721)
          ·
            refine ⟨32275116200608984300838791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43033488267478645734451721 32275116200608984300838791)
            ·
              refine ⟨48412674300913476451258187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32275116200608984300838791 48412674300913476451258187)
              ·
                refine ⟨72619011451370214676887281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48412674300913476451258187 72619011451370214676887281)
                ·
                  refine ⟨54464258588527661007665461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72619011451370214676887281 54464258588527661007665461)
                  ·
                    refine ⟨5106024242674468219468637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54464258588527661007665461 5106024242674468219468637)
                    ·
                      refine ⟨1914759091002925582300739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5106024242674468219468637 1914759091002925582300739)
                      ·
                        rfl

theorem cell23_3728980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_3728980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3728980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3728980 prefixEnd_3728980 := by exact prefixLift 3728980
  have htrace : WordTrace (prefixWord ++ tailWord_3728980) baseStart_3728980 baseEnd_3728980 := by
    simpa [prefixWord, tailWord_3728980, baseEnd_3728980] using wordTrace_append hprefix tailTrace_3728980
  have hstable : (prefixWord ++ tailWord_3728980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3728980).length < 2 ^ (prefixWord ++ tailWord_3728980).sum := by decide
  have hdescent : baseEnd_3728980 < baseStart_3728980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3728980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729003 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 4]
def baseStart_3729003 : Nat := 118140960795 + 3729003 * 2 ^ 59
def prefixEnd_3729003 : Nat := 4983230072969 + 3 ^ 40 * 3729003 * 2
def baseEnd_3729003 : Nat := 1914770901057978992313133

theorem tailTrace_3729003 : CollatzResearch.WordTrace tailWord_3729003 prefixEnd_3729003 1914770901057978992313133 := by
  unfold tailWord_3729003
  simp only [CollatzResearch.WordTrace]
  refine ⟨136007912909466468854255663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90671941939644312569503775 136007912909466468854255663)
  ·
    refine ⟨204011869364199703281383495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136007912909466468854255663 204011869364199703281383495)
    ·
      refine ⟨306017804046299554922075243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204011869364199703281383495 306017804046299554922075243)
      ·
        refine ⟨459026706069449332383112865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306017804046299554922075243 459026706069449332383112865)
        ·
          refine ⟨344270029552086999287334649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459026706069449332383112865 344270029552086999287334649)
          ·
            refine ⟨258202522164065249465500987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344270029552086999287334649 258202522164065249465500987)
            ·
              refine ⟨387303783246097874198251481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258202522164065249465500987 387303783246097874198251481)
              ·
                refine ⟨290477837434573405648688611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387303783246097874198251481 290477837434573405648688611)
                ·
                  refine ⟨435716756151860108473032917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 290477837434573405648688611 435716756151860108473032917)
                  ·
                    refine ⟨10212111472309221292336709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 435716756151860108473032917 10212111472309221292336709)
                    ·
                      refine ⟨1914770901057978992313133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10212111472309221292336709 1914770901057978992313133)
                      ·
                        rfl

theorem cell23_3729003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 4].length) (baseStart_3729003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729003 prefixEnd_3729003 := by exact prefixLift 3729003
  have htrace : WordTrace (prefixWord ++ tailWord_3729003) baseStart_3729003 baseEnd_3729003 := by
    simpa [prefixWord, tailWord_3729003, baseEnd_3729003] using wordTrace_append hprefix tailTrace_3729003
  have hstable : (prefixWord ++ tailWord_3729003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729003).length < 2 ^ (prefixWord ++ tailWord_3729003).sum := by decide
  have hdescent : baseEnd_3729003 < baseStart_3729003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729020 : List Nat := [2, 2, 2, 1, 1, 2, 1, 4, 3, 1, 4]
def baseStart_3729020 : Nat := 118140960795 + 3729020 * 2 ^ 59
def prefixEnd_3729020 : Nat := 4983230072969 + 3 ^ 40 * 3729020 * 2
def baseEnd_3729020 : Nat := 1914779630229105425800555

theorem tailTrace_3729020 : CollatzResearch.WordTrace tailWord_3729020 prefixEnd_3729020 1914779630229105425800555 := by
  unfold tailWord_3729020
  simp only [CollatzResearch.WordTrace]
  refine ⟨68004266475202440378812257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90672355300269920505083009 68004266475202440378812257)
  ·
    refine ⟨51003199856401830284109193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68004266475202440378812257 51003199856401830284109193)
    ·
      refine ⟨38252399892301372713081895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51003199856401830284109193 38252399892301372713081895)
      ·
        refine ⟨57378599838452059069622843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38252399892301372713081895 57378599838452059069622843)
        ·
          refine ⟨86067899757678088604434265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57378599838452059069622843 86067899757678088604434265)
          ·
            refine ⟨64550924818258566453325699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86067899757678088604434265 64550924818258566453325699)
            ·
              refine ⟨96826387227387849679988549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64550924818258566453325699 96826387227387849679988549)
              ·
                refine ⟨18154947605135221814997853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96826387227387849679988549 18154947605135221814997853)
                ·
                  refine ⟨6808105351925708180624195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18154947605135221814997853 6808105351925708180624195)
                  ·
                    refine ⟨10212158027888562270936293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6808105351925708180624195 10212158027888562270936293)
                    ·
                      refine ⟨1914779630229105425800555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10212158027888562270936293 1914779630229105425800555)
                      ·
                        rfl

theorem cell23_3729020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_3729020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729020 prefixEnd_3729020 := by exact prefixLift 3729020
  have htrace : WordTrace (prefixWord ++ tailWord_3729020) baseStart_3729020 baseEnd_3729020 := by
    simpa [prefixWord, tailWord_3729020, baseEnd_3729020] using wordTrace_append hprefix tailTrace_3729020
  have hstable : (prefixWord ++ tailWord_3729020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729020).length < 2 ^ (prefixWord ++ tailWord_3729020).sum := by decide
  have hdescent : baseEnd_3729020 < baseStart_3729020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729023 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 5]
def baseStart_3729023 : Nat := 118140960795 + 3729023 * 2 ^ 59
def prefixEnd_3729023 : Nat := 4983230072969 + 3 ^ 40 * 3729023 * 2
def baseEnd_3729023 : Nat := 1914781170671068914063041

theorem tailTrace_3729023 : CollatzResearch.WordTrace tailWord_3729023 prefixEnd_3729023 1914781170671068914063041 := by
  unfold tailWord_3729023
  simp only [CollatzResearch.WordTrace]
  refine ⟨136008642369394012269983723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90672428246262674846655815 136008642369394012269983723)
  ·
    refine ⟨204012963554091018404975585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136008642369394012269983723 204012963554091018404975585)
    ·
      refine ⟨153009722665568263803731689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204012963554091018404975585 153009722665568263803731689)
      ·
        refine ⟨114757291999176197852798767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153009722665568263803731689 114757291999176197852798767)
        ·
          refine ⟨172135937998764296779198151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114757291999176197852798767 172135937998764296779198151)
          ·
            refine ⟨258203906998146445168797227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172135937998764296779198151 258203906998146445168797227)
            ·
              refine ⟨387305860497219667753195841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258203906998146445168797227 387305860497219667753195841)
              ·
                refine ⟨290479395372914750814896881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387305860497219667753195841 290479395372914750814896881)
                ·
                  refine ⟨217859546529686063111172661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 290479395372914750814896881 217859546529686063111172661)
                  ·
                    refine ⟨20424332487158068416672437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 217859546529686063111172661 20424332487158068416672437)
                    ·
                      refine ⟨1914781170671068914063041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20424332487158068416672437 1914781170671068914063041)
                      ·
                        rfl

theorem cell23_3729023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_3729023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729023 prefixEnd_3729023 := by exact prefixLift 3729023
  have htrace : WordTrace (prefixWord ++ tailWord_3729023) baseStart_3729023 baseEnd_3729023 := by
    simpa [prefixWord, tailWord_3729023, baseEnd_3729023] using wordTrace_append hprefix tailTrace_3729023
  have hstable : (prefixWord ++ tailWord_3729023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729023).length < 2 ^ (prefixWord ++ tailWord_3729023).sum := by decide
  have hdescent : baseEnd_3729023 < baseStart_3729023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729034 : List Nat := [3, 1, 2, 3, 2, 3, 1, 2, 1, 5]
def baseStart_3729034 : Nat := 118140960795 + 3729034 * 2 ^ 59
def prefixEnd_3729034 : Nat := 4983230072969 + 3 ^ 40 * 3729034 * 2
def baseEnd_3729034 : Nat := 638262272986089457008497

theorem tailTrace_3729034 : CollatzResearch.WordTrace tailWord_3729034 prefixEnd_3729034 638262272986089457008497 := by
  unfold tailWord_3729034
  simp only [CollatzResearch.WordTrace]
  refine ⟨34002260893088540287158539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90672695714902774099089437 34002260893088540287158539)
  ·
    refine ⟨51003391339632810430737809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34002260893088540287158539 51003391339632810430737809)
    ·
      refine ⟨38252543504724607823053357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51003391339632810430737809 38252543504724607823053357)
      ·
        refine ⟨14344703814271727933645009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38252543504724607823053357 14344703814271727933645009)
        ·
          refine ⟨10758527860703795950233757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14344703814271727933645009 10758527860703795950233757)
          ·
            refine ⟨4034447947763923481337659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10758527860703795950233757 4034447947763923481337659)
            ·
              refine ⟨6051671921645885222006489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4034447947763923481337659 6051671921645885222006489)
              ·
                refine ⟨4538753941234413916504867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6051671921645885222006489 4538753941234413916504867)
                ·
                  refine ⟨6808130911851620874757301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4538753941234413916504867 6808130911851620874757301)
                  ·
                    refine ⟨638262272986089457008497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6808130911851620874757301 638262272986089457008497)
                    ·
                      rfl

theorem cell23_3729034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_3729034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729034 prefixEnd_3729034 := by exact prefixLift 3729034
  have htrace : WordTrace (prefixWord ++ tailWord_3729034) baseStart_3729034 baseEnd_3729034 := by
    simpa [prefixWord, tailWord_3729034, baseEnd_3729034] using wordTrace_append hprefix tailTrace_3729034
  have hstable : (prefixWord ++ tailWord_3729034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729034).length < 2 ^ (prefixWord ++ tailWord_3729034).sum := by decide
  have hdescent : baseEnd_3729034 < baseStart_3729034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729057 : List Nat := [1, 2, 3, 3, 2, 1, 3, 1, 1, 1, 5]
def baseStart_3729057 : Nat := 118140960795 + 3729057 * 2 ^ 59
def prefixEnd_3729057 : Nat := 4983230072969 + 3 ^ 40 * 3729057 * 2
def baseEnd_3729057 : Nat := 1914798629013321781037885

theorem tailTrace_3729057 : CollatzResearch.WordTrace tailWord_3729057 prefixEnd_3729057 1914798629013321781037885 := by
  unfold tailWord_3729057
  simp only [CollatzResearch.WordTrace]
  refine ⟨136009882451270836076721425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90673254967513890717814283 136009882451270836076721425)
  ·
    refine ⟨102007411838453127057541069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136009882451270836076721425 102007411838453127057541069)
    ·
      refine ⟨38252779439419922646577901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102007411838453127057541069 38252779439419922646577901)
      ·
        refine ⟨14344792289782470992466713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38252779439419922646577901 14344792289782470992466713)
        ·
          refine ⟨10758594217336853244350035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14344792289782470992466713 10758594217336853244350035)
          ·
            refine ⟨16137891326005279866525053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10758594217336853244350035 16137891326005279866525053)
            ·
              refine ⟨6051709247251979949946895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16137891326005279866525053 6051709247251979949946895)
              ·
                refine ⟨9077563870877969924920343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6051709247251979949946895 9077563870877969924920343)
                ·
                  refine ⟨13616345806316954887380515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9077563870877969924920343 13616345806316954887380515)
                  ·
                    refine ⟨20424518709475432331070773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13616345806316954887380515 20424518709475432331070773)
                    ·
                      refine ⟨1914798629013321781037885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20424518709475432331070773 1914798629013321781037885)
                      ·
                        rfl

theorem cell23_3729057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_3729057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729057 prefixEnd_3729057 := by exact prefixLift 3729057
  have htrace : WordTrace (prefixWord ++ tailWord_3729057) baseStart_3729057 baseEnd_3729057 := by
    simpa [prefixWord, tailWord_3729057, baseEnd_3729057] using wordTrace_append hprefix tailTrace_3729057
  have hstable : (prefixWord ++ tailWord_3729057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729057).length < 2 ^ (prefixWord ++ tailWord_3729057).sum := by decide
  have hdescent : baseEnd_3729057 < baseStart_3729057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729071 : List Nat := [1, 1, 2, 1, 2, 4, 3, 4, 1, 2, 2]
def baseStart_3729071 : Nat := 118140960795 + 3729071 * 2 ^ 59
def prefixEnd_3729071 : Nat := 4983230072969 + 3 ^ 40 * 3729071 * 2
def baseEnd_3729071 : Nat := 1914805817742484726262821

theorem tailTrace_3729071 : CollatzResearch.WordTrace tailWord_3729071 prefixEnd_3729071 1914805817742484726262821 := by
  unfold tailWord_3729071
  simp only [CollatzResearch.WordTrace]
  refine ⟨136010393073220116467731067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90673595382146744311820711 136010393073220116467731067)
  ·
    refine ⟨204015589609830174701596601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136010393073220116467731067 204015589609830174701596601)
    ·
      refine ⟨153011692207372631026197451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204015589609830174701596601 153011692207372631026197451)
      ·
        refine ⟨229517538311058946539296177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153011692207372631026197451 229517538311058946539296177)
        ·
          refine ⟨172138153733294209904472133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229517538311058946539296177 172138153733294209904472133)
          ·
            refine ⟨32275903824992664357088525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172138153733294209904472133 32275903824992664357088525)
            ·
              refine ⟨12103463934372249133908197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32275903824992664357088525 12103463934372249133908197)
              ·
                refine ⟨2269399487694796712607787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12103463934372249133908197 2269399487694796712607787)
                ·
                  refine ⟨3404099231542195068911681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2269399487694796712607787 3404099231542195068911681)
                  ·
                    refine ⟨2553074423656646301683761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3404099231542195068911681 2553074423656646301683761)
                    ·
                      refine ⟨1914805817742484726262821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2553074423656646301683761 1914805817742484726262821)
                      ·
                        rfl

theorem cell23_3729071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4, 1, 2, 2].length) (baseStart_3729071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729071 prefixEnd_3729071 := by exact prefixLift 3729071
  have htrace : WordTrace (prefixWord ++ tailWord_3729071) baseStart_3729071 baseEnd_3729071 := by
    simpa [prefixWord, tailWord_3729071, baseEnd_3729071] using wordTrace_append hprefix tailTrace_3729071
  have hstable : (prefixWord ++ tailWord_3729071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729071).length < 2 ^ (prefixWord ++ tailWord_3729071).sum := by decide
  have hdescent : baseEnd_3729071 < baseStart_3729071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729087 : List Nat := [1, 1, 2, 2, 2, 3, 4, 1, 1, 3, 3]
def baseStart_3729087 : Nat := 118140960795 + 3729087 * 2 ^ 59
def prefixEnd_3729087 : Nat := 4983230072969 + 3 ^ 40 * 3729087 * 2
def baseEnd_3729087 : Nat := 1914814033432956663662747

theorem tailTrace_3729087 : CollatzResearch.WordTrace tailWord_3729087 prefixEnd_3729087 1914814033432956663662747 := by
  unfold tailWord_3729087
  simp only [CollatzResearch.WordTrace]
  refine ⟨136010976641162151200313515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90673984427441434133542343 136010976641162151200313515)
  ·
    refine ⟨204016464961743226800470273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136010976641162151200313515 204016464961743226800470273)
    ·
      refine ⟨153012348721307420100352705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204016464961743226800470273 153012348721307420100352705)
      ·
        refine ⟨114759261540980565075264529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153012348721307420100352705 114759261540980565075264529)
        ·
          refine ⟨86069446155735423806448397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114759261540980565075264529 86069446155735423806448397)
          ·
            refine ⟨32276042308400783927418149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86069446155735423806448397 32276042308400783927418149)
            ·
              refine ⟨6051757932825146986390903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32276042308400783927418149 6051757932825146986390903)
              ·
                refine ⟨9077636899237720479586355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6051757932825146986390903 9077636899237720479586355)
                ·
                  refine ⟨13616455348856580719379533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9077636899237720479586355 13616455348856580719379533)
                  ·
                    refine ⟨5106170755821217769767325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13616455348856580719379533 5106170755821217769767325)
                    ·
                      refine ⟨1914814033432956663662747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5106170755821217769767325 1914814033432956663662747)
                      ·
                        rfl

theorem cell23_3729087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3, 3].length) (baseStart_3729087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729087 prefixEnd_3729087 := by exact prefixLift 3729087
  have htrace : WordTrace (prefixWord ++ tailWord_3729087) baseStart_3729087 baseEnd_3729087 := by
    simpa [prefixWord, tailWord_3729087, baseEnd_3729087] using wordTrace_append hprefix tailTrace_3729087
  have hstable : (prefixWord ++ tailWord_3729087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729087).length < 2 ^ (prefixWord ++ tailWord_3729087).sum := by decide
  have hdescent : baseEnd_3729087 < baseStart_3729087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729108 : List Nat := [2, 4, 1, 3, 1, 3, 2, 1, 1, 2, 3]
def baseStart_3729108 : Nat := 118140960795 + 3729108 * 2 ^ 59
def prefixEnd_3729108 : Nat := 4983230072969 + 3 ^ 40 * 3729108 * 2
def baseEnd_3729108 : Nat := 1914824816526701081500151

theorem tailTrace_3729108 : CollatzResearch.WordTrace tailWord_3729108 prefixEnd_3729108 1914824816526701081500151 := by
  unfold tailWord_3729108
  simp only [CollatzResearch.WordTrace]
  refine ⟨68005871287043035893413989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90674495049390714524551985 68005871287043035893413989)
  ·
    refine ⟨12751100866320569230015123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68005871287043035893413989 12751100866320569230015123)
    ·
      refine ⟨19126651299480853845022685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12751100866320569230015123 19126651299480853845022685)
      ·
        refine ⟨7172494237305320191883507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19126651299480853845022685 7172494237305320191883507)
        ·
          refine ⟨10758741355957980287825261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7172494237305320191883507 10758741355957980287825261)
          ·
            refine ⟨4034528008484242607934473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10758741355957980287825261 4034528008484242607934473)
            ·
              refine ⟨3025896006363181955950855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4034528008484242607934473 3025896006363181955950855)
              ·
                refine ⟨4538844009544772933926283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3025896006363181955950855 4538844009544772933926283)
                ·
                  refine ⟨6808266014317159400889425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4538844009544772933926283 6808266014317159400889425)
                  ·
                    refine ⟨5106199510737869550667069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6808266014317159400889425 5106199510737869550667069)
                    ·
                      refine ⟨1914824816526701081500151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5106199510737869550667069 1914824816526701081500151)
                      ·
                        rfl

theorem cell23_3729108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_3729108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729108 prefixEnd_3729108 := by exact prefixLift 3729108
  have htrace : WordTrace (prefixWord ++ tailWord_3729108) baseStart_3729108 baseEnd_3729108 := by
    simpa [prefixWord, tailWord_3729108, baseEnd_3729108] using wordTrace_append hprefix tailTrace_3729108
  have hstable : (prefixWord ++ tailWord_3729108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729108).length < 2 ^ (prefixWord ++ tailWord_3729108).sum := by decide
  have hdescent : baseEnd_3729108 < baseStart_3729108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729120 : List Nat := [2, 1, 1, 3, 1, 2, 3, 2, 2, 6]
def baseStart_3729120 : Nat := 118140960795 + 3729120 * 2 ^ 59
def prefixEnd_3729120 : Nat := 4983230072969 + 3 ^ 40 * 3729120 * 2
def baseEnd_3729120 : Nat := 638276992764851678183365

theorem tailTrace_3729120 : CollatzResearch.WordTrace tailWord_3729120 prefixEnd_3729120 638276992764851678183365 := by
  unfold tailWord_3729120
  simp only [CollatzResearch.WordTrace]
  refine ⟨68006090125021298918132407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90674786833361731890843209 68006090125021298918132407)
  ·
    refine ⟨102009135187531948377198611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68006090125021298918132407 102009135187531948377198611)
    ·
      refine ⟨153013702781297922565797917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102009135187531948377198611 153013702781297922565797917)
      ·
        refine ⟨57380138542986720962174219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153013702781297922565797917 57380138542986720962174219)
        ·
          refine ⟨86070207814480081443261329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57380138542986720962174219 86070207814480081443261329)
          ·
            refine ⟨64552655860860061082445997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86070207814480081443261329 64552655860860061082445997)
            ·
              refine ⟨24207245947822522905917249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64552655860860061082445997 24207245947822522905917249)
              ·
                refine ⟨18155434460866892179437937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24207245947822522905917249 18155434460866892179437937)
                ·
                  refine ⟨13616575845650169134578453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18155434460866892179437937 13616575845650169134578453)
                  ·
                    refine ⟨638276992764851678183365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13616575845650169134578453 638276992764851678183365)
                    ·
                      rfl

theorem cell23_3729120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 2, 6].length) (baseStart_3729120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729120 prefixEnd_3729120 := by exact prefixLift 3729120
  have htrace : WordTrace (prefixWord ++ tailWord_3729120) baseStart_3729120 baseEnd_3729120 := by
    simpa [prefixWord, tailWord_3729120, baseEnd_3729120] using wordTrace_append hprefix tailTrace_3729120
  have hstable : (prefixWord ++ tailWord_3729120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729120).length < 2 ^ (prefixWord ++ tailWord_3729120).sum := by decide
  have hdescent : baseEnd_3729120 < baseStart_3729120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729167 : List Nat := [1, 1, 2, 1, 1, 1, 4, 7, 5]
def baseStart_3729167 : Nat := 118140960795 + 3729167 * 2 ^ 59
def prefixEnd_3729167 : Nat := 4983230072969 + 3 ^ 40 * 3729167 * 2
def baseEnd_3729167 : Nat := 212761679098368483406931

theorem tailTrace_3729167 : CollatzResearch.WordTrace tailWord_3729167 prefixEnd_3729167 212761679098368483406931 := by
  unfold tailWord_3729167
  simp only [CollatzResearch.WordTrace]
  refine ⟨136013894480872324863225755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90675929653914883242150503 136013894480872324863225755)
  ·
    refine ⟨204020841721308487294838633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136013894480872324863225755 204020841721308487294838633)
    ·
      refine ⟨153015631290981365471128975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204020841721308487294838633 153015631290981365471128975)
      ·
        refine ⟨229523446936472048206693463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153015631290981365471128975 229523446936472048206693463)
        ·
          refine ⟨344285170404708072310040195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229523446936472048206693463 344285170404708072310040195)
          ·
            refine ⟨516427755607062108465060293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344285170404708072310040195 516427755607062108465060293)
            ·
              refine ⟨96830204176324145337198805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 516427755607062108465060293 96830204176324145337198805)
              ·
                refine ⟨2269457910382597156340597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 96830204176324145337198805 2269457910382597156340597)
                ·
                  refine ⟨212761679098368483406931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2269457910382597156340597 212761679098368483406931)
                  ·
                    rfl

theorem cell23_3729167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7, 5].length) (baseStart_3729167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729167 prefixEnd_3729167 := by exact prefixLift 3729167
  have htrace : WordTrace (prefixWord ++ tailWord_3729167) baseStart_3729167 baseEnd_3729167 := by
    simpa [prefixWord, tailWord_3729167, baseEnd_3729167] using wordTrace_append hprefix tailTrace_3729167
  have hstable : (prefixWord ++ tailWord_3729167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729167).length < 2 ^ (prefixWord ++ tailWord_3729167).sum := by decide
  have hdescent : baseEnd_3729167 < baseStart_3729167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729214 : List Nat := [4, 2, 1, 2, 2, 1, 1, 3, 2, 5]
def baseStart_3729214 : Nat := 118140960795 + 3729214 * 2 ^ 59
def prefixEnd_3729214 : Nat := 4983230072969 + 3 ^ 40 * 3729214 * 2
def baseEnd_3729214 : Nat := 638293081825359222258221

theorem tailTrace_3729214 : CollatzResearch.WordTrace tailWord_3729214 prefixEnd_3729214 638293081825359222258221 := by
  unfold tailWord_3729214
  simp only [CollatzResearch.WordTrace]
  refine ⟨17001951088962756486273337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90677072474468034593457797 17001951088962756486273337)
  ·
    refine ⟨12751463316722067364705003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17001951088962756486273337 12751463316722067364705003)
    ·
      refine ⟨19127194975083101047057505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12751463316722067364705003 19127194975083101047057505)
      ·
        refine ⟨14345396231312325785293129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19127194975083101047057505 14345396231312325785293129)
        ·
          refine ⟨10759047173484244338969847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14345396231312325785293129 10759047173484244338969847)
          ·
            refine ⟨16138570760226366508454771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10759047173484244338969847 16138570760226366508454771)
            ·
              refine ⟨24207856140339549762682157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16138570760226366508454771 24207856140339549762682157)
              ·
                refine ⟨9077946052627331161005809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24207856140339549762682157 9077946052627331161005809)
                ·
                  refine ⟨6808459539470498370754357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9077946052627331161005809 6808459539470498370754357)
                  ·
                    refine ⟨638293081825359222258221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6808459539470498370754357 638293081825359222258221)
                    ·
                      rfl

theorem cell23_3729214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_3729214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729214 prefixEnd_3729214 := by exact prefixLift 3729214
  have htrace : WordTrace (prefixWord ++ tailWord_3729214) baseStart_3729214 baseEnd_3729214 := by
    simpa [prefixWord, tailWord_3729214, baseEnd_3729214] using wordTrace_append hprefix tailTrace_3729214
  have hstable : (prefixWord ++ tailWord_3729214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729214).length < 2 ^ (prefixWord ++ tailWord_3729214).sum := by decide
  have hdescent : baseEnd_3729214 < baseStart_3729214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729234 : List Nat := [3, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_3729234 : Nat := 118140960795 + 3729234 * 2 ^ 59
def prefixEnd_3729234 : Nat := 4983230072969 + 3 ^ 40 * 3729234 * 2
def baseEnd_3729234 : Nat := 1914889515089167588524571

theorem tailTrace_3729234 : CollatzResearch.WordTrace tailWord_3729234 prefixEnd_3729234 1914889515089167588524571 := by
  unfold tailWord_3729234
  simp only [CollatzResearch.WordTrace]
  refine ⟨34004084542907398826478689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90677558781086396870609837 34004084542907398826478689)
  ·
    refine ⟨25503063407180549119859017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34004084542907398826478689 25503063407180549119859017)
    ·
      refine ⟨19127297555385411839894263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25503063407180549119859017 19127297555385411839894263)
      ·
        refine ⟨28690946333078117759841395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19127297555385411839894263 28690946333078117759841395)
        ·
          refine ⟨43036419499617176639762093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28690946333078117759841395 43036419499617176639762093)
          ·
            refine ⟨16138657312356441239910785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43036419499617176639762093 16138657312356441239910785)
            ·
              refine ⟨12103992984267330929933089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16138657312356441239910785 12103992984267330929933089)
              ·
                refine ⟨9077994738200498197449817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12103992984267330929933089 9077994738200498197449817)
                ·
                  refine ⟨6808496053650373648087363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9077994738200498197449817 6808496053650373648087363)
                  ·
                    refine ⟨10212744080475560472131045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6808496053650373648087363 10212744080475560472131045)
                    ·
                      refine ⟨1914889515089167588524571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10212744080475560472131045 1914889515089167588524571)
                      ·
                        rfl

theorem cell23_3729234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_3729234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729234 prefixEnd_3729234 := by exact prefixLift 3729234
  have htrace : WordTrace (prefixWord ++ tailWord_3729234) baseStart_3729234 baseEnd_3729234 := by
    simpa [prefixWord, tailWord_3729234, baseEnd_3729234] using wordTrace_append hprefix tailTrace_3729234
  have hstable : (prefixWord ++ tailWord_3729234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729234).length < 2 ^ (prefixWord ++ tailWord_3729234).sum := by decide
  have hdescent : baseEnd_3729234 < baseStart_3729234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729251 : List Nat := [1, 1, 1, 5, 4, 1, 1, 1, 2, 4, 2]
def baseStart_3729251 : Nat := 118140960795 + 3729251 * 2 ^ 59
def prefixEnd_3729251 : Nat := 4983230072969 + 3 ^ 40 * 3729251 * 2
def baseEnd_3729251 : Nat := 1914898244260294022011993

theorem tailTrace_3729251 : CollatzResearch.WordTrace tailWord_3729251 prefixEnd_3729251 1914898244260294022011993 := by
  unfold tailWord_3729251
  simp only [CollatzResearch.WordTrace]
  refine ⟨136016958212568007209283607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90677972141712004806189071 136016958212568007209283607)
  ·
    refine ⟨204025437318852010813925411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136016958212568007209283607 204025437318852010813925411)
    ·
      refine ⟨306038155978278016220888117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204025437318852010813925411 306038155978278016220888117)
      ·
        refine ⟨28691077122963564020708261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 306038155978278016220888117 28691077122963564020708261)
        ·
          refine ⟨5379576960555668253882799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28691077122963564020708261 5379576960555668253882799)
          ·
            refine ⟨8069365440833502380824199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5379576960555668253882799 8069365440833502380824199)
            ·
              refine ⟨12104048161250253571236299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8069365440833502380824199 12104048161250253571236299)
              ·
                refine ⟨18156072241875380356854449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12104048161250253571236299 18156072241875380356854449)
                ·
                  refine ⟨13617054181406535267640837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18156072241875380356854449 13617054181406535267640837)
                  ·
                    refine ⟨2553197659013725362682657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13617054181406535267640837 2553197659013725362682657)
                    ·
                      refine ⟨1914898244260294022011993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2553197659013725362682657 1914898244260294022011993)
                      ·
                        rfl

theorem cell23_3729251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_3729251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729251 prefixEnd_3729251 := by exact prefixLift 3729251
  have htrace : WordTrace (prefixWord ++ tailWord_3729251) baseStart_3729251 baseEnd_3729251 := by
    simpa [prefixWord, tailWord_3729251, baseEnd_3729251] using wordTrace_append hprefix tailTrace_3729251
  have hstable : (prefixWord ++ tailWord_3729251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729251).length < 2 ^ (prefixWord ++ tailWord_3729251).sum := by decide
  have hdescent : baseEnd_3729251 < baseStart_3729251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729301 : List Nat := [1, 3, 2, 1, 1, 3, 4, 1, 3, 1, 3]
def baseStart_3729301 : Nat := 118140960795 + 3729301 * 2 ^ 59
def prefixEnd_3729301 : Nat := 4983230072969 + 3 ^ 40 * 3729301 * 2
def baseEnd_3729301 : Nat := 1914923918293018826386763

theorem tailTrace_3729301 : CollatzResearch.WordTrace tailWord_3729301 prefixEnd_3729301 1914923918293018826386763 := by
  unfold tailWord_3729301
  simp only [CollatzResearch.WordTrace]
  refine ⟨136018781862386865748603757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90679187908257910499069171 136018781862386865748603757)
  ·
    refine ⟨51007043198395074655726409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136018781862386865748603757 51007043198395074655726409)
    ·
      refine ⟨38255282398796305991794807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51007043198395074655726409 38255282398796305991794807)
      ·
        refine ⟨57382923598194458987692211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38255282398796305991794807 57382923598194458987692211)
        ·
          refine ⟨86074385397291688481538317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57382923598194458987692211 86074385397291688481538317)
          ·
            refine ⟨32277894523984383180576869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86074385397291688481538317 32277894523984383180576869)
            ·
              refine ⟨6052105223247071846358163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32277894523984383180576869 6052105223247071846358163)
              ·
                refine ⟨9078157834870607769537245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6052105223247071846358163 9078157834870607769537245)
                ·
                  refine ⟨3404309188076477913576467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9078157834870607769537245 3404309188076477913576467)
                  ·
                    refine ⟨5106463782114716870364701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3404309188076477913576467 5106463782114716870364701)
                    ·
                      refine ⟨1914923918293018826386763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5106463782114716870364701 1914923918293018826386763)
                      ·
                        rfl

theorem cell23_3729301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_3729301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729301 prefixEnd_3729301 := by exact prefixLift 3729301
  have htrace : WordTrace (prefixWord ++ tailWord_3729301) baseStart_3729301 baseEnd_3729301 := by
    simpa [prefixWord, tailWord_3729301, baseEnd_3729301] using wordTrace_append hprefix tailTrace_3729301
  have hstable : (prefixWord ++ tailWord_3729301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729301).length < 2 ^ (prefixWord ++ tailWord_3729301).sum := by decide
  have hdescent : baseEnd_3729301 < baseStart_3729301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729327 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 5]
def baseStart_3729327 : Nat := 118140960795 + 3729327 * 2 ^ 59
def prefixEnd_3729327 : Nat := 4983230072969 + 3 ^ 40 * 3729327 * 2
def baseEnd_3729327 : Nat := 1914937268790035724661643

theorem tailTrace_3729327 : CollatzResearch.WordTrace tailWord_3729327 prefixEnd_3729327 1914937268790035724661643 := by
  unfold tailWord_3729327
  simp only [CollatzResearch.WordTrace]
  refine ⟨136019730160292672189050235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90679820106861781459366823 136019730160292672189050235)
  ·
    refine ⟨204029595240439008283575353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136019730160292672189050235 204029595240439008283575353)
    ·
      refine ⟨153022196430329256212681515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204029595240439008283575353 153022196430329256212681515)
      ·
        refine ⟨229533294645493884319022273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153022196430329256212681515 229533294645493884319022273)
        ·
          refine ⟨172149970984120413239266705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229533294645493884319022273 172149970984120413239266705)
          ·
            refine ⟨129112478238090309929450029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172149970984120413239266705 129112478238090309929450029)
            ·
              refine ⟨48417179339283866223543761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129112478238090309929450029 48417179339283866223543761)
              ·
                refine ⟨36312884504462899667657821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48417179339283866223543761 36312884504462899667657821)
                ·
                  refine ⟨13617331689173587375371683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36312884504462899667657821 13617331689173587375371683)
                  ·
                    refine ⟨20425997533760381063057525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13617331689173587375371683 20425997533760381063057525)
                    ·
                      refine ⟨1914937268790035724661643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20425997533760381063057525 1914937268790035724661643)
                      ·
                        rfl

theorem cell23_3729327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 5].length) (baseStart_3729327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729327 prefixEnd_3729327 := by exact prefixLift 3729327
  have htrace : WordTrace (prefixWord ++ tailWord_3729327) baseStart_3729327 baseEnd_3729327 := by
    simpa [prefixWord, tailWord_3729327, baseEnd_3729327] using wordTrace_append hprefix tailTrace_3729327
  have hstable : (prefixWord ++ tailWord_3729327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729327).length < 2 ^ (prefixWord ++ tailWord_3729327).sum := by decide
  have hdescent : baseEnd_3729327 < baseStart_3729327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729341 : List Nat := [1, 4, 1, 2, 3, 1, 2, 3, 1, 1, 4]
def baseStart_3729341 : Nat := 118140960795 + 3729341 * 2 ^ 59
def prefixEnd_3729341 : Nat := 4983230072969 + 3 ^ 40 * 3729341 * 2
def baseEnd_3729341 : Nat := 1914944457519198669886579

theorem tailTrace_3729341 : CollatzResearch.WordTrace tailWord_3729341 prefixEnd_3729341 1914944457519198669886579 := by
  unfold tailWord_3729341
  simp only [CollatzResearch.WordTrace]
  refine ⟨136020240782241952580059877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90680160521494635053373251 136020240782241952580059877)
  ·
    refine ⟨25503795146670366108761227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136020240782241952580059877 25503795146670366108761227)
    ·
      refine ⟨38255692720005549163141841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25503795146670366108761227 38255692720005549163141841)
      ·
        refine ⟨28691769540004161872356381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38255692720005549163141841 28691769540004161872356381)
        ·
          refine ⟨10759413577501560702133643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28691769540004161872356381 10759413577501560702133643)
          ·
            refine ⟨16139120366252341053200465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10759413577501560702133643 16139120366252341053200465)
            ·
              refine ⟨12104340274689255789900349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16139120366252341053200465 12104340274689255789900349)
              ·
                refine ⟨4539127603008470921212631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12104340274689255789900349 4539127603008470921212631)
                ·
                  refine ⟨6808691404512706381818947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4539127603008470921212631 6808691404512706381818947)
                  ·
                    refine ⟨10213037106769059572728421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6808691404512706381818947 10213037106769059572728421)
                    ·
                      refine ⟨1914944457519198669886579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10213037106769059572728421 1914944457519198669886579)
                      ·
                        rfl

theorem cell23_3729341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_3729341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729341 prefixEnd_3729341 := by exact prefixLift 3729341
  have htrace : WordTrace (prefixWord ++ tailWord_3729341) baseStart_3729341 baseEnd_3729341 := by
    simpa [prefixWord, tailWord_3729341, baseEnd_3729341] using wordTrace_append hprefix tailTrace_3729341
  have hstable : (prefixWord ++ tailWord_3729341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729341).length < 2 ^ (prefixWord ++ tailWord_3729341).sum := by decide
  have hdescent : baseEnd_3729341 < baseStart_3729341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729344 : List Nat := [2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 5]
def baseStart_3729344 : Nat := 118140960795 + 3729344 * 2 ^ 59
def prefixEnd_3729344 : Nat := 4983230072969 + 3 ^ 40 * 3729344 * 2
def baseEnd_3729344 : Nat := 1914945997961162158149065

theorem tailTrace_3729344 : CollatzResearch.WordTrace tailWord_3729344 prefixEnd_3729344 1914945997961162158149065 := by
  unfold tailWord_3729344
  simp only [CollatzResearch.WordTrace]
  refine ⟨68010175100615542046209543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90680233467487389394946057 68010175100615542046209543)
  ·
    refine ⟨102015262650923313069314315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68010175100615542046209543 102015262650923313069314315)
    ·
      refine ⟨153022893976384969603971473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102015262650923313069314315 153022893976384969603971473)
      ·
        refine ⟨114767170482288727202978605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153022893976384969603971473 114767170482288727202978605)
        ·
          refine ⟨43037688930858272701116977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114767170482288727202978605 43037688930858272701116977)
          ·
            refine ⟨32278266698143704525837733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43037688930858272701116977 32278266698143704525837733)
            ·
              refine ⟨6052175005901944598594575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32278266698143704525837733 6052175005901944598594575)
              ·
                refine ⟨9078262508852916897891863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6052175005901944598594575 9078262508852916897891863)
                ·
                  refine ⟨13617393763279375346837795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9078262508852916897891863 13617393763279375346837795)
                  ·
                    refine ⟨20426090644919063020256693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13617393763279375346837795 20426090644919063020256693)
                    ·
                      refine ⟨1914945997961162158149065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20426090644919063020256693 1914945997961162158149065)
                      ·
                        rfl

theorem cell23_3729344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 5].length) (baseStart_3729344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729344 prefixEnd_3729344 := by exact prefixLift 3729344
  have htrace : WordTrace (prefixWord ++ tailWord_3729344) baseStart_3729344 baseEnd_3729344 := by
    simpa [prefixWord, tailWord_3729344, baseEnd_3729344] using wordTrace_append hprefix tailTrace_3729344
  have hstable : (prefixWord ++ tailWord_3729344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729344).length < 2 ^ (prefixWord ++ tailWord_3729344).sum := by decide
  have hdescent : baseEnd_3729344 < baseStart_3729344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729364 : List Nat := [2, 4, 1, 2, 1, 1, 4, 8]
def baseStart_3729364 : Nat := 118140960795 + 3729364 * 2 ^ 59
def prefixEnd_3729364 : Nat := 4983230072969 + 3 ^ 40 * 3729364 * 2
def baseEnd_3729364 : Nat := 70924306206453780736999

theorem tailTrace_3729364 : CollatzResearch.WordTrace tailWord_3729364 prefixEnd_3729364 70924306206453780736999 := by
  unfold tailWord_3729364
  simp only [CollatzResearch.WordTrace]
  refine ⟨68010539830579313754073573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90680719774105751672098097 68010539830579313754073573)
  ·
    refine ⟨12751976218233621328888795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68010539830579313754073573 12751976218233621328888795)
    ·
      refine ⟨19127964327350431993333193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12751976218233621328888795 19127964327350431993333193)
      ·
        refine ⟨14345973245512823994999895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19127964327350431993333193 14345973245512823994999895)
        ·
          refine ⟨21518959868269235992499843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14345973245512823994999895 21518959868269235992499843)
          ·
            refine ⟨32278439802403853988749765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21518959868269235992499843 32278439802403853988749765)
            ·
              refine ⟨6052207462950722622890581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32278439802403853988749765 6052207462950722622890581)
              ·
                refine ⟨70924306206453780736999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6052207462950722622890581 70924306206453780736999)
                ·
                  rfl

theorem cell23_3729364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 8].length) (baseStart_3729364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729364 prefixEnd_3729364 := by exact prefixLift 3729364
  have htrace : WordTrace (prefixWord ++ tailWord_3729364) baseStart_3729364 baseEnd_3729364 := by
    simpa [prefixWord, tailWord_3729364, baseEnd_3729364] using wordTrace_append hprefix tailTrace_3729364
  have hstable : (prefixWord ++ tailWord_3729364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729364).length < 2 ^ (prefixWord ++ tailWord_3729364).sum := by decide
  have hdescent : baseEnd_3729364 < baseStart_3729364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729367 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 6]
def baseStart_3729367 : Nat := 118140960795 + 3729367 * 2 ^ 59
def prefixEnd_3729367 : Nat := 4983230072969 + 3 ^ 40 * 3729367 * 2
def baseEnd_3729367 : Nat := 1914957808016215568161459

theorem tailTrace_3729367 : CollatzResearch.WordTrace tailWord_3729367 prefixEnd_3729367 1914957808016215568161459 := by
  unfold tailWord_3729367
  simp only [CollatzResearch.WordTrace]
  refine ⟨136021189080147759020506355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90680792720098506013670903 136021189080147759020506355)
  ·
    refine ⟨204031783620221638530759533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136021189080147759020506355 204031783620221638530759533)
    ·
      refine ⟨76511918857583114449034825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204031783620221638530759533 76511918857583114449034825)
      ·
        refine ⟨57383939143187335836776119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76511918857583114449034825 57383939143187335836776119)
        ·
          refine ⟨86075908714781003755164179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57383939143187335836776119 86075908714781003755164179)
          ·
            refine ⟨129113863072171505632746269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86075908714781003755164179 129113863072171505632746269)
            ·
              refine ⟨48417698652064314612279851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129113863072171505632746269 48417698652064314612279851)
              ·
                refine ⟨72626547978096471918419777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48417698652064314612279851 72626547978096471918419777)
                ·
                  refine ⟨54469910983572353938814833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72626547978096471918419777 54469910983572353938814833)
                  ·
                    refine ⟨40852433237679265454111125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54469910983572353938814833 40852433237679265454111125)
                    ·
                      refine ⟨1914957808016215568161459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40852433237679265454111125 1914957808016215568161459)
                      ·
                        rfl

theorem cell23_3729367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_3729367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729367 prefixEnd_3729367 := by exact prefixLift 3729367
  have htrace : WordTrace (prefixWord ++ tailWord_3729367) baseStart_3729367 baseEnd_3729367 := by
    simpa [prefixWord, tailWord_3729367, baseEnd_3729367] using wordTrace_append hprefix tailTrace_3729367
  have hstable : (prefixWord ++ tailWord_3729367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729367).length < 2 ^ (prefixWord ++ tailWord_3729367).sum := by decide
  have hdescent : baseEnd_3729367 < baseStart_3729367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729372 : List Nat := [2, 2, 6, 1, 1, 2, 1, 2, 1, 5]
def baseStart_3729372 : Nat := 118140960795 + 3729372 * 2 ^ 59
def prefixEnd_3729372 : Nat := 4983230072969 + 3 ^ 40 * 3729372 * 2
def baseEnd_3729372 : Nat := 638320125139829349532979

theorem tailTrace_3729372 : CollatzResearch.WordTrace tailWord_3729372 prefixEnd_3729372 638320125139829349532979 := by
  unfold tailWord_3729372
  simp only [CollatzResearch.WordTrace]
  refine ⟨68010685722564822437219185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90680914296753096582958913 68010685722564822437219185)
  ·
    refine ⟨51008014291923616827914389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68010685722564822437219185 51008014291923616827914389)
    ·
      refine ⟨2391000669933919538808487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51008014291923616827914389 2391000669933919538808487)
      ·
        refine ⟨3586501004900879308212731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2391000669933919538808487 3586501004900879308212731)
        ·
          refine ⟨5379751507351318962319097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3586501004900879308212731 5379751507351318962319097)
          ·
            refine ⟨4034813630513489221739323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5379751507351318962319097 4034813630513489221739323)
            ·
              refine ⟨6052220445770233832608985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4034813630513489221739323 6052220445770233832608985)
              ·
                refine ⟨4539165334327675374456739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6052220445770233832608985 4539165334327675374456739)
                ·
                  refine ⟨6808748001491513061685109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4539165334327675374456739 6808748001491513061685109)
                  ·
                    refine ⟨638320125139829349532979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6808748001491513061685109 638320125139829349532979)
                    ·
                      rfl

theorem cell23_3729372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_3729372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729372 prefixEnd_3729372 := by exact prefixLift 3729372
  have htrace : WordTrace (prefixWord ++ tailWord_3729372) baseStart_3729372 baseEnd_3729372 := by
    simpa [prefixWord, tailWord_3729372, baseEnd_3729372] using wordTrace_append hprefix tailTrace_3729372
  have hstable : (prefixWord ++ tailWord_3729372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729372).length < 2 ^ (prefixWord ++ tailWord_3729372).sum := by decide
  have hdescent : baseEnd_3729372 < baseStart_3729372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729387 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 5]
def baseStart_3729387 : Nat := 118140960795 + 3729387 * 2 ^ 59
def prefixEnd_3729387 : Nat := 4983230072969 + 3 ^ 40 * 3729387 * 2
def baseEnd_3729387 : Nat := 1914968077629305489911367

theorem tailTrace_3729387 : CollatzResearch.WordTrace tailWord_3729387 prefixEnd_3729387 1914968077629305489911367 := by
  unfold tailWord_3729387
  simp only [CollatzResearch.WordTrace]
  refine ⟨136021918540075302436234415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90681279026716868290822943 136021918540075302436234415)
  ·
    refine ⟨204032877810112953654351623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136021918540075302436234415 204032877810112953654351623)
    ·
      refine ⟨306049316715169430481527435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204032877810112953654351623 306049316715169430481527435)
      ·
        refine ⟨459073975072754145722291153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306049316715169430481527435 459073975072754145722291153)
        ·
          refine ⟨344305481304565609291718365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459073975072754145722291153 344305481304565609291718365)
          ·
            refine ⟨129114555489212103484394387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344305481304565609291718365 129114555489212103484394387)
            ·
              refine ⟨193671833233818155226591581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129114555489212103484394387 193671833233818155226591581)
              ·
                refine ⟨72626937462681808209971843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193671833233818155226591581 72626937462681808209971843)
                ·
                  refine ⟨108940406194022712314957765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72626937462681808209971843 108940406194022712314957765)
                  ·
                    refine ⟨20426326161379258559054581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108940406194022712314957765 20426326161379258559054581)
                    ·
                      refine ⟨1914968077629305489911367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20426326161379258559054581 1914968077629305489911367)
                      ·
                        rfl

theorem cell23_3729387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 5].length) (baseStart_3729387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729387 prefixEnd_3729387 := by exact prefixLift 3729387
  have htrace : WordTrace (prefixWord ++ tailWord_3729387) baseStart_3729387 baseEnd_3729387 := by
    simpa [prefixWord, tailWord_3729387, baseEnd_3729387] using wordTrace_append hprefix tailTrace_3729387
  have hstable : (prefixWord ++ tailWord_3729387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729387).length < 2 ^ (prefixWord ++ tailWord_3729387).sum := by decide
  have hdescent : baseEnd_3729387 < baseStart_3729387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729407 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 3, 8]
def baseStart_3729407 : Nat := 118140960795 + 3729407 * 2 ^ 59
def prefixEnd_3729407 : Nat := 4983230072969 + 3 ^ 40 * 3729407 * 2
def baseEnd_3729407 : Nat := 638326115747465137220425

theorem tailTrace_3729407 : CollatzResearch.WordTrace tailWord_3729407 prefixEnd_3729407 638326115747465137220425 := by
  unfold tailWord_3729407
  simp only [CollatzResearch.WordTrace]
  refine ⟨136022648000002845851962475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90681765333335230567974983 136022648000002845851962475)
  ·
    refine ⟨204033972000004268777943713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136022648000002845851962475 204033972000004268777943713)
    ·
      refine ⟨153025479000003201583457785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204033972000004268777943713 153025479000003201583457785)
      ·
        refine ⟨114769109250002401187593339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153025479000003201583457785 114769109250002401187593339)
        ·
          refine ⟨172153663875003601781390009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114769109250002401187593339 172153663875003601781390009)
          ·
            refine ⟨129115247906252701336042507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172153663875003601781390009 129115247906252701336042507)
            ·
              refine ⟨193672871859379052004063761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129115247906252701336042507 193672871859379052004063761)
              ·
                refine ⟨145254653894534289003047821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193672871859379052004063761 145254653894534289003047821)
                ·
                  refine ⟨54470495210450358376142933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145254653894534289003047821 54470495210450358376142933)
                  ·
                    refine ⟨638326115747465137220425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54470495210450358376142933 638326115747465137220425)
                    ·
                      rfl

theorem cell23_3729407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 8].length) (baseStart_3729407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729407 prefixEnd_3729407 := by exact prefixLift 3729407
  have htrace : WordTrace (prefixWord ++ tailWord_3729407) baseStart_3729407 baseEnd_3729407 := by
    simpa [prefixWord, tailWord_3729407, baseEnd_3729407] using wordTrace_append hprefix tailTrace_3729407
  have hstable : (prefixWord ++ tailWord_3729407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729407).length < 2 ^ (prefixWord ++ tailWord_3729407).sum := by decide
  have hdescent : baseEnd_3729407 < baseStart_3729407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729465 : List Nat := [1, 2, 1, 5, 3, 1, 1, 1, 4, 2, 2]
def baseStart_3729465 : Nat := 118140960795 + 3729465 * 2 ^ 59
def prefixEnd_3729465 : Nat := 4983230072969 + 3 ^ 40 * 3729465 * 2
def baseEnd_3729465 : Nat := 1915008129120356184736009

theorem tailTrace_3729465 : CollatzResearch.WordTrace tailWord_3729465 prefixEnd_3729465 1915008129120356184736009 := by
  unfold tailWord_3729465
  simp only [CollatzResearch.WordTrace]
  refine ⟨136024763433792721757573849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90683175622528481171715899 136024763433792721757573849)
  ·
    refine ⟨102018572575344541318180387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136024763433792721757573849 102018572575344541318180387)
    ·
      refine ⟨153027858863016811977270581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102018572575344541318180387 153027858863016811977270581)
      ·
        refine ⟨14346361768407826122869117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153027858863016811977270581 14346361768407826122869117)
        ·
          refine ⟨5379885663152934796075919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14346361768407826122869117 5379885663152934796075919)
          ·
            refine ⟨8069828494729402194113879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5379885663152934796075919 8069828494729402194113879)
            ·
              refine ⟨12104742742094103291170819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8069828494729402194113879 12104742742094103291170819)
              ·
                refine ⟨18157114113141154936756229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12104742742094103291170819 18157114113141154936756229)
                ·
                  refine ⟨3404458896213966550641793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18157114113141154936756229 3404458896213966550641793)
                  ·
                    refine ⟨2553344172160474912981345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3404458896213966550641793 2553344172160474912981345)
                    ·
                      refine ⟨1915008129120356184736009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2553344172160474912981345 1915008129120356184736009)
                      ·
                        rfl

theorem cell23_3729465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_3729465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729465 prefixEnd_3729465 := by exact prefixLift 3729465
  have htrace : WordTrace (prefixWord ++ tailWord_3729465) baseStart_3729465 baseEnd_3729465 := by
    simpa [prefixWord, tailWord_3729465, baseEnd_3729465] using wordTrace_append hprefix tailTrace_3729465
  have hstable : (prefixWord ++ tailWord_3729465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729465).length < 2 ^ (prefixWord ++ tailWord_3729465).sum := by decide
  have hdescent : baseEnd_3729465 < baseStart_3729465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729471 : List Nat := [1, 1, 2, 2, 3, 1, 4, 4, 5]
def baseStart_3729471 : Nat := 118140960795 + 3729471 * 2 ^ 59
def prefixEnd_3729471 : Nat := 4983230072969 + 3 ^ 40 * 3729471 * 2
def baseEnd_3729471 : Nat := 212779023333809240140109

theorem tailTrace_3729471 : CollatzResearch.WordTrace tailWord_3729471 prefixEnd_3729471 212779023333809240140109 := by
  unfold tailWord_3729471
  simp only [CollatzResearch.WordTrace]
  refine ⟨136024982271770984782292267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90683321514513989854861511 136024982271770984782292267)
  ·
    refine ⟨204037473407656477173438401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136024982271770984782292267 204037473407656477173438401)
    ·
      refine ⟨153028105055742357880078801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204037473407656477173438401 153028105055742357880078801)
      ·
        refine ⟨114771078791806768410059101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153028105055742357880078801 114771078791806768410059101)
        ·
          refine ⟨43039154546927538153772163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114771078791806768410059101 43039154546927538153772163)
          ·
            refine ⟨64558731820391307230658245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43039154546927538153772163 64558731820391307230658245)
            ·
              refine ⟨12104762216323370105748421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64558731820391307230658245 12104762216323370105748421)
              ·
                refine ⟨2269642915560631894827829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12104762216323370105748421 2269642915560631894827829)
                ·
                  refine ⟨212779023333809240140109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2269642915560631894827829 212779023333809240140109)
                  ·
                    rfl

theorem cell23_3729471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4, 5].length) (baseStart_3729471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729471 prefixEnd_3729471 := by exact prefixLift 3729471
  have htrace : WordTrace (prefixWord ++ tailWord_3729471) baseStart_3729471 baseEnd_3729471 := by
    simpa [prefixWord, tailWord_3729471, baseEnd_3729471] using wordTrace_append hprefix tailTrace_3729471
  have hstable : (prefixWord ++ tailWord_3729471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729471).length < 2 ^ (prefixWord ++ tailWord_3729471).sum := by decide
  have hdescent : baseEnd_3729471 < baseStart_3729471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729478 : List Nat := [6, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_3729478 : Nat := 118140960795 + 3729478 * 2 ^ 59
def prefixEnd_3729478 : Nat := 4983230072969 + 3 ^ 40 * 3729478 * 2
def baseEnd_3729478 : Nat := 1915014804368864633873449

theorem tailTrace_3729478 : CollatzResearch.WordTrace tailWord_3729478 prefixEnd_3729478 1915014804368864633873449 := by
  unfold tailWord_3729478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4250788674460800780556159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 90683491721830416651864725 4250788674460800780556159)
  ·
    refine ⟨6376183011691201170834239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4250788674460800780556159 6376183011691201170834239)
    ·
      refine ⟨9564274517536801756251359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6376183011691201170834239 9564274517536801756251359)
      ·
        refine ⟨14346411776305202634377039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9564274517536801756251359 14346411776305202634377039)
        ·
          refine ⟨21519617664457803951565559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14346411776305202634377039 21519617664457803951565559)
          ·
            refine ⟨32279426496686705927348339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21519617664457803951565559 32279426496686705927348339)
            ·
              refine ⟨48419139745030058891022509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32279426496686705927348339 48419139745030058891022509)
              ·
                refine ⟨18157177404386272084133441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48419139745030058891022509 18157177404386272084133441)
                ·
                  refine ⟨13617883053289704063100081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18157177404386272084133441 13617883053289704063100081)
                  ·
                    refine ⟨10213412289967278047325061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13617883053289704063100081 10213412289967278047325061)
                    ·
                      refine ⟨1915014804368864633873449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10213412289967278047325061 1915014804368864633873449)
                      ·
                        rfl

theorem cell23_3729478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_3729478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729478 prefixEnd_3729478 := by exact prefixLift 3729478
  have htrace : WordTrace (prefixWord ++ tailWord_3729478) baseStart_3729478 baseEnd_3729478 := by
    simpa [prefixWord, tailWord_3729478, baseEnd_3729478] using wordTrace_append hprefix tailTrace_3729478
  have hstable : (prefixWord ++ tailWord_3729478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729478).length < 2 ^ (prefixWord ++ tailWord_3729478).sum := by decide
  have hdescent : baseEnd_3729478 < baseStart_3729478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729484 : List Nat := [2, 2, 1, 3, 1, 1, 3, 2, 1, 7]
def baseStart_3729484 : Nat := 118140960795 + 3729484 * 2 ^ 59
def prefixEnd_3729484 : Nat := 4983230072969 + 3 ^ 40 * 3729484 * 2
def baseEnd_3729484 : Nat := 638339295084263870132807

theorem tailTrace_3729484 : CollatzResearch.WordTrace tailWord_3729484 prefixEnd_3729484 638339295084263870132807 := by
  unfold tailWord_3729484
  simp only [CollatzResearch.WordTrace]
  refine ⟨68012728210361944001257753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90683637613815925335010337 68012728210361944001257753)
  ·
    refine ⟨51009546157771458000943315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68012728210361944001257753 51009546157771458000943315)
    ·
      refine ⟨76514319236657187001414973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51009546157771458000943315 76514319236657187001414973)
      ·
        refine ⟨28692869713746445125530615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76514319236657187001414973 28692869713746445125530615)
        ·
          refine ⟨43039304570619667688295923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28692869713746445125530615 43039304570619667688295923)
          ·
            refine ⟨64558956855929501532443885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43039304570619667688295923 64558956855929501532443885)
            ·
              refine ⟨24209608820973563074666457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64558956855929501532443885 24209608820973563074666457)
              ·
                refine ⟨18157206615730172305999843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24209608820973563074666457 18157206615730172305999843)
                ·
                  refine ⟨27235809923595258458999765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18157206615730172305999843 27235809923595258458999765)
                  ·
                    refine ⟨638339295084263870132807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27235809923595258458999765 638339295084263870132807)
                    ·
                      rfl

theorem cell23_3729484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 1, 7].length) (baseStart_3729484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729484 prefixEnd_3729484 := by exact prefixLift 3729484
  have htrace : WordTrace (prefixWord ++ tailWord_3729484) baseStart_3729484 baseEnd_3729484 := by
    simpa [prefixWord, tailWord_3729484, baseEnd_3729484] using wordTrace_append hprefix tailTrace_3729484
  have hstable : (prefixWord ++ tailWord_3729484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729484).length < 2 ^ (prefixWord ++ tailWord_3729484).sum := by decide
  have hdescent : baseEnd_3729484 < baseStart_3729484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729521 : List Nat := [1, 2, 2, 2, 1, 1, 5, 2, 2, 1, 4]
def baseStart_3729521 : Nat := 118140960795 + 3729521 * 2 ^ 59
def prefixEnd_3729521 : Nat := 4983230072969 + 3 ^ 40 * 3729521 * 2
def baseEnd_3729521 : Nat := 1915036884037007965635751

theorem tailTrace_3729521 : CollatzResearch.WordTrace tailWord_3729521 prefixEnd_3729521 1915036884037007965635751 := by
  unfold tailWord_3729521
  simp only [CollatzResearch.WordTrace]
  refine ⟨136026805921589843321612417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90684537281059895547741611 136026805921589843321612417)
  ·
    refine ⟨102020104441192382491209313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136026805921589843321612417 102020104441192382491209313)
    ·
      refine ⟨76515078330894286868406985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102020104441192382491209313 76515078330894286868406985)
      ·
        refine ⟨57386308748170715151305239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76515078330894286868406985 57386308748170715151305239)
        ·
          refine ⟨86079463122256072726957859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57386308748170715151305239 86079463122256072726957859)
          ·
            refine ⟨129119194683384109090436789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86079463122256072726957859 129119194683384109090436789)
            ·
              refine ⟨12104924501567260227228449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129119194683384109090436789 12104924501567260227228449)
              ·
                refine ⟨9078693376175445170421337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12104924501567260227228449 9078693376175445170421337)
                ·
                  refine ⟨6809020032131583877816003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9078693376175445170421337 6809020032131583877816003)
                  ·
                    refine ⟨10213530048197375816724005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6809020032131583877816003 10213530048197375816724005)
                    ·
                      refine ⟨1915036884037007965635751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10213530048197375816724005 1915036884037007965635751)
                      ·
                        rfl

theorem cell23_3729521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_3729521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729521 prefixEnd_3729521 := by exact prefixLift 3729521
  have htrace : WordTrace (prefixWord ++ tailWord_3729521) baseStart_3729521 baseEnd_3729521 := by
    simpa [prefixWord, tailWord_3729521, baseEnd_3729521] using wordTrace_append hprefix tailTrace_3729521
  have hstable : (prefixWord ++ tailWord_3729521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729521).length < 2 ^ (prefixWord ++ tailWord_3729521).sum := by decide
  have hdescent : baseEnd_3729521 < baseStart_3729521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729584 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 7]
def baseStart_3729584 : Nat := 118140960795 + 3729584 * 2 ^ 59
def prefixEnd_3729584 : Nat := 4983230072969 + 3 ^ 40 * 3729584 * 2
def baseEnd_3729584 : Nat := 1915069233318241219147961

theorem tailTrace_3729584 : CollatzResearch.WordTrace tailWord_3729584 prefixEnd_3729584 1915069233318241219147961 := by
  unfold tailWord_3729584
  simp only [CollatzResearch.WordTrace]
  refine ⟨68014551860180802540577903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90686069146907736720770537 68014551860180802540577903)
  ·
    refine ⟨102021827790271203810866855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68014551860180802540577903 102021827790271203810866855)
    ·
      refine ⟨153032741685406805716300283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102021827790271203810866855 153032741685406805716300283)
      ·
        refine ⟨229549112528110208574450425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153032741685406805716300283 229549112528110208574450425)
        ·
          refine ⟨172161834396082656430837819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229549112528110208574450425 172161834396082656430837819)
          ·
            refine ⟨258242751594123984646256729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172161834396082656430837819 258242751594123984646256729)
            ·
              refine ⟨193682063695592988484692547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258242751594123984646256729 193682063695592988484692547)
              ·
                refine ⟨290523095543389482727038821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193682063695592988484692547 290523095543389482727038821)
                ·
                  refine ⟨54473080414385528011319779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 290523095543389482727038821 54473080414385528011319779)
                  ·
                    refine ⟨81709620621578292016979669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54473080414385528011319779 81709620621578292016979669)
                    ·
                      refine ⟨1915069233318241219147961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 81709620621578292016979669 1915069233318241219147961)
                      ·
                        rfl

theorem cell23_3729584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 7].length) (baseStart_3729584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729584 prefixEnd_3729584 := by exact prefixLift 3729584
  have htrace : WordTrace (prefixWord ++ tailWord_3729584) baseStart_3729584 baseEnd_3729584 := by
    simpa [prefixWord, tailWord_3729584, baseEnd_3729584] using wordTrace_append hprefix tailTrace_3729584
  have hstable : (prefixWord ++ tailWord_3729584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729584).length < 2 ^ (prefixWord ++ tailWord_3729584).sum := by decide
  have hdescent : baseEnd_3729584 < baseStart_3729584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729591 : List Nat := [1, 1, 3, 1, 4, 2, 1, 2, 3, 5]
def baseStart_3729591 : Nat := 118140960795 + 3729591 * 2 ^ 59
def prefixEnd_3729591 : Nat := 4983230072969 + 3 ^ 40 * 3729591 * 2
def baseEnd_3729591 : Nat := 638357609227607563920143

theorem tailTrace_3729591 : CollatzResearch.WordTrace tailWord_3729591 prefixEnd_3729591 638357609227607563920143 := by
  unfold tailWord_3729591
  simp only [CollatzResearch.WordTrace]
  refine ⟨136029359031336245276660627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90686239354224163517773751 136029359031336245276660627)
  ·
    refine ⟨204044038547004367914990941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136029359031336245276660627 204044038547004367914990941)
    ·
      refine ⟨76516514455126637968121603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204044038547004367914990941 76516514455126637968121603)
      ·
        refine ⟨114774771682689956952182405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76516514455126637968121603 114774771682689956952182405)
        ·
          refine ⟨21520269690504366928534201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114774771682689956952182405 21520269690504366928534201)
          ·
            refine ⟨16140202267878275196400651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21520269690504366928534201 16140202267878275196400651)
            ·
              refine ⟨24210303401817412794600977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16140202267878275196400651 24210303401817412794600977)
              ·
                refine ⟨18157727551363059595950733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24210303401817412794600977 18157727551363059595950733)
                ·
                  refine ⟨6809147831761147348481525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18157727551363059595950733 6809147831761147348481525)
                  ·
                    refine ⟨638357609227607563920143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6809147831761147348481525 638357609227607563920143)
                    ·
                      rfl

theorem cell23_3729591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 5].length) (baseStart_3729591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729591 prefixEnd_3729591 := by exact prefixLift 3729591
  have htrace : WordTrace (prefixWord ++ tailWord_3729591) baseStart_3729591 baseEnd_3729591 := by
    simpa [prefixWord, tailWord_3729591, baseEnd_3729591] using wordTrace_append hprefix tailTrace_3729591
  have hstable : (prefixWord ++ tailWord_3729591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729591).length < 2 ^ (prefixWord ++ tailWord_3729591).sum := by decide
  have hdescent : baseEnd_3729591 < baseStart_3729591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729611 : List Nat := [1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 4]
def baseStart_3729611 : Nat := 118140960795 + 3729611 * 2 ^ 59
def prefixEnd_3729611 : Nat := 4983230072969 + 3 ^ 40 * 3729611 * 2
def baseEnd_3729611 : Nat := 1915083097295912613510337

theorem tailTrace_3729611 : CollatzResearch.WordTrace tailWord_3729611 prefixEnd_3729611 1915083097295912613510337 := by
  unfold tailWord_3729611
  simp only [CollatzResearch.WordTrace]
  refine ⟨136030088491263788692388687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90686725660842525794925791 136030088491263788692388687)
  ·
    refine ⟨204045132736895683038583031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136030088491263788692388687 204045132736895683038583031)
    ·
      refine ⟨306067699105343524557874547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204045132736895683038583031 306067699105343524557874547)
      ·
        refine ⟨459101548658015286836811821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306067699105343524557874547 459101548658015286836811821)
        ·
          refine ⟨172163080746755732563804433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 459101548658015286836811821 172163080746755732563804433)
          ·
            refine ⟨129122310560066799422853325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172163080746755732563804433 129122310560066799422853325)
            ·
              refine ⟨48420866460025049783569997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129122310560066799422853325 48420866460025049783569997)
              ·
                refine ⟨18157824922509393668838749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48420866460025049783569997 18157824922509393668838749)
                ·
                  refine ⟨6809184345941022625814531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18157824922509393668838749 6809184345941022625814531)
                  ·
                    refine ⟨10213776518911533938721797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6809184345941022625814531 10213776518911533938721797)
                    ·
                      refine ⟨1915083097295912613510337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10213776518911533938721797 1915083097295912613510337)
                      ·
                        rfl

theorem cell23_3729611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 4].length) (baseStart_3729611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729611 prefixEnd_3729611 := by exact prefixLift 3729611
  have htrace : WordTrace (prefixWord ++ tailWord_3729611) baseStart_3729611 baseEnd_3729611 := by
    simpa [prefixWord, tailWord_3729611, baseEnd_3729611] using wordTrace_append hprefix tailTrace_3729611
  have hstable : (prefixWord ++ tailWord_3729611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729611).length < 2 ^ (prefixWord ++ tailWord_3729611).sum := by decide
  have hdescent : baseEnd_3729611 < baseStart_3729611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729631 : List Nat := [1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 5]
def baseStart_3729631 : Nat := 118140960795 + 3729631 * 2 ^ 59
def prefixEnd_3729631 : Nat := 4983230072969 + 3 ^ 40 * 3729631 * 2
def baseEnd_3729631 : Nat := 1915093366909002535260245

theorem tailTrace_3729631 : CollatzResearch.WordTrace tailWord_3729631 prefixEnd_3729631 1915093366909002535260245 := by
  unfold tailWord_3729631
  simp only [CollatzResearch.WordTrace]
  refine ⟨136030817951191332108116747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90687211967460888072077831 136030817951191332108116747)
  ·
    refine ⟨204046226926786998162175121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136030817951191332108116747 204046226926786998162175121)
    ·
      refine ⟨153034670195090248621631341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204046226926786998162175121 153034670195090248621631341)
      ·
        refine ⟨57388001323158843233111753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153034670195090248621631341 57388001323158843233111753)
        ·
          refine ⟨43041000992369132424833815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57388001323158843233111753 43041000992369132424833815)
          ·
            refine ⟨64561501488553698637250723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43041000992369132424833815 64561501488553698637250723)
            ·
              refine ⟨96842252232830547955876085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64561501488553698637250723 96842252232830547955876085)
              ·
                refine ⟨9078961146827863870863383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96842252232830547955876085 9078961146827863870863383)
                ·
                  refine ⟨13618441720241795806295075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9078961146827863870863383 13618441720241795806295075)
                  ·
                    refine ⟨20427662580362693709442613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13618441720241795806295075 20427662580362693709442613)
                    ·
                      refine ⟨1915093366909002535260245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20427662580362693709442613 1915093366909002535260245)
                      ·
                        rfl

theorem cell23_3729631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_3729631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729631 prefixEnd_3729631 := by exact prefixLift 3729631
  have htrace : WordTrace (prefixWord ++ tailWord_3729631) baseStart_3729631 baseEnd_3729631 := by
    simpa [prefixWord, tailWord_3729631, baseEnd_3729631] using wordTrace_append hprefix tailTrace_3729631
  have hstable : (prefixWord ++ tailWord_3729631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729631).length < 2 ^ (prefixWord ++ tailWord_3729631).sum := by decide
  have hdescent : baseEnd_3729631 < baseStart_3729631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729658 : List Nat := [3, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4]
def baseStart_3729658 : Nat := 118140960795 + 3729658 * 2 ^ 59
def prefixEnd_3729658 : Nat := 4983230072969 + 3 ^ 40 * 3729658 * 2
def baseEnd_3729658 : Nat := 1915107230886673929622621

theorem tailTrace_3729658 : CollatzResearch.WordTrace tailWord_3729658 prefixEnd_3729658 1915107230886673929622621 := by
  unfold tailWord_3729658
  simp only [CollatzResearch.WordTrace]
  refine ⟨34007950680523378929837407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90687868481395677146233085 34007950680523378929837407)
  ·
    refine ⟨51011926020785068394756111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34007950680523378929837407 51011926020785068394756111)
    ·
      refine ⟨76517889031177602592134167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51011926020785068394756111 76517889031177602592134167)
      ·
        refine ⟨114776833546766403888201251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76517889031177602592134167 114776833546766403888201251)
        ·
          refine ⟨172165250320149605832301877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114776833546766403888201251 172165250320149605832301877)
          ·
            refine ⟨16140492217514025546778301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 172165250320149605832301877 16140492217514025546778301)
            ·
              refine ⟨6052684581567759580041863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16140492217514025546778301 6052684581567759580041863)
              ·
                refine ⟨9079026872351639370062795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6052684581567759580041863 9079026872351639370062795)
                ·
                  refine ⟨13618540308527459055094193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9079026872351639370062795 13618540308527459055094193)
                  ·
                    refine ⟨10213905231395594291320645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13618540308527459055094193 10213905231395594291320645)
                    ·
                      refine ⟨1915107230886673929622621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10213905231395594291320645 1915107230886673929622621)
                      ·
                        rfl

theorem cell23_3729658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4].length) (baseStart_3729658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729658 prefixEnd_3729658 := by exact prefixLift 3729658
  have htrace : WordTrace (prefixWord ++ tailWord_3729658) baseStart_3729658 baseEnd_3729658 := by
    simpa [prefixWord, tailWord_3729658, baseEnd_3729658] using wordTrace_append hprefix tailTrace_3729658
  have hstable : (prefixWord ++ tailWord_3729658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729658).length < 2 ^ (prefixWord ++ tailWord_3729658).sum := by decide
  have hdescent : baseEnd_3729658 < baseStart_3729658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729662 : List Nat := [4, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2]
def baseStart_3729662 : Nat := 118140960795 + 3729662 * 2 ^ 59
def prefixEnd_3729662 : Nat := 4983230072969 + 3 ^ 40 * 3729662 * 2
def baseEnd_3729662 : Nat := 1915109284809291913972603

theorem tailTrace_3729662 : CollatzResearch.WordTrace tailWord_3729662 prefixEnd_3729662 1915109284809291913972603 := by
  unfold tailWord_3729662
  simp only [CollatzResearch.WordTrace]
  refine ⟨17003993576759878050311905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90687965742719349601663493 17003993576759878050311905)
  ·
    refine ⟨12752995182569908537733929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17003993576759878050311905 12752995182569908537733929)
    ·
      refine ⟨9564746386927431403300447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12752995182569908537733929 9564746386927431403300447)
      ·
        refine ⟨14347119580391147104950671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9564746386927431403300447 14347119580391147104950671)
        ·
          refine ⟨21520679370586720657426007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14347119580391147104950671 21520679370586720657426007)
          ·
            refine ⟨32281019055880080986139011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21520679370586720657426007 32281019055880080986139011)
            ·
              refine ⟨48421528583820121479208517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32281019055880080986139011 48421528583820121479208517)
              ·
                refine ⟨9079036609466272777351597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48421528583820121479208517 9079036609466272777351597)
                ·
                  refine ⟨3404638728549852291506849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9079036609466272777351597 3404638728549852291506849)
                  ·
                    refine ⟨2553479046412389218630137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3404638728549852291506849 2553479046412389218630137)
                    ·
                      refine ⟨1915109284809291913972603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2553479046412389218630137 1915109284809291913972603)
                      ·
                        rfl

theorem cell23_3729662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_3729662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729662 prefixEnd_3729662 := by exact prefixLift 3729662
  have htrace : WordTrace (prefixWord ++ tailWord_3729662) baseStart_3729662 baseEnd_3729662 := by
    simpa [prefixWord, tailWord_3729662, baseEnd_3729662] using wordTrace_append hprefix tailTrace_3729662
  have hstable : (prefixWord ++ tailWord_3729662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729662).length < 2 ^ (prefixWord ++ tailWord_3729662).sum := by decide
  have hdescent : baseEnd_3729662 < baseStart_3729662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729665 : List Nat := [1, 2, 4, 1, 1, 2, 4, 2, 1, 2, 3]
def baseStart_3729665 : Nat := 118140960795 + 3729665 * 2 ^ 59
def prefixEnd_3729665 : Nat := 4983230072969 + 3 ^ 40 * 3729665 * 2
def baseEnd_3729665 : Nat := 1915110825251255402235089

theorem tailTrace_3729665 : CollatzResearch.WordTrace tailWord_3729665 prefixEnd_3729665 1915110825251255402235089 := by
  unfold tailWord_3729665
  simp only [CollatzResearch.WordTrace]
  refine ⟨136032058033068155914854449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90688038688712103943236299 136032058033068155914854449)
  ·
    refine ⟨102024043524801116936140837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136032058033068155914854449 102024043524801116936140837)
    ·
      refine ⟨19129508160900209425526407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102024043524801116936140837 19129508160900209425526407)
      ·
        refine ⟨28694262241350314138289611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19129508160900209425526407 28694262241350314138289611)
        ·
          refine ⟨43041393362025471207434417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28694262241350314138289611 43041393362025471207434417)
          ·
            refine ⟨32281045021519103405575813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43041393362025471207434417 32281045021519103405575813)
            ·
              refine ⟨6052695941534831888545465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32281045021519103405575813 6052695941534831888545465)
              ·
                refine ⟨4539521956151123916409099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6052695941534831888545465 4539521956151123916409099)
                ·
                  refine ⟨6809282934226685874613649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4539521956151123916409099 6809282934226685874613649)
                  ·
                    refine ⟨5106962200670014405960237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6809282934226685874613649 5106962200670014405960237)
                    ·
                      refine ⟨1915110825251255402235089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5106962200670014405960237 1915110825251255402235089)
                      ·
                        rfl

theorem cell23_3729665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_3729665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729665 prefixEnd_3729665 := by exact prefixLift 3729665
  have htrace : WordTrace (prefixWord ++ tailWord_3729665) baseStart_3729665 baseEnd_3729665 := by
    simpa [prefixWord, tailWord_3729665, baseEnd_3729665] using wordTrace_append hprefix tailTrace_3729665
  have hstable : (prefixWord ++ tailWord_3729665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729665).length < 2 ^ (prefixWord ++ tailWord_3729665).sum := by decide
  have hdescent : baseEnd_3729665 < baseStart_3729665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729668 : List Nat := [2, 3, 2, 2, 3, 1, 1, 9]
def baseStart_3729668 : Nat := 118140960795 + 3729668 * 2 ^ 59
def prefixEnd_3729668 : Nat := 4983230072969 + 3 ^ 40 * 3729668 * 2
def baseEnd_3729668 : Nat := 70930087618267366314725

theorem tailTrace_3729668 : CollatzResearch.WordTrace tailWord_3729668 prefixEnd_3729668 70930087618267366314725 := by
  unfold tailWord_3729668
  simp only [CollatzResearch.WordTrace]
  refine ⟨68016083726028643713606829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90688111634704858284809105 68016083726028643713606829)
  ·
    refine ⟨25506031397260741392602561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68016083726028643713606829 25506031397260741392602561)
    ·
      refine ⟨19129523547945556044451921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25506031397260741392602561 19129523547945556044451921)
      ·
        refine ⟨14347142660959167033338941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19129523547945556044451921 14347142660959167033338941)
        ·
          refine ⟨5380178497859687637502103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14347142660959167033338941 5380178497859687637502103)
          ·
            refine ⟨8070267746789531456253155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5380178497859687637502103 8070267746789531456253155)
            ·
              refine ⟨12105401620184297184379733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8070267746789531456253155 12105401620184297184379733)
              ·
                refine ⟨70930087618267366314725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12105401620184297184379733 70930087618267366314725)
                ·
                  rfl

theorem cell23_3729668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 9].length) (baseStart_3729668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729668 prefixEnd_3729668 := by exact prefixLift 3729668
  have htrace : WordTrace (prefixWord ++ tailWord_3729668) baseStart_3729668 baseEnd_3729668 := by
    simpa [prefixWord, tailWord_3729668, baseEnd_3729668] using wordTrace_append hprefix tailTrace_3729668
  have hstable : (prefixWord ++ tailWord_3729668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729668).length < 2 ^ (prefixWord ++ tailWord_3729668).sum := by decide
  have hdescent : baseEnd_3729668 < baseStart_3729668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729678 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3]
def baseStart_3729678 : Nat := 118140960795 + 3729678 * 2 ^ 59
def prefixEnd_3729678 : Nat := 4983230072969 + 3 ^ 40 * 3729678 * 2
def baseEnd_3729678 : Nat := 1915117500499763851372529

theorem tailTrace_3729678 : CollatzResearch.WordTrace tailWord_3729678 prefixEnd_3729678 1915117500499763851372529 := by
  unfold tailWord_3729678
  simp only [CollatzResearch.WordTrace]
  refine ⟨17004066522752632391884711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90688354788014039423385125 17004066522752632391884711)
  ·
    refine ⟨25506099784128948587827067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17004066522752632391884711 25506099784128948587827067)
    ·
      refine ⟨38259149676193422881740601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25506099784128948587827067 38259149676193422881740601)
      ·
        refine ⟨28694362257145067161305451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38259149676193422881740601 28694362257145067161305451)
        ·
          refine ⟨43041543385717600741958177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28694362257145067161305451 43041543385717600741958177)
          ·
            refine ⟨32281157539288200556468633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43041543385717600741958177 32281157539288200556468633)
            ·
              refine ⟨24210868154466150417351475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32281157539288200556468633 24210868154466150417351475)
              ·
                refine ⟨36316302231699225626027213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24210868154466150417351475 36316302231699225626027213)
                ·
                  refine ⟨13618613336887209609760205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36316302231699225626027213 13618613336887209609760205)
                  ·
                    refine ⟨5106980001332703603660077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13618613336887209609760205 5106980001332703603660077)
                    ·
                      refine ⟨1915117500499763851372529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5106980001332703603660077 1915117500499763851372529)
                      ·
                        rfl

theorem cell23_3729678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_3729678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729678 prefixEnd_3729678 := by exact prefixLift 3729678
  have htrace : WordTrace (prefixWord ++ tailWord_3729678) baseStart_3729678 baseEnd_3729678 := by
    simpa [prefixWord, tailWord_3729678, baseEnd_3729678] using wordTrace_append hprefix tailTrace_3729678
  have hstable : (prefixWord ++ tailWord_3729678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729678).length < 2 ^ (prefixWord ++ tailWord_3729678).sum := by decide
  have hdescent : baseEnd_3729678 < baseStart_3729678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729695 : List Nat := [1, 1, 2, 4, 3, 1, 2, 1, 4, 1, 3]
def baseStart_3729695 : Nat := 118140960795 + 3729695 * 2 ^ 59
def prefixEnd_3729695 : Nat := 4983230072969 + 3 ^ 40 * 3729695 * 2
def baseEnd_3729695 : Nat := 1915126229670890284859951

theorem tailTrace_3729695 : CollatzResearch.WordTrace tailWord_3729695 prefixEnd_3729695 1915126229670890284859951 := by
  unfold tailWord_3729695
  simp only [CollatzResearch.WordTrace]
  refine ⟨136033152222959471038446539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90688768148639647358964359 136033152222959471038446539)
  ·
    refine ⟨204049728334439206557669809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136033152222959471038446539 204049728334439206557669809)
    ·
      refine ⟨153037296250829404918252357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204049728334439206557669809 153037296250829404918252357)
      ·
        refine ⟨28694493047030513422172317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153037296250829404918252357 28694493047030513422172317)
        ·
          refine ⟨10760434892636442533314619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28694493047030513422172317 10760434892636442533314619)
          ·
            refine ⟨16140652338954663799971929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10760434892636442533314619 16140652338954663799971929)
            ·
              refine ⟨12105489254215997849978947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16140652338954663799971929 12105489254215997849978947)
              ·
                refine ⟨18158233881323996774968421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12105489254215997849978947 18158233881323996774968421)
                ·
                  refine ⟨3404668852748249395306579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18158233881323996774968421 3404668852748249395306579)
                  ·
                    refine ⟨5107003279122374092959869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3404668852748249395306579 5107003279122374092959869)
                    ·
                      refine ⟨1915126229670890284859951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5107003279122374092959869 1915126229670890284859951)
                      ·
                        rfl

theorem cell23_3729695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_3729695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729695 prefixEnd_3729695 := by exact prefixLift 3729695
  have htrace : WordTrace (prefixWord ++ tailWord_3729695) baseStart_3729695 baseEnd_3729695 := by
    simpa [prefixWord, tailWord_3729695, baseEnd_3729695] using wordTrace_append hprefix tailTrace_3729695
  have hstable : (prefixWord ++ tailWord_3729695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729695).length < 2 ^ (prefixWord ++ tailWord_3729695).sum := by decide
  have hdescent : baseEnd_3729695 < baseStart_3729695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729696 : List Nat := [2, 1, 1, 5, 2, 2, 3, 2, 1, 2, 2]
def baseStart_3729696 : Nat := 118140960795 + 3729696 * 2 ^ 59
def prefixEnd_3729696 : Nat := 4983230072969 + 3 ^ 40 * 3729696 * 2
def baseEnd_3729696 : Nat := 1915126743151544780947447

theorem tailTrace_3729696 : CollatzResearch.WordTrace tailWord_3729696 prefixEnd_3729696 1915126743151544780947447 := by
  unfold tailWord_3729696
  simp only [CollatzResearch.WordTrace]
  refine ⟨68016594347977924104616471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90688792463970565472821961 68016594347977924104616471)
  ·
    refine ⟨102024891521966886156924707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68016594347977924104616471 102024891521966886156924707)
    ·
      refine ⟨153037337282950329235387061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102024891521966886156924707 153037337282950329235387061)
      ·
        refine ⟨14347250370276593365817537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153037337282950329235387061 14347250370276593365817537)
        ·
          refine ⟨10760437777707445024363153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14347250370276593365817537 10760437777707445024363153)
          ·
            refine ⟨8070328333280583768272365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10760437777707445024363153 8070328333280583768272365)
            ·
              refine ⟨3026373124980218913102137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8070328333280583768272365 3026373124980218913102137)
              ·
                refine ⟨2269779843735164184826603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3026373124980218913102137 2269779843735164184826603)
                ·
                  refine ⟨3404669765602746277239905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2269779843735164184826603 3404669765602746277239905)
                  ·
                    refine ⟨2553502324202059707929929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3404669765602746277239905 2553502324202059707929929)
                    ·
                      refine ⟨1915126743151544780947447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2553502324202059707929929 1915126743151544780947447)
                      ·
                        rfl

theorem cell23_3729696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_3729696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729696 prefixEnd_3729696 := by exact prefixLift 3729696
  have htrace : WordTrace (prefixWord ++ tailWord_3729696) baseStart_3729696 baseEnd_3729696 := by
    simpa [prefixWord, tailWord_3729696, baseEnd_3729696] using wordTrace_append hprefix tailTrace_3729696
  have hstable : (prefixWord ++ tailWord_3729696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729696).length < 2 ^ (prefixWord ++ tailWord_3729696).sum := by decide
  have hdescent : baseEnd_3729696 < baseStart_3729696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729706 : List Nat := [3, 1, 4, 2, 3, 1, 2, 1, 2, 4]
def baseStart_3729706 : Nat := 118140960795 + 3729706 * 2 ^ 59
def prefixEnd_3729706 : Nat := 4983230072969 + 3 ^ 40 * 3729706 * 2
def baseEnd_3729706 : Nat := 638377292652696580607467

theorem tailTrace_3729706 : CollatzResearch.WordTrace tailWord_3729706 prefixEnd_3729706 638377292652696580607467 := by
  unfold tailWord_3729706
  simp only [CollatzResearch.WordTrace]
  refine ⟨34008388356479904979274243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90689035617279746611397981 34008388356479904979274243)
  ·
    refine ⟨51012582534719857468911365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34008388356479904979274243 51012582534719857468911365)
    ·
      refine ⟨9564859225259973275420881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51012582534719857468911365 9564859225259973275420881)
      ·
        refine ⟨7173644418944979956565661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9564859225259973275420881 7173644418944979956565661)
        ·
          refine ⟨2690116657104367483712123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7173644418944979956565661 2690116657104367483712123)
          ·
            refine ⟨4035174985656551225568185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2690116657104367483712123 4035174985656551225568185)
            ·
              refine ⟨3026381239242413419176139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4035174985656551225568185 3026381239242413419176139)
              ·
                refine ⟨4539571858863620128764209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3026381239242413419176139 4539571858863620128764209)
                ·
                  refine ⟨3404678894147715096573157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4539571858863620128764209 3404678894147715096573157)
                  ·
                    refine ⟨638377292652696580607467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3404678894147715096573157 638377292652696580607467)
                    ·
                      rfl

theorem cell23_3729706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_3729706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729706 prefixEnd_3729706 := by exact prefixLift 3729706
  have htrace : WordTrace (prefixWord ++ tailWord_3729706) baseStart_3729706 baseEnd_3729706 := by
    simpa [prefixWord, tailWord_3729706, baseEnd_3729706] using wordTrace_append hprefix tailTrace_3729706
  have hstable : (prefixWord ++ tailWord_3729706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729706).length < 2 ^ (prefixWord ++ tailWord_3729706).sum := by decide
  have hdescent : baseEnd_3729706 < baseStart_3729706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729711 : List Nat := [1, 1, 2, 1, 2, 1, 4, 3, 2, 6]
def baseStart_3729711 : Nat := 118140960795 + 3729711 * 2 ^ 59
def prefixEnd_3729711 : Nat := 4983230072969 + 3 ^ 40 * 3729711 * 2
def baseEnd_3729711 : Nat := 638378148453787407419959

theorem tailTrace_3729711 : CollatzResearch.WordTrace tailWord_3729711 prefixEnd_3729711 638378148453787407419959 := by
  unfold tailWord_3729711
  simp only [CollatzResearch.WordTrace]
  refine ⟨136033735790901505771028987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90689157193934337180685991 136033735790901505771028987)
  ·
    refine ⟨204050603686352258656543481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136033735790901505771028987 204050603686352258656543481)
    ·
      refine ⟨153037952764764193992407611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204050603686352258656543481 153037952764764193992407611)
      ·
        refine ⟨229556929147146290988611417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153037952764764193992407611 229556929147146290988611417)
        ·
          refine ⟨172167696860359718241458563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229556929147146290988611417 172167696860359718241458563)
          ·
            refine ⟨258251545290539577362187845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172167696860359718241458563 258251545290539577362187845)
            ·
              refine ⟨48422164741976170755410221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 258251545290539577362187845 48422164741976170755410221)
              ·
                refine ⟨18158311778241064033278833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48422164741976170755410221 18158311778241064033278833)
                ·
                  refine ⟨13618733833680798024959125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18158311778241064033278833 13618733833680798024959125)
                  ·
                    refine ⟨638378148453787407419959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13618733833680798024959125 638378148453787407419959)
                    ·
                      rfl

theorem cell23_3729711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 6].length) (baseStart_3729711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729711 prefixEnd_3729711 := by exact prefixLift 3729711
  have htrace : WordTrace (prefixWord ++ tailWord_3729711) baseStart_3729711 baseEnd_3729711 := by
    simpa [prefixWord, tailWord_3729711, baseEnd_3729711] using wordTrace_append hprefix tailTrace_3729711
  have hstable : (prefixWord ++ tailWord_3729711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729711).length < 2 ^ (prefixWord ++ tailWord_3729711).sum := by decide
  have hdescent : baseEnd_3729711 < baseStart_3729711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729722 : List Nat := [3, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2]
def baseStart_3729722 : Nat := 118140960795 + 3729722 * 2 ^ 59
def prefixEnd_3729722 : Nat := 4983230072969 + 3 ^ 40 * 3729722 * 2
def baseEnd_3729722 : Nat := 1915140093648561679222327

theorem tailTrace_3729722 : CollatzResearch.WordTrace tailWord_3729722 prefixEnd_3729722 1915140093648561679222327 := by
  unfold tailWord_3729722
  simp only [CollatzResearch.WordTrace]
  refine ⟨34008534248465413662419855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90689424662574436433119613 34008534248465413662419855)
  ·
    refine ⟨51012801372698120493629783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34008534248465413662419855 51012801372698120493629783)
    ·
      refine ⟨76519202059047180740444675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51012801372698120493629783 76519202059047180740444675)
      ·
        refine ⟨114778803088570771110667013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76519202059047180740444675 114778803088570771110667013)
        ·
          refine ⟨21521025579107019583250065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114778803088570771110667013 21521025579107019583250065)
          ·
            refine ⟨16140769184330264687437549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21521025579107019583250065 16140769184330264687437549)
            ·
              refine ⟨6052788444123849257789081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16140769184330264687437549 6052788444123849257789081)
              ·
                refine ⟨4539591333092886943341811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6052788444123849257789081 4539591333092886943341811)
                ·
                  refine ⟨6809386999639330415012717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4539591333092886943341811 6809386999639330415012717)
                  ·
                    refine ⟨2553520124864748905629769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6809386999639330415012717 2553520124864748905629769)
                    ·
                      refine ⟨1915140093648561679222327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2553520124864748905629769 1915140093648561679222327)
                      ·
                        rfl

theorem cell23_3729722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2].length) (baseStart_3729722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729722 prefixEnd_3729722 := by exact prefixLift 3729722
  have htrace : WordTrace (prefixWord ++ tailWord_3729722) baseStart_3729722 baseEnd_3729722 := by
    simpa [prefixWord, tailWord_3729722, baseEnd_3729722] using wordTrace_append hprefix tailTrace_3729722
  have hstable : (prefixWord ++ tailWord_3729722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729722).length < 2 ^ (prefixWord ++ tailWord_3729722).sum := by decide
  have hdescent : baseEnd_3729722 < baseStart_3729722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729735 : List Nat := [1, 1, 4, 1, 2, 2, 3, 2, 1, 4, 2]
def baseStart_3729735 : Nat := 118140960795 + 3729735 * 2 ^ 59
def prefixEnd_3729735 : Nat := 4983230072969 + 3 ^ 40 * 3729735 * 2
def baseEnd_3729735 : Nat := 1915146768897070128359767

theorem tailTrace_3729735 : CollatzResearch.WordTrace tailWord_3729735 prefixEnd_3729735 1915146768897070128359767 := by
  unfold tailWord_3729735
  simp only [CollatzResearch.WordTrace]
  refine ⟨136034611142814557869902659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90689740761876371913268439 136034611142814557869902659)
  ·
    refine ⟨204051916714221836804853989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136034611142814557869902659 204051916714221836804853989)
    ·
      refine ⟨38259734383916594400910123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204051916714221836804853989 38259734383916594400910123)
      ·
        refine ⟨57389601575874891601365185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38259734383916594400910123 57389601575874891601365185)
        ·
          refine ⟨43042201181906168701023889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57389601575874891601365185 43042201181906168701023889)
          ·
            refine ⟨32281650886429626525767917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43042201181906168701023889 32281650886429626525767917)
            ·
              refine ⟨12105619082411109947162969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32281650886429626525767917 12105619082411109947162969)
              ·
                refine ⟨9079214311808332460372227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12105619082411109947162969 9079214311808332460372227)
                ·
                  refine ⟨13618821467712498690558341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9079214311808332460372227 13618821467712498690558341)
                  ·
                    refine ⟨2553529025196093504479689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13618821467712498690558341 2553529025196093504479689)
                    ·
                      refine ⟨1915146768897070128359767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2553529025196093504479689 1915146768897070128359767)
                      ·
                        rfl

theorem cell23_3729735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 4, 2].length) (baseStart_3729735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729735 prefixEnd_3729735 := by exact prefixLift 3729735
  have htrace : WordTrace (prefixWord ++ tailWord_3729735) baseStart_3729735 baseEnd_3729735 := by
    simpa [prefixWord, tailWord_3729735, baseEnd_3729735] using wordTrace_append hprefix tailTrace_3729735
  have hstable : (prefixWord ++ tailWord_3729735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729735).length < 2 ^ (prefixWord ++ tailWord_3729735).sum := by decide
  have hdescent : baseEnd_3729735 < baseStart_3729735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729761 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 1, 3, 8]
def baseStart_3729761 : Nat := 118140960795 + 3729761 * 2 ^ 59
def prefixEnd_3729761 : Nat := 4983230072969 + 3 ^ 40 * 3729761 * 2
def baseEnd_3729761 : Nat := 1915160119394087026634647

theorem tailTrace_3729761 : CollatzResearch.WordTrace tailWord_3729761 prefixEnd_3729761 1915160119394087026634647 := by
  unfold tailWord_3729761
  simp only [CollatzResearch.WordTrace]
  refine ⟨136035559440720364310349137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90690372960480242873566091 136035559440720364310349137)
  ·
    refine ⟨102026669580540273232761853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136035559440720364310349137 102026669580540273232761853)
    ·
      refine ⟨38260001092702602462285695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102026669580540273232761853 38260001092702602462285695)
      ·
        refine ⟨57390001639053903693428543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38260001092702602462285695 57390001639053903693428543)
        ·
          refine ⟨86085002458580855540142815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57390001639053903693428543 86085002458580855540142815)
          ·
            refine ⟨129127503687871283310214223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86085002458580855540142815 129127503687871283310214223)
            ·
              refine ⟨193691255531806924965321335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129127503687871283310214223 193691255531806924965321335)
              ·
                refine ⟨290536883297710387447982003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193691255531806924965321335 290536883297710387447982003)
                ·
                  refine ⟨435805324946565581171973005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 290536883297710387447982003 435805324946565581171973005)
                  ·
                    refine ⟨163426996854962092939489877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 435805324946565581171973005 163426996854962092939489877)
                    ·
                      refine ⟨1915160119394087026634647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 163426996854962092939489877 1915160119394087026634647)
                      ·
                        rfl

theorem cell23_3729761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_3729761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729761 prefixEnd_3729761 := by exact prefixLift 3729761
  have htrace : WordTrace (prefixWord ++ tailWord_3729761) baseStart_3729761 baseEnd_3729761 := by
    simpa [prefixWord, tailWord_3729761, baseEnd_3729761] using wordTrace_append hprefix tailTrace_3729761
  have hstable : (prefixWord ++ tailWord_3729761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729761).length < 2 ^ (prefixWord ++ tailWord_3729761).sum := by decide
  have hdescent : baseEnd_3729761 < baseStart_3729761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729771 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 3, 7]
def baseStart_3729771 : Nat := 118140960795 + 3729771 * 2 ^ 59
def prefixEnd_3729771 : Nat := 4983230072969 + 3 ^ 40 * 3729771 * 2
def baseEnd_3729771 : Nat := 638388418066877329169867

theorem tailTrace_3729771 : CollatzResearch.WordTrace tailWord_3729771 prefixEnd_3729771 638388418066877329169867 := by
  unfold tailWord_3729771
  simp only [CollatzResearch.WordTrace]
  refine ⟨136035924170684136018213167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90690616113789424012142111 136035924170684136018213167)
  ·
    refine ⟨204053886256026204027319751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136035924170684136018213167 204053886256026204027319751)
    ·
      refine ⟨306080829384039306040979627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204053886256026204027319751 306080829384039306040979627)
      ·
        refine ⟨459121244076058959061469441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306080829384039306040979627 459121244076058959061469441)
        ·
          refine ⟨344340933057044219296102081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459121244076058959061469441 344340933057044219296102081)
          ·
            refine ⟨258255699792783164472076561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344340933057044219296102081 258255699792783164472076561)
            ·
              refine ⟨193691774844587373354057421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258255699792783164472076561 193691774844587373354057421)
              ·
                refine ⟨72634415566720265007771533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193691774844587373354057421 72634415566720265007771533)
                ·
                  refine ⟨27237905837520099377914325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72634415566720265007771533 27237905837520099377914325)
                  ·
                    refine ⟨638388418066877329169867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27237905837520099377914325 638388418066877329169867)
                    ·
                      rfl

theorem cell23_3729771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 7].length) (baseStart_3729771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729771 prefixEnd_3729771 := by exact prefixLift 3729771
  have htrace : WordTrace (prefixWord ++ tailWord_3729771) baseStart_3729771 baseEnd_3729771 := by
    simpa [prefixWord, tailWord_3729771, baseEnd_3729771] using wordTrace_append hprefix tailTrace_3729771
  have hstable : (prefixWord ++ tailWord_3729771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729771).length < 2 ^ (prefixWord ++ tailWord_3729771).sum := by decide
  have hdescent : baseEnd_3729771 < baseStart_3729771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729788 : List Nat := [2, 2, 2, 1, 1, 1, 2, 5, 2, 5]
def baseStart_3729788 : Nat := 118140960795 + 3729788 * 2 ^ 59
def prefixEnd_3729788 : Nat := 4983230072969 + 3 ^ 40 * 3729788 * 2
def baseEnd_3729788 : Nat := 638391327790586140332341

theorem tailTrace_3729788 : CollatzResearch.WordTrace tailWord_3729788 prefixEnd_3729788 638391327790586140332341 := by
  unfold tailWord_3729788
  simp only [CollatzResearch.WordTrace]
  refine ⟨68018272105811273960791009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90691029474415031947721345 68018272105811273960791009)
  ·
    refine ⟨51013704079358455470593257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68018272105811273960791009 51013704079358455470593257)
    ·
      refine ⟨38260278059518841602944943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51013704079358455470593257 38260278059518841602944943)
      ·
        refine ⟨57390417089278262404417415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38260278059518841602944943 57390417089278262404417415)
        ·
          refine ⟨86085625633917393606626123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57390417089278262404417415 86085625633917393606626123)
          ·
            refine ⟨129128438450876090409939185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86085625633917393606626123 129128438450876090409939185)
            ·
              refine ⟨96846328838157067807454389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129128438450876090409939185 96846328838157067807454389)
              ·
                refine ⟨9079343328577225106948849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96846328838157067807454389 9079343328577225106948849)
                ·
                  refine ⟨6809507496432918830211637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9079343328577225106948849 6809507496432918830211637)
                  ·
                    refine ⟨638391327790586140332341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6809507496432918830211637 638391327790586140332341)
                    ·
                      rfl

theorem cell23_3729788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_3729788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729788 prefixEnd_3729788 := by exact prefixLift 3729788
  have htrace : WordTrace (prefixWord ++ tailWord_3729788) baseStart_3729788 baseEnd_3729788 := by
    simpa [prefixWord, tailWord_3729788, baseEnd_3729788] using wordTrace_append hprefix tailTrace_3729788
  have hstable : (prefixWord ++ tailWord_3729788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729788).length < 2 ^ (prefixWord ++ tailWord_3729788).sum := by decide
  have hdescent : baseEnd_3729788 < baseStart_3729788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729895 : List Nat := [1, 1, 5, 2, 1, 1, 3, 1, 3, 5]
def baseStart_3729895 : Nat := 118140960795 + 3729895 * 2 ^ 59
def prefixEnd_3729895 : Nat := 4983230072969 + 3 ^ 40 * 3729895 * 2
def baseEnd_3729895 : Nat := 638409641933929834119677

theorem tailTrace_3729895 : CollatzResearch.WordTrace tailWord_3729895 prefixEnd_3729895 638409641933929834119677 := by
  unfold tailWord_3729895
  simp only [CollatzResearch.WordTrace]
  refine ⟨136040446822234905195727139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90693631214823270130484759 136040446822234905195727139)
  ·
    refine ⟨204060670233352357793590709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136040446822234905195727139 204060670233352357793590709)
    ·
      refine ⟨19130687834376783543149129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204060670233352357793590709 19130687834376783543149129)
      ·
        refine ⟨14348015875782587657361847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19130687834376783543149129 14348015875782587657361847)
        ·
          refine ⟨21522023813673881486042771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14348015875782587657361847 21522023813673881486042771)
          ·
            refine ⟨32283035720510822229064157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21522023813673881486042771 32283035720510822229064157)
            ·
              refine ⟨12106138395191558335899059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32283035720510822229064157 12106138395191558335899059)
              ·
                refine ⟨18159207592787337503848589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12106138395191558335899059 18159207592787337503848589)
                ·
                  refine ⟨6809702847295251563943221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18159207592787337503848589 6809702847295251563943221)
                  ·
                    refine ⟨638409641933929834119677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6809702847295251563943221 638409641933929834119677)
                    ·
                      rfl

theorem cell23_3729895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_3729895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729895 prefixEnd_3729895 := by exact prefixLift 3729895
  have htrace : WordTrace (prefixWord ++ tailWord_3729895) baseStart_3729895 baseEnd_3729895 := by
    simpa [prefixWord, tailWord_3729895, baseEnd_3729895] using wordTrace_append hprefix tailTrace_3729895
  have hstable : (prefixWord ++ tailWord_3729895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729895).length < 2 ^ (prefixWord ++ tailWord_3729895).sum := by decide
  have hdescent : baseEnd_3729895 < baseStart_3729895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729912 : List Nat := [2, 1, 2, 1, 1, 4, 5, 1, 1, 5]
def baseStart_3729912 : Nat := 118140960795 + 3729912 * 2 ^ 59
def prefixEnd_3729912 : Nat := 4983230072969 + 3 ^ 40 * 3729912 * 2
def baseEnd_3729912 : Nat := 638412551657638645282151

theorem tailTrace_3729912 : CollatzResearch.WordTrace tailWord_3729912 prefixEnd_3729912 638412551657638645282151 := by
  unfold tailWord_3729912
  simp only [CollatzResearch.WordTrace]
  refine ⟨68020533431586658549547995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90694044575448878066063993 68020533431586658549547995)
  ·
    refine ⟨102030800147379987824321993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68020533431586658549547995 102030800147379987824321993)
    ·
      refine ⟨76523100110534990868241495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102030800147379987824321993 76523100110534990868241495)
      ·
        refine ⟨114784650165802486302362243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76523100110534990868241495 114784650165802486302362243)
        ·
          refine ⟨172176975248703729453543365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114784650165802486302362243 172176975248703729453543365)
          ·
            refine ⟨32283182859131949272539381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172176975248703729453543365 32283182859131949272539381)
            ·
              refine ⟨3026548393043620244300567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32283182859131949272539381 3026548393043620244300567)
              ·
                refine ⟨4539822589565430366450851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3026548393043620244300567 4539822589565430366450851)
                ·
                  refine ⟨6809733884348145549676277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4539822589565430366450851 6809733884348145549676277)
                  ·
                    refine ⟨638412551657638645282151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6809733884348145549676277 638412551657638645282151)
                    ·
                      rfl

theorem cell23_3729912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 1, 5].length) (baseStart_3729912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729912 prefixEnd_3729912 := by exact prefixLift 3729912
  have htrace : WordTrace (prefixWord ++ tailWord_3729912) baseStart_3729912 baseEnd_3729912 := by
    simpa [prefixWord, tailWord_3729912, baseEnd_3729912] using wordTrace_append hprefix tailTrace_3729912
  have hstable : (prefixWord ++ tailWord_3729912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729912).length < 2 ^ (prefixWord ++ tailWord_3729912).sum := by decide
  have hdescent : baseEnd_3729912 < baseStart_3729912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729925 : List Nat := [1, 3, 1, 1, 2, 2, 2, 3, 4, 4]
def baseStart_3729925 : Nat := 118140960795 + 3729925 * 2 ^ 59
def prefixEnd_3729925 : Nat := 4983230072969 + 3 ^ 40 * 3729925 * 2
def baseEnd_3729925 : Nat := 638414776740474794994631

theorem tailTrace_3729925 : CollatzResearch.WordTrace tailWord_3729925 prefixEnd_3729925 638414776740474794994631 := by
  unfold tailWord_3729925
  simp only [CollatzResearch.WordTrace]
  refine ⟨136041541012126220319319229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90694360674750813546212819 136041541012126220319319229)
  ·
    refine ⟨51015577879547332619744711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136041541012126220319319229 51015577879547332619744711)
    ·
      refine ⟨76523366819320998929617067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51015577879547332619744711 76523366819320998929617067)
      ·
        refine ⟨114785050228981498394425601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76523366819320998929617067 114785050228981498394425601)
        ·
          refine ⟨86088787671736123795819201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114785050228981498394425601 86088787671736123795819201)
          ·
            refine ⟨64566590753802092846864401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86088787671736123795819201 64566590753802092846864401)
            ·
              refine ⟨48424943065351569635148301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64566590753802092846864401 48424943065351569635148301)
              ·
                refine ⟨18159353649506838613180613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48424943065351569635148301 18159353649506838613180613)
                ·
                  refine ⟨3404878809282532239971365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18159353649506838613180613 3404878809282532239971365)
                  ·
                    refine ⟨638414776740474794994631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3404878809282532239971365 638414776740474794994631)
                    ·
                      rfl

theorem cell23_3729925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4, 4].length) (baseStart_3729925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729925 prefixEnd_3729925 := by exact prefixLift 3729925
  have htrace : WordTrace (prefixWord ++ tailWord_3729925) baseStart_3729925 baseEnd_3729925 := by
    simpa [prefixWord, tailWord_3729925, baseEnd_3729925] using wordTrace_append hprefix tailTrace_3729925
  have hstable : (prefixWord ++ tailWord_3729925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729925).length < 2 ^ (prefixWord ++ tailWord_3729925).sum := by decide
  have hdescent : baseEnd_3729925 < baseStart_3729925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729935 : List Nat := [1, 1, 2, 1, 1, 1, 2, 6, 3, 2, 3]
def baseStart_3729935 : Nat := 118140960795 + 3729935 * 2 ^ 59
def prefixEnd_3729935 : Nat := 4983230072969 + 3 ^ 40 * 3729935 * 2
def baseEnd_3729935 : Nat := 1915249465027969345858847

theorem tailTrace_3729935 : CollatzResearch.WordTrace tailWord_3729935 prefixEnd_3729935 1915249465027969345858847 := by
  unfold tailWord_3729935
  simp only [CollatzResearch.WordTrace]
  refine ⟨136041905742089992027183259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90694603828059994684788839 136041905742089992027183259)
  ·
    refine ⟨204062858613134988040774889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136041905742089992027183259 204062858613134988040774889)
    ·
      refine ⟨153047143959851241030581167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204062858613134988040774889 153047143959851241030581167)
      ·
        refine ⟨229570715939776861545871751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153047143959851241030581167 229570715939776861545871751)
        ·
          refine ⟨344356073909665292318807627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229570715939776861545871751 344356073909665292318807627)
          ·
            refine ⟨516534110864497938478211441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344356073909665292318807627 516534110864497938478211441)
            ·
              refine ⟨387400583148373453858658581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 516534110864497938478211441 387400583148373453858658581)
              ·
                refine ⟨18159402335080005649624621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 387400583148373453858658581 18159402335080005649624621)
                ·
                  refine ⟨6809775875655002118609233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18159402335080005649624621 6809775875655002118609233)
                  ·
                    refine ⟨5107331906741251588956925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6809775875655002118609233 5107331906741251588956925)
                    ·
                      refine ⟨1915249465027969345858847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5107331906741251588956925 1915249465027969345858847)
                      ·
                        rfl

theorem cell23_3729935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2, 3].length) (baseStart_3729935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729935 prefixEnd_3729935 := by exact prefixLift 3729935
  have htrace : WordTrace (prefixWord ++ tailWord_3729935) baseStart_3729935 baseEnd_3729935 := by
    simpa [prefixWord, tailWord_3729935, baseEnd_3729935] using wordTrace_append hprefix tailTrace_3729935
  have hstable : (prefixWord ++ tailWord_3729935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729935).length < 2 ^ (prefixWord ++ tailWord_3729935).sum := by decide
  have hdescent : baseEnd_3729935 < baseStart_3729935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729949 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 5, 2, 2]
def baseStart_3729949 : Nat := 118140960795 + 3729949 * 2 ^ 59
def prefixEnd_3729949 : Nat := 4983230072969 + 3 ^ 40 * 3729949 * 2
def baseEnd_3729949 : Nat := 1915256653757132291083783

theorem tailTrace_3729949 : CollatzResearch.WordTrace tailWord_3729949 prefixEnd_3729949 1915256653757132291083783 := by
  unfold tailWord_3729949
  simp only [CollatzResearch.WordTrace]
  refine ⟨136042416364039272418192901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90694944242692848278795267 136042416364039272418192901)
  ·
    refine ⟨25507953068257363578411169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136042416364039272418192901 25507953068257363578411169)
    ·
      refine ⟨19130964801193022683808377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25507953068257363578411169 19130964801193022683808377)
      ·
        refine ⟨14348223600894767012856283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19130964801193022683808377 14348223600894767012856283)
        ·
          refine ⟨21522335401342150519284425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14348223600894767012856283 21522335401342150519284425)
          ·
            refine ⟨16141751551006612889463319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21522335401342150519284425 16141751551006612889463319)
            ·
              refine ⟨24212627326509919334194979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16141751551006612889463319 24212627326509919334194979)
              ·
                refine ⟨36318940989764879001292469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24212627326509919334194979 36318940989764879001292469)
                ·
                  refine ⟨3404900717790457406371169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36318940989764879001292469 3404900717790457406371169)
                  ·
                    refine ⟨2553675538342843054778377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3404900717790457406371169 2553675538342843054778377)
                    ·
                      refine ⟨1915256653757132291083783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2553675538342843054778377 1915256653757132291083783)
                      ·
                        rfl

theorem cell23_3729949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_3729949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729949 prefixEnd_3729949 := by exact prefixLift 3729949
  have htrace : WordTrace (prefixWord ++ tailWord_3729949) baseStart_3729949 baseEnd_3729949 := by
    simpa [prefixWord, tailWord_3729949, baseEnd_3729949] using wordTrace_append hprefix tailTrace_3729949
  have hstable : (prefixWord ++ tailWord_3729949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729949).length < 2 ^ (prefixWord ++ tailWord_3729949).sum := by decide
  have hdescent : baseEnd_3729949 < baseStart_3729949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729962 : List Nat := [3, 1, 4, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_3729962 : Nat := 118140960795 + 3729962 * 2 ^ 59
def prefixEnd_3729962 : Nat := 4983230072969 + 3 ^ 40 * 3729962 * 2
def baseEnd_3729962 : Nat := 1915263329005640740221223

theorem tailTrace_3729962 : CollatzResearch.WordTrace tailWord_3729962 prefixEnd_3729962 1915263329005640740221223 := by
  unfold tailWord_3729962
  simp only [CollatzResearch.WordTrace]
  refine ⟨34010722628248043909604035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90695260341994783758944093 34010722628248043909604035)
  ·
    refine ⟨51016083942372065864406053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34010722628248043909604035 51016083942372065864406053)
    ·
      refine ⟨9565515739194762349576135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51016083942372065864406053 9565515739194762349576135)
      ·
        refine ⟨14348273608792143524364203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9565515739194762349576135 14348273608792143524364203)
        ·
          refine ⟨21522410413188215286546305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14348273608792143524364203 21522410413188215286546305)
          ·
            refine ⟨16141807809891161464909729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21522410413188215286546305 16141807809891161464909729)
            ·
              refine ⟨12106355857418371098682297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16141807809891161464909729 12106355857418371098682297)
              ·
                refine ⟨9079766893063778324011723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12106355857418371098682297 9079766893063778324011723)
                ·
                  refine ⟨13619650339595667486017585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9079766893063778324011723 13619650339595667486017585)
                  ·
                    refine ⟨10214737754696750614513189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13619650339595667486017585 10214737754696750614513189)
                    ·
                      refine ⟨1915263329005640740221223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10214737754696750614513189 1915263329005640740221223)
                      ·
                        rfl

theorem cell23_3729962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_3729962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729962 prefixEnd_3729962 := by exact prefixLift 3729962
  have htrace : WordTrace (prefixWord ++ tailWord_3729962) baseStart_3729962 baseEnd_3729962 := by
    simpa [prefixWord, tailWord_3729962, baseEnd_3729962] using wordTrace_append hprefix tailTrace_3729962
  have hstable : (prefixWord ++ tailWord_3729962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729962).length < 2 ^ (prefixWord ++ tailWord_3729962).sum := by decide
  have hdescent : baseEnd_3729962 < baseStart_3729962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729969 : List Nat := [1, 2, 2, 3, 1, 1, 6, 1, 1, 2, 3]
def baseStart_3729969 : Nat := 118140960795 + 3729969 * 2 ^ 59
def prefixEnd_3729969 : Nat := 4983230072969 + 3 ^ 40 * 3729969 * 2
def baseEnd_3729969 : Nat := 1915266923370222212833691

theorem tailTrace_3729969 : CollatzResearch.WordTrace tailWord_3729969 prefixEnd_3729969 1915266923370222212833691 := by
  unfold tailWord_3729969
  simp only [CollatzResearch.WordTrace]
  refine ⟨136043145823966815833920961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90695430549311210555947307 136043145823966815833920961)
  ·
    refine ⟨102032359367975111875440721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136043145823966815833920961 102032359367975111875440721)
    ·
      refine ⟨76524269525981333906580541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102032359367975111875440721 76524269525981333906580541)
      ·
        refine ⟨28696601072243000214967703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76524269525981333906580541 28696601072243000214967703)
        ·
          refine ⟨43044901608364500322451555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28696601072243000214967703 43044901608364500322451555)
          ·
            refine ⟨64567352412546750483677333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43044901608364500322451555 64567352412546750483677333)
            ·
              refine ⟨3026594644338128928922375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64567352412546750483677333 3026594644338128928922375)
              ·
                refine ⟨4539891966507193393383563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3026594644338128928922375 4539891966507193393383563)
                ·
                  refine ⟨6809837949760790090075345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4539891966507193393383563 6809837949760790090075345)
                  ·
                    refine ⟨5107378462320592567556509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6809837949760790090075345 5107378462320592567556509)
                    ·
                      refine ⟨1915266923370222212833691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5107378462320592567556509 1915266923370222212833691)
                      ·
                        rfl

theorem cell23_3729969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_3729969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729969 prefixEnd_3729969 := by exact prefixLift 3729969
  have htrace : WordTrace (prefixWord ++ tailWord_3729969) baseStart_3729969 baseEnd_3729969 := by
    simpa [prefixWord, tailWord_3729969, baseEnd_3729969] using wordTrace_append hprefix tailTrace_3729969
  have hstable : (prefixWord ++ tailWord_3729969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729969).length < 2 ^ (prefixWord ++ tailWord_3729969).sum := by decide
  have hdescent : baseEnd_3729969 < baseStart_3729969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3729992 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 5, 3, 2]
def baseStart_3729992 : Nat := 118140960795 + 3729992 * 2 ^ 59
def prefixEnd_3729992 : Nat := 4983230072969 + 3 ^ 40 * 3729992 * 2
def baseEnd_3729992 : Nat := 1915278733425275622846085

theorem tailTrace_3729992 : CollatzResearch.WordTrace tailWord_3729992 prefixEnd_3729992 1915278733425275622846085 := by
  unfold tailWord_3729992
  simp only [CollatzResearch.WordTrace]
  refine ⟨68021992351441745381004115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90695989801922327174672153 68021992351441745381004115)
  ·
    refine ⟨102032988527162618071506173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68021992351441745381004115 102032988527162618071506173)
    ·
      refine ⟨38262370697685981776814815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102032988527162618071506173 38262370697685981776814815)
      ·
        refine ⟨57393556046528972665222223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38262370697685981776814815 57393556046528972665222223)
        ·
          refine ⟨86090334069793458997833335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57393556046528972665222223 86090334069793458997833335)
          ·
            refine ⟨129135501104690188496750003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86090334069793458997833335 129135501104690188496750003)
            ·
              refine ⟨193703251657035282745125005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129135501104690188496750003 193703251657035282745125005)
              ·
                refine ⟨72638719371388231029421877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193703251657035282745125005 72638719371388231029421877)
                ·
                  refine ⟨6809879941067646659008301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72638719371388231029421877 6809879941067646659008301)
                  ·
                    refine ⟨2553704977900367497128113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6809879941067646659008301 2553704977900367497128113)
                    ·
                      refine ⟨1915278733425275622846085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2553704977900367497128113 1915278733425275622846085)
                      ·
                        rfl

theorem cell23_3729992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 5, 3, 2].length) (baseStart_3729992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3729992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3729992 prefixEnd_3729992 := by exact prefixLift 3729992
  have htrace : WordTrace (prefixWord ++ tailWord_3729992) baseStart_3729992 baseEnd_3729992 := by
    simpa [prefixWord, tailWord_3729992, baseEnd_3729992] using wordTrace_append hprefix tailTrace_3729992
  have hstable : (prefixWord ++ tailWord_3729992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3729992).length < 2 ^ (prefixWord ++ tailWord_3729992).sum := by decide
  have hdescent : baseEnd_3729992 < baseStart_3729992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3729992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730005 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 2, 3, 4]
def baseStart_3730005 : Nat := 118140960795 + 3730005 * 2 ^ 59
def prefixEnd_3730005 : Nat := 4983230072969 + 3 ^ 40 * 3730005 * 2
def baseEnd_3730005 : Nat := 1915285408673784071983525

theorem tailTrace_3730005 : CollatzResearch.WordTrace tailWord_3730005 prefixEnd_3730005 1915285408673784071983525 := by
  unfold tailWord_3730005
  simp only [CollatzResearch.WordTrace]
  refine ⟨136044458851836393982231469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90696305901224262654820979 136044458851836393982231469)
  ·
    refine ⟨51016672069438647743336801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136044458851836393982231469 51016672069438647743336801)
    ·
      refine ⟨38262504052078985807502601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51016672069438647743336801 38262504052078985807502601)
      ·
        refine ⟨28696878039059239355626951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38262504052078985807502601 28696878039059239355626951)
        ·
          refine ⟨43045317058588859033440427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28696878039059239355626951 43045317058588859033440427)
          ·
            refine ⟨64567975587883288550160641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43045317058588859033440427 64567975587883288550160641)
            ·
              refine ⟨48425981690912466412620481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64567975587883288550160641 48425981690912466412620481)
              ·
                refine ⟨36319486268184349809465361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48425981690912466412620481 36319486268184349809465361)
                ·
                  refine ⟨27239614701138262357099021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36319486268184349809465361 27239614701138262357099021)
                  ·
                    refine ⟨10214855512926848383912133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27239614701138262357099021 10214855512926848383912133)
                    ·
                      refine ⟨1915285408673784071983525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10214855512926848383912133 1915285408673784071983525)
                      ·
                        rfl

theorem cell23_3730005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_3730005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730005 prefixEnd_3730005 := by exact prefixLift 3730005
  have htrace : WordTrace (prefixWord ++ tailWord_3730005) baseStart_3730005 baseEnd_3730005 := by
    simpa [prefixWord, tailWord_3730005, baseEnd_3730005] using wordTrace_append hprefix tailTrace_3730005
  have hstable : (prefixWord ++ tailWord_3730005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730005).length < 2 ^ (prefixWord ++ tailWord_3730005).sum := by decide
  have hdescent : baseEnd_3730005 < baseStart_3730005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730025 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 1, 6, 3]
def baseStart_3730025 : Nat := 118140960795 + 3730025 * 2 ^ 59
def prefixEnd_3730025 : Nat := 4983230072969 + 3 ^ 40 * 3730025 * 2
def baseEnd_3730025 : Nat := 1915295678286873993733433

theorem tailTrace_3730025 : CollatzResearch.WordTrace tailWord_3730025 prefixEnd_3730025 1915295678286873993733433 := by
  unfold tailWord_3730025
  simp only [CollatzResearch.WordTrace]
  refine ⟨136045188311763937397959529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90696792207842624931973019 136045188311763937397959529)
  ·
    refine ⟨102033891233822953048469647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136045188311763937397959529 102033891233822953048469647)
    ·
      refine ⟨153050836850734429572704471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102033891233822953048469647 153050836850734429572704471)
      ·
        refine ⟨229576255276101644359056707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153050836850734429572704471 229576255276101644359056707)
        ·
          refine ⟨344364382914152466538585061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229576255276101644359056707 344364382914152466538585061)
          ·
            refine ⟨64568321796403587475984699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 344364382914152466538585061 64568321796403587475984699)
            ·
              refine ⟨96852482694605381213977049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64568321796403587475984699 96852482694605381213977049)
              ·
                refine ⟨72639362020954035910482787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96852482694605381213977049 72639362020954035910482787)
                ·
                  refine ⟨108959043031431053865724181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72639362020954035910482787 108959043031431053865724181)
                  ·
                    refine ⟨5107455142098330649955821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108959043031431053865724181 5107455142098330649955821)
                    ·
                      refine ⟨1915295678286873993733433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5107455142098330649955821 1915295678286873993733433)
                      ·
                        rfl

theorem cell23_3730025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 6, 3].length) (baseStart_3730025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730025 prefixEnd_3730025 := by exact prefixLift 3730025
  have htrace : WordTrace (prefixWord ++ tailWord_3730025) baseStart_3730025 baseEnd_3730025 := by
    simpa [prefixWord, tailWord_3730025, baseEnd_3730025] using wordTrace_append hprefix tailTrace_3730025
  have hstable : (prefixWord ++ tailWord_3730025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730025).length < 2 ^ (prefixWord ++ tailWord_3730025).sum := by decide
  have hdescent : baseEnd_3730025 < baseStart_3730025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730035 : List Nat := [1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 4]
def baseStart_3730035 : Nat := 118140960795 + 3730035 * 2 ^ 59
def prefixEnd_3730035 : Nat := 4983230072969 + 3 ^ 40 * 3730035 * 2
def baseEnd_3730035 : Nat := 1915300813093418954608387

theorem tailTrace_3730035 : CollatzResearch.WordTrace tailWord_3730035 prefixEnd_3730035 1915300813093418954608387 := by
  unfold tailWord_3730035
  simp only [CollatzResearch.WordTrace]
  refine ⟨136045553041727709105823559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90697035361151806070549039 136045553041727709105823559)
  ·
    refine ⟨204068329562591563658735339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136045553041727709105823559 204068329562591563658735339)
    ·
      refine ⟨306102494343887345488103009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204068329562591563658735339 306102494343887345488103009)
      ·
        refine ⟨229576870757915509116077257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306102494343887345488103009 229576870757915509116077257)
        ·
          refine ⟨172182653068436631837057943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229576870757915509116077257 172182653068436631837057943)
          ·
            refine ⟨258273979602654947755586915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172182653068436631837057943 258273979602654947755586915)
            ·
              refine ⟨387410969403982421633380373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258273979602654947755586915 387410969403982421633380373)
              ·
                refine ⟨18159889190811676014064705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 387410969403982421633380373 18159889190811676014064705)
                ·
                  refine ⟨13619916893108757010548529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18159889190811676014064705 13619916893108757010548529)
                  ·
                    refine ⟨10214937669831567757911397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13619916893108757010548529 10214937669831567757911397)
                    ·
                      refine ⟨1915300813093418954608387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10214937669831567757911397 1915300813093418954608387)
                      ·
                        rfl

theorem cell23_3730035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 4].length) (baseStart_3730035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730035 prefixEnd_3730035 := by exact prefixLift 3730035
  have htrace : WordTrace (prefixWord ++ tailWord_3730035) baseStart_3730035 baseEnd_3730035 := by
    simpa [prefixWord, tailWord_3730035, baseEnd_3730035] using wordTrace_append hprefix tailTrace_3730035
  have hstable : (prefixWord ++ tailWord_3730035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730035).length < 2 ^ (prefixWord ++ tailWord_3730035).sum := by decide
  have hdescent : baseEnd_3730035 < baseStart_3730035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730039 : List Nat := [1, 1, 3, 1, 1, 3, 4, 1, 4, 2, 2]
def baseStart_3730039 : Nat := 118140960795 + 3730039 * 2 ^ 59
def prefixEnd_3730039 : Nat := 4983230072969 + 3 ^ 40 * 3730039 * 2
def baseEnd_3730039 : Nat := 1915302867016036938958369

theorem tailTrace_3730039 : CollatzResearch.WordTrace tailWord_3730039 prefixEnd_3730039 1915302867016036938958369 := by
  unfold tailWord_3730039
  simp only [CollatzResearch.WordTrace]
  refine ⟨136045698933713217788969171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90697132622475478525979447 136045698933713217788969171)
  ·
    refine ⟨204068548400569826683453757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136045698933713217788969171 204068548400569826683453757)
    ·
      refine ⟨76525705650213685006295159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204068548400569826683453757 76525705650213685006295159)
      ·
        refine ⟨114788558475320527509442739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76525705650213685006295159 114788558475320527509442739)
        ·
          refine ⟨172182837712980791264164109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114788558475320527509442739 172182837712980791264164109)
          ·
            refine ⟨64568564142367796724061541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172182837712980791264164109 64568564142367796724061541)
            ·
              refine ⟨12106605776693961885761539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64568564142367796724061541 12106605776693961885761539)
              ·
                refine ⟨18159908665040942828642309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12106605776693961885761539 18159908665040942828642309)
                ·
                  refine ⟨3404982874695176780370433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18159908665040942828642309 3404982874695176780370433)
                  ·
                    refine ⟨2553737156021382585277825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3404982874695176780370433 2553737156021382585277825)
                    ·
                      refine ⟨1915302867016036938958369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2553737156021382585277825 1915302867016036938958369)
                      ·
                        rfl

theorem cell23_3730039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4, 2, 2].length) (baseStart_3730039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730039 prefixEnd_3730039 := by exact prefixLift 3730039
  have htrace : WordTrace (prefixWord ++ tailWord_3730039) baseStart_3730039 baseEnd_3730039 := by
    simpa [prefixWord, tailWord_3730039, baseEnd_3730039] using wordTrace_append hprefix tailTrace_3730039
  have hstable : (prefixWord ++ tailWord_3730039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730039).length < 2 ^ (prefixWord ++ tailWord_3730039).sum := by decide
  have hdescent : baseEnd_3730039 < baseStart_3730039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730105 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 2, 8]
def baseStart_3730105 : Nat := 118140960795 + 3730105 * 2 ^ 59
def prefixEnd_3730105 : Nat := 4983230072969 + 3 ^ 40 * 3730105 * 2
def baseEnd_3730105 : Nat := 638445585579744560244355

theorem tailTrace_3730105 : CollatzResearch.WordTrace tailWord_3730105 prefixEnd_3730105 638445585579744560244355 := by
  unfold tailWord_3730105
  simp only [CollatzResearch.WordTrace]
  refine ⟨136048106151474111060871769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90698737434316074040581179 136048106151474111060871769)
  ·
    refine ⟨102036079613605583295653827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136048106151474111060871769 102036079613605583295653827)
    ·
      refine ⟨153054119420408374943480741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102036079613605583295653827 153054119420408374943480741)
      ·
        refine ⟨28697647391326570301902639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153054119420408374943480741 28697647391326570301902639)
        ·
          refine ⟨43046471086989855452853959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28697647391326570301902639 43046471086989855452853959)
          ·
            refine ⟨64569706630484783179280939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43046471086989855452853959 64569706630484783179280939)
            ·
              refine ⟨96854559945727174768921409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64569706630484783179280939 96854559945727174768921409)
              ·
                refine ⟨72640919959295381076691057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96854559945727174768921409 72640919959295381076691057)
                ·
                  refine ⟨54480689969471535807518293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72640919959295381076691057 54480689969471535807518293)
                  ·
                    refine ⟨638445585579744560244355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54480689969471535807518293 638445585579744560244355)
                    ·
                      rfl

theorem cell23_3730105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 8].length) (baseStart_3730105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730105 prefixEnd_3730105 := by exact prefixLift 3730105
  have htrace : WordTrace (prefixWord ++ tailWord_3730105) baseStart_3730105 baseEnd_3730105 := by
    simpa [prefixWord, tailWord_3730105, baseEnd_3730105] using wordTrace_append hprefix tailTrace_3730105
  have hstable : (prefixWord ++ tailWord_3730105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730105).length < 2 ^ (prefixWord ++ tailWord_3730105).sum := by decide
  have hdescent : baseEnd_3730105 < baseStart_3730105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730232 : List Nat := [2, 1, 2, 1, 3, 2, 1, 3, 1, 1, 6]
def baseStart_3730232 : Nat := 118140960795 + 3730232 * 2 ^ 59
def prefixEnd_3730232 : Nat := 4983230072969 + 3 ^ 40 * 3730232 * 2
def baseEnd_3730232 : Nat := 1915401968782354683844981

theorem tailTrace_3730232 : CollatzResearch.WordTrace tailWord_3730232 prefixEnd_3730232 1915401968782354683844981 := by
  unfold tailWord_3730232
  simp only [CollatzResearch.WordTrace]
  refine ⟨68026369111007005875372475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90701825481342674500496633 68026369111007005875372475)
  ·
    refine ⟨102039553666510508813058713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68026369111007005875372475 102039553666510508813058713)
    ·
      refine ⟨76529665249882881609794035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102039553666510508813058713 76529665249882881609794035)
      ·
        refine ⟨114794497874824322414691053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76529665249882881609794035 114794497874824322414691053)
        ·
          refine ⟨43047936703059120905509145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114794497874824322414691053 43047936703059120905509145)
          ·
            refine ⟨32285952527294340679131859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43047936703059120905509145 32285952527294340679131859)
            ·
              refine ⟨48428928790941511018697789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32285952527294340679131859 48428928790941511018697789)
              ·
                refine ⟨18160848296603066632011671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48428928790941511018697789 18160848296603066632011671)
                ·
                  refine ⟨27241272444904599948017507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18160848296603066632011671 27241272444904599948017507)
                  ·
                    refine ⟨40861908667356899922026261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27241272444904599948017507 40861908667356899922026261)
                    ·
                      refine ⟨1915401968782354683844981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40861908667356899922026261 1915401968782354683844981)
                      ·
                        rfl

theorem cell23_3730232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_3730232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730232 prefixEnd_3730232 := by exact prefixLift 3730232
  have htrace : WordTrace (prefixWord ++ tailWord_3730232) baseStart_3730232 baseEnd_3730232 := by
    simpa [prefixWord, tailWord_3730232, baseEnd_3730232] using wordTrace_append hprefix tailTrace_3730232
  have hstable : (prefixWord ++ tailWord_3730232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730232).length < 2 ^ (prefixWord ++ tailWord_3730232).sum := by decide
  have hdescent : baseEnd_3730232 < baseStart_3730232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730236 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 5, 2, 2]
def baseStart_3730236 : Nat := 118140960795 + 3730236 * 2 ^ 59
def prefixEnd_3730236 : Nat := 4983230072969 + 3 ^ 40 * 3730236 * 2
def baseEnd_3730236 : Nat := 1915404022704972668194963

theorem tailTrace_3730236 : CollatzResearch.WordTrace tailWord_3730236 prefixEnd_3730236 1915404022704972668194963 := by
  unfold tailWord_3730236
  simp only [CollatzResearch.WordTrace]
  refine ⟨68026442056999760216945281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90701922742666346955927041 68026442056999760216945281)
  ·
    refine ⟨51019831542749820162708961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68026442056999760216945281 51019831542749820162708961)
    ·
      refine ⟨38264873657062365122031721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51019831542749820162708961 38264873657062365122031721)
      ·
        refine ⟨28698655242796773841523791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38264873657062365122031721 28698655242796773841523791)
        ·
          refine ⟨43047982864195160762285687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28698655242796773841523791 43047982864195160762285687)
          ·
            refine ⟨64571974296292741143428531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43047982864195160762285687 64571974296292741143428531)
            ·
              refine ⟨96857961444439111715142797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64571974296292741143428531 96857961444439111715142797)
              ·
                refine ⟨36321735541664666893178549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96857961444439111715142797 36321735541664666893178549)
                ·
                  refine ⟨3405162707031062521235489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36321735541664666893178549 3405162707031062521235489)
                  ·
                    refine ⟨2553872030273296890926617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3405162707031062521235489 2553872030273296890926617)
                    ·
                      refine ⟨1915404022704972668194963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2553872030273296890926617 1915404022704972668194963)
                      ·
                        rfl

theorem cell23_3730236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_3730236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730236 prefixEnd_3730236 := by exact prefixLift 3730236
  have htrace : WordTrace (prefixWord ++ tailWord_3730236) baseStart_3730236 baseEnd_3730236 := by
    simpa [prefixWord, tailWord_3730236, baseEnd_3730236] using wordTrace_append hprefix tailTrace_3730236
  have hstable : (prefixWord ++ tailWord_3730236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730236).length < 2 ^ (prefixWord ++ tailWord_3730236).sum := by decide
  have hdescent : baseEnd_3730236 < baseStart_3730236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730249 : List Nat := [1, 2, 1, 1, 2, 6, 1, 2, 1, 2, 4]
def baseStart_3730249 : Nat := 118140960795 + 3730249 * 2 ^ 59
def prefixEnd_3730249 : Nat := 4983230072969 + 3 ^ 40 * 3730249 * 2
def baseEnd_3730249 : Nat := 1915410697953481117332403

theorem tailTrace_3730249 : CollatzResearch.WordTrace tailWord_3730249 prefixEnd_3730249 1915410697953481117332403 := by
  unfold tailWord_3730249
  simp only [CollatzResearch.WordTrace]
  refine ⟨136053358262952423654113801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90702238841968282436075867 136053358262952423654113801)
  ·
    refine ⟨102040018697214317740585351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136053358262952423654113801 102040018697214317740585351)
    ·
      refine ⟨153060028045821476610878027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102040018697214317740585351 153060028045821476610878027)
      ·
        refine ⟨229590042068732214916317041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153060028045821476610878027 229590042068732214916317041)
        ·
          refine ⟨172192531551549161187237781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229590042068732214916317041 172192531551549161187237781)
          ·
            refine ⟨8071524916478866930651771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 172192531551549161187237781 8071524916478866930651771)
            ·
              refine ⟨12107287374718300395977657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8071524916478866930651771 12107287374718300395977657)
              ·
                refine ⟨9080465531038725296983243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12107287374718300395977657 9080465531038725296983243)
                ·
                  refine ⟨13620698296558087945474865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9080465531038725296983243 13620698296558087945474865)
                  ·
                    refine ⟨10215523722418565959106149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13620698296558087945474865 10215523722418565959106149)
                    ·
                      refine ⟨1915410697953481117332403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10215523722418565959106149 1915410697953481117332403)
                      ·
                        rfl

theorem cell23_3730249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 2, 4].length) (baseStart_3730249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730249 prefixEnd_3730249 := by exact prefixLift 3730249
  have htrace : WordTrace (prefixWord ++ tailWord_3730249) baseStart_3730249 baseEnd_3730249 := by
    simpa [prefixWord, tailWord_3730249, baseEnd_3730249] using wordTrace_append hprefix tailTrace_3730249
  have hstable : (prefixWord ++ tailWord_3730249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730249).length < 2 ^ (prefixWord ++ tailWord_3730249).sum := by decide
  have hdescent : baseEnd_3730249 < baseStart_3730249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730272 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 1, 9]
def baseStart_3730272 : Nat := 118140960795 + 3730272 * 2 ^ 59
def prefixEnd_3730272 : Nat := 4983230072969 + 3 ^ 40 * 3730272 * 2
def baseEnd_3730272 : Nat := 638474169336178175781599

theorem tailTrace_3730272 : CollatzResearch.WordTrace tailWord_3730272 prefixEnd_3730272 638474169336178175781599 := by
  unfold tailWord_3730272
  simp only [CollatzResearch.WordTrace]
  refine ⟨68027098570934549291100535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90702798094579399054800713 68027098570934549291100535)
  ·
    refine ⟨102040647856401823936650803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68027098570934549291100535 102040647856401823936650803)
    ·
      refine ⟨153060971784602735904976205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102040647856401823936650803 153060971784602735904976205)
      ·
        refine ⟨57397864419226025964366077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153060971784602735904976205 57397864419226025964366077)
        ·
          refine ⟨21524199157209759736637279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57397864419226025964366077 21524199157209759736637279)
          ·
            refine ⟨32286298735814639604955919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21524199157209759736637279 32286298735814639604955919)
            ·
              refine ⟨48429448103721959407433879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32286298735814639604955919 48429448103721959407433879)
              ·
                refine ⟨72644172155582939111150819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48429448103721959407433879 72644172155582939111150819)
                ·
                  refine ⟨108966258233374408666726229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72644172155582939111150819 108966258233374408666726229)
                  ·
                    refine ⟨638474169336178175781599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 108966258233374408666726229 638474169336178175781599)
                    ·
                      rfl

theorem cell23_3730272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 1, 9].length) (baseStart_3730272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730272 prefixEnd_3730272 := by exact prefixLift 3730272
  have htrace : WordTrace (prefixWord ++ tailWord_3730272) baseStart_3730272 baseEnd_3730272 := by
    simpa [prefixWord, tailWord_3730272, baseEnd_3730272] using wordTrace_append hprefix tailTrace_3730272
  have hstable : (prefixWord ++ tailWord_3730272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730272).length < 2 ^ (prefixWord ++ tailWord_3730272).sum := by decide
  have hdescent : baseEnd_3730272 < baseStart_3730272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730313 : List Nat := [1, 2, 1, 1, 5, 3, 1, 3, 1, 3, 2]
def baseStart_3730313 : Nat := 118140960795 + 3730313 * 2 ^ 59
def prefixEnd_3730313 : Nat := 4983230072969 + 3 ^ 40 * 3730313 * 2
def baseEnd_3730313 : Nat := 1915443560715368866932109

theorem tailTrace_3730313 : CollatzResearch.WordTrace tailWord_3730313 prefixEnd_3730313 1915443560715368866932109 := by
  unfold tailWord_3730313
  simp only [CollatzResearch.WordTrace]
  refine ⟨136055692534720562584443593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90703795023147041722962395 136055692534720562584443593)
  ·
    refine ⟨102041769401040421938332695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136055692534720562584443593 102041769401040421938332695)
    ·
      refine ⟨153062654101560632907499043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102041769401040421938332695 153062654101560632907499043)
      ·
        refine ⟨229593981152340949361248565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153062654101560632907499043 229593981152340949361248565)
        ·
          refine ⟨21524435733031964002617053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 229593981152340949361248565 21524435733031964002617053)
          ·
            refine ⟨8071663399886986500981395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21524435733031964002617053 8071663399886986500981395)
            ·
              refine ⟨12107495099830479751472093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8071663399886986500981395 12107495099830479751472093)
              ·
                refine ⟨4540310662436429906802035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12107495099830479751472093 4540310662436429906802035)
                ·
                  refine ⟨6810465993654644860203053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4540310662436429906802035 6810465993654644860203053)
                  ·
                    refine ⟨2553924747620491822576145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6810465993654644860203053 2553924747620491822576145)
                    ·
                      refine ⟨1915443560715368866932109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2553924747620491822576145 1915443560715368866932109)
                      ·
                        rfl

theorem cell23_3730313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 3, 2].length) (baseStart_3730313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730313 prefixEnd_3730313 := by exact prefixLift 3730313
  have htrace : WordTrace (prefixWord ++ tailWord_3730313) baseStart_3730313 baseEnd_3730313 := by
    simpa [prefixWord, tailWord_3730313, baseEnd_3730313] using wordTrace_append hprefix tailTrace_3730313
  have hstable : (prefixWord ++ tailWord_3730313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730313).length < 2 ^ (prefixWord ++ tailWord_3730313).sum := by decide
  have hdescent : baseEnd_3730313 < baseStart_3730313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730339 : List Nat := [1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 4]
def baseStart_3730339 : Nat := 118140960795 + 3730339 * 2 ^ 59
def prefixEnd_3730339 : Nat := 4983230072969 + 3 ^ 40 * 3730339 * 2
def baseEnd_3730339 : Nat := 1915456911212385765206989

theorem tailTrace_3730339 : CollatzResearch.WordTrace tailWord_3730339 prefixEnd_3730339 1915456911212385765206989 := by
  unfold tailWord_3730339
  simp only [CollatzResearch.WordTrace]
  refine ⟨136056640832626369024890071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90704427221750912683260047 136056640832626369024890071)
  ·
    refine ⟨204084961248939553537335107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136056640832626369024890071 204084961248939553537335107)
    ·
      refine ⟨306127441873409330306002661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204084961248939553537335107 306127441873409330306002661)
      ·
        refine ⟨57398895351264249432375499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 306127441873409330306002661 57398895351264249432375499)
        ·
          refine ⟨86098343026896374148563249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57398895351264249432375499 86098343026896374148563249)
          ·
            refine ⟨64573757270172280611422437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86098343026896374148563249 64573757270172280611422437)
            ·
              refine ⟨12107579488157302614641707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64573757270172280611422437 12107579488157302614641707)
              ·
                refine ⟨18161369232235953921962561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12107579488157302614641707 18161369232235953921962561)
                ·
                  refine ⟨13621026924176965441471921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18161369232235953921962561 13621026924176965441471921)
                  ·
                    refine ⟨10215770193132724081103941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13621026924176965441471921 10215770193132724081103941)
                    ·
                      refine ⟨1915456911212385765206989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10215770193132724081103941 1915456911212385765206989)
                      ·
                        rfl

theorem cell23_3730339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_3730339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730339 prefixEnd_3730339 := by exact prefixLift 3730339
  have htrace : WordTrace (prefixWord ++ tailWord_3730339) baseStart_3730339 baseEnd_3730339 := by
    simpa [prefixWord, tailWord_3730339, baseEnd_3730339] using wordTrace_append hprefix tailTrace_3730339
  have hstable : (prefixWord ++ tailWord_3730339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730339).length < 2 ^ (prefixWord ++ tailWord_3730339).sum := by decide
  have hdescent : baseEnd_3730339 < baseStart_3730339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730359 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 1, 5, 3]
def baseStart_3730359 : Nat := 118140960795 + 3730359 * 2 ^ 59
def prefixEnd_3730359 : Nat := 4983230072969 + 3 ^ 40 * 3730359 * 2
def baseEnd_3730359 : Nat := 1915467180825475686956897

theorem tailTrace_3730359 : CollatzResearch.WordTrace tailWord_3730359 prefixEnd_3730359 1915467180825475686956897 := by
  unfold tailWord_3730359
  simp only [CollatzResearch.WordTrace]
  refine ⟨136057370292553912440618131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90704913528369274960412087 136057370292553912440618131)
  ·
    refine ⟨204086055438830868660927197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136057370292553912440618131 204086055438830868660927197)
    ·
      refine ⟨76532270789561575747847699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204086055438830868660927197 76532270789561575747847699)
      ·
        refine ⟨114798406184342363621771549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76532270789561575747847699 114798406184342363621771549)
        ·
          refine ⟨43049402319128386358164331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114798406184342363621771549 43049402319128386358164331)
          ·
            refine ⟨64574103478692579537246497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43049402319128386358164331 64574103478692579537246497)
            ·
              refine ⟨48430577609019434652934873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64574103478692579537246497 48430577609019434652934873)
              ·
                refine ⟨36322933206764575989701155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48430577609019434652934873 36322933206764575989701155)
                ·
                  refine ⟨54484399810146863984551733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36322933206764575989701155 54484399810146863984551733)
                  ·
                    refine ⟨5107912482201268498551725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54484399810146863984551733 5107912482201268498551725)
                    ·
                      refine ⟨1915467180825475686956897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5107912482201268498551725 1915467180825475686956897)
                      ·
                        rfl

theorem cell23_3730359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5, 3].length) (baseStart_3730359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730359 prefixEnd_3730359 := by exact prefixLift 3730359
  have htrace : WordTrace (prefixWord ++ tailWord_3730359) baseStart_3730359 baseEnd_3730359 := by
    simpa [prefixWord, tailWord_3730359, baseEnd_3730359] using wordTrace_append hprefix tailTrace_3730359
  have hstable : (prefixWord ++ tailWord_3730359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730359).length < 2 ^ (prefixWord ++ tailWord_3730359).sum := by decide
  have hdescent : baseEnd_3730359 < baseStart_3730359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730379 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 4, 5]
def baseStart_3730379 : Nat := 118140960795 + 3730379 * 2 ^ 59
def prefixEnd_3730379 : Nat := 4983230072969 + 3 ^ 40 * 3730379 * 2
def baseEnd_3730379 : Nat := 638492483479521869568935

theorem tailTrace_3730379 : CollatzResearch.WordTrace tailWord_3730379 prefixEnd_3730379 638492483479521869568935 := by
  unfold tailWord_3730379
  simp only [CollatzResearch.WordTrace]
  refine ⟨136058099752481455856346191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90705399834987637237564127 136058099752481455856346191)
  ·
    refine ⟨204087149628722183784519287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136058099752481455856346191 204087149628722183784519287)
    ·
      refine ⟨306130724443083275676778931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204087149628722183784519287 306130724443083275676778931)
      ·
        refine ⟨459196086664624913515168397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306130724443083275676778931 459196086664624913515168397)
        ·
          refine ⟨172198532499234342568188149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 459196086664624913515168397 172198532499234342568188149)
          ·
            refine ⟨16143612421803219615767639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 172198532499234342568188149 16143612421803219615767639)
            ·
              refine ⟨24215418632704829423651459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16143612421803219615767639 24215418632704829423651459)
              ·
                refine ⟨36323127949057244135477189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24215418632704829423651459 36323127949057244135477189)
                ·
                  refine ⟨6810586490448233275401973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36323127949057244135477189 6810586490448233275401973)
                  ·
                    refine ⟨638492483479521869568935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6810586490448233275401973 638492483479521869568935)
                    ·
                      rfl

theorem cell23_3730379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 5].length) (baseStart_3730379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730379 prefixEnd_3730379 := by exact prefixLift 3730379
  have htrace : WordTrace (prefixWord ++ tailWord_3730379) baseStart_3730379 baseEnd_3730379 := by
    simpa [prefixWord, tailWord_3730379, baseEnd_3730379] using wordTrace_append hprefix tailTrace_3730379
  have hstable : (prefixWord ++ tailWord_3730379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730379).length < 2 ^ (prefixWord ++ tailWord_3730379).sum := by decide
  have hdescent : baseEnd_3730379 < baseStart_3730379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730383 : List Nat := [1, 1, 2, 1, 1, 7, 3, 2, 5]
def baseStart_3730383 : Nat := 118140960795 + 3730383 * 2 ^ 59
def prefixEnd_3730383 : Nat := 4983230072969 + 3 ^ 40 * 3730383 * 2
def baseEnd_3730383 : Nat := 212831056040131510339643

theorem tailTrace_3730383 : CollatzResearch.WordTrace tailWord_3730383 prefixEnd_3730383 212831056040131510339643 := by
  unfold tailWord_3730383
  simp only [CollatzResearch.WordTrace]
  refine ⟨136058245644466964539491803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90705497096311309692994535 136058245644466964539491803)
  ·
    refine ⟨204087368466700446809237705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136058245644466964539491803 204087368466700446809237705)
    ·
      refine ⟨153065526350025335106928279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204087368466700446809237705 153065526350025335106928279)
      ·
        refine ⟨229598289525038002660392419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153065526350025335106928279 229598289525038002660392419)
        ·
          refine ⟨344397434287557003990588629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229598289525038002660392419 344397434287557003990588629)
          ·
            refine ⟨8071814866114617281029421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 344397434287557003990588629 8071814866114617281029421)
            ·
              refine ⟨3026930574792981480386033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8071814866114617281029421 3026930574792981480386033)
              ·
                refine ⟨2270197931094736110289525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3026930574792981480386033 2270197931094736110289525)
                ·
                  refine ⟨212831056040131510339643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2270197931094736110289525 212831056040131510339643)
                  ·
                    rfl

theorem cell23_3730383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2, 5].length) (baseStart_3730383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730383 prefixEnd_3730383 := by exact prefixLift 3730383
  have htrace : WordTrace (prefixWord ++ tailWord_3730383) baseStart_3730383 baseEnd_3730383 := by
    simpa [prefixWord, tailWord_3730383, baseEnd_3730383] using wordTrace_append hprefix tailTrace_3730383
  have hstable : (prefixWord ++ tailWord_3730383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730383).length < 2 ^ (prefixWord ++ tailWord_3730383).sum := by decide
  have hdescent : baseEnd_3730383 < baseStart_3730383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730416 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 4, 4, 2]
def baseStart_3730416 : Nat := 118140960795 + 3730416 * 2 ^ 59
def prefixEnd_3730416 : Nat := 4983230072969 + 3 ^ 40 * 3730416 * 2
def baseEnd_3730416 : Nat := 1915496449222781963944135

theorem tailTrace_3730416 : CollatzResearch.WordTrace tailWord_3730416 prefixEnd_3730416 1915496449222781963944135 := by
  unfold tailWord_3730416
  simp only [CollatzResearch.WordTrace]
  refine ⟨68029724626673705587721551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90706299502231607450295401 68029724626673705587721551)
  ·
    refine ⟨102044586940010558381582327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68029724626673705587721551 102044586940010558381582327)
    ·
      refine ⟨153066880410015837572373491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102044586940010558381582327 153066880410015837572373491)
      ·
        refine ⟨229600320615023756358560237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153066880410015837572373491 229600320615023756358560237)
        ·
          refine ⟨86100120230633908634460089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229600320615023756358560237 86100120230633908634460089)
          ·
            refine ⟨64575090172975431475845067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86100120230633908634460089 64575090172975431475845067)
            ·
              refine ⟨96862635259463147213767601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64575090172975431475845067 96862635259463147213767601)
              ·
                refine ⟨72646976444597360410325701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96862635259463147213767601 72646976444597360410325701)
                ·
                  refine ⟨13621308083362005076936069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72646976444597360410325701 13621308083362005076936069)
                  ·
                    refine ⟨2553995265630375951925513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13621308083362005076936069 2553995265630375951925513)
                    ·
                      refine ⟨1915496449222781963944135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2553995265630375951925513 1915496449222781963944135)
                      ·
                        rfl

theorem cell23_3730416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 4, 4, 2].length) (baseStart_3730416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730416 prefixEnd_3730416 := by exact prefixLift 3730416
  have htrace : WordTrace (prefixWord ++ tailWord_3730416) baseStart_3730416 baseEnd_3730416 := by
    simpa [prefixWord, tailWord_3730416, baseEnd_3730416] using wordTrace_append hprefix tailTrace_3730416
  have hstable : (prefixWord ++ tailWord_3730416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730416).length < 2 ^ (prefixWord ++ tailWord_3730416).sum := by decide
  have hdescent : baseEnd_3730416 < baseStart_3730416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730429 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 2, 1, 6]
def baseStart_3730429 : Nat := 118140960795 + 3730429 * 2 ^ 59
def prefixEnd_3730429 : Nat := 4983230072969 + 3 ^ 40 * 3730429 * 2
def baseEnd_3730429 : Nat := 1915503124471290413081575

theorem tailTrace_3730429 : CollatzResearch.WordTrace tailWord_3730429 prefixEnd_3730429 1915503124471290413081575 := by
  unfold tailWord_3730429
  simp only [CollatzResearch.WordTrace]
  refine ⟨136059923402300314395666341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90706615601533542930444227 136059923402300314395666341)
  ·
    refine ⟨25511235637931308949187439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136059923402300314395666341 25511235637931308949187439)
    ·
      refine ⟨38266853456896963423781159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25511235637931308949187439 38266853456896963423781159)
      ·
        refine ⟨57400280185345445135671739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38266853456896963423781159 57400280185345445135671739)
        ·
          refine ⟨86100420278018167703507609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57400280185345445135671739 86100420278018167703507609)
          ·
            refine ⟨64575315208513625777630707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86100420278018167703507609 64575315208513625777630707)
            ·
              refine ⟨96862972812770438666446061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64575315208513625777630707 96862972812770438666446061)
              ·
                refine ⟨36323614804788914499917273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96862972812770438666446061 36323614804788914499917273)
                ·
                  refine ⟨27242711103591685874937955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36323614804788914499917273 27242711103591685874937955)
                  ·
                    refine ⟨40864066655387528812406933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27242711103591685874937955 40864066655387528812406933)
                    ·
                      refine ⟨1915503124471290413081575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40864066655387528812406933 1915503124471290413081575)
                      ·
                        rfl

theorem cell23_3730429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_3730429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730429 prefixEnd_3730429 := by exact prefixLift 3730429
  have htrace : WordTrace (prefixWord ++ tailWord_3730429) baseStart_3730429 baseEnd_3730429 := by
    simpa [prefixWord, tailWord_3730429, baseEnd_3730429] using wordTrace_append hprefix tailTrace_3730429
  have hstable : (prefixWord ++ tailWord_3730429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730429).length < 2 ^ (prefixWord ++ tailWord_3730429).sum := by decide
  have hdescent : baseEnd_3730429 < baseStart_3730429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730434 : List Nat := [3, 4, 1, 3, 1, 2, 2, 2, 5]
def baseStart_3730434 : Nat := 118140960795 + 3730434 * 2 ^ 59
def prefixEnd_3730434 : Nat := 4983230072969 + 3 ^ 40 * 3730434 * 2
def baseEnd_3730434 : Nat := 212833965763840321502117

theorem tailTrace_3730434 : CollatzResearch.WordTrace tailWord_3730434 prefixEnd_3730434 212833965763840321502117 := by
  unfold tailWord_3730434
  simp only [CollatzResearch.WordTrace]
  refine ⟨34015026441820550062399589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90706737178188133499732237 34015026441820550062399589)
  ·
    refine ⟨6377817457841353136699923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34015026441820550062399589 6377817457841353136699923)
    ·
      refine ⟨9566726186762029705049885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6377817457841353136699923 9566726186762029705049885)
      ·
        refine ⟨3587522320035761139393707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9566726186762029705049885 3587522320035761139393707)
        ·
          refine ⟨5381283480053641709090561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3587522320035761139393707 5381283480053641709090561)
          ·
            refine ⟨4035962610040231281817921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5381283480053641709090561 4035962610040231281817921)
            ·
              refine ⟨3026971957530173461363441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4035962610040231281817921 3026971957530173461363441)
              ·
                refine ⟨2270228968147630096022581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3026971957530173461363441 2270228968147630096022581)
                ·
                  refine ⟨212833965763840321502117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2270228968147630096022581 212833965763840321502117)
                  ·
                    rfl

theorem cell23_3730434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_3730434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730434 prefixEnd_3730434 := by exact prefixLift 3730434
  have htrace : WordTrace (prefixWord ++ tailWord_3730434) baseStart_3730434 baseEnd_3730434 := by
    simpa [prefixWord, tailWord_3730434, baseEnd_3730434] using wordTrace_append hprefix tailTrace_3730434
  have hstable : (prefixWord ++ tailWord_3730434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730434).length < 2 ^ (prefixWord ++ tailWord_3730434).sum := by decide
  have hdescent : baseEnd_3730434 < baseStart_3730434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730456 : List Nat := [2, 1, 2, 3, 2, 2, 2, 3, 6]
def baseStart_3730456 : Nat := 118140960795 + 3730456 * 2 ^ 59
def prefixEnd_3730456 : Nat := 4983230072969 + 3 ^ 40 * 3730456 * 2
def baseEnd_3730456 : Nat := 212835220938773534160439

theorem tailTrace_3730456 : CollatzResearch.WordTrace tailWord_3730456 prefixEnd_3730456 212835220938773534160439 := by
  unfold tailWord_3730456
  simp only [CollatzResearch.WordTrace]
  refine ⟨68030454086601249003449611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90707272115468332004599481 68030454086601249003449611)
  ·
    refine ⟨102045681129901873505174417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68030454086601249003449611 102045681129901873505174417)
    ·
      refine ⟨76534260847426405128880813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102045681129901873505174417 76534260847426405128880813)
      ·
        refine ⟨28700347817784901923330305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76534260847426405128880813 28700347817784901923330305)
        ·
          refine ⟨21525260863338676442497729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28700347817784901923330305 21525260863338676442497729)
          ·
            refine ⟨16143945647504007331873297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21525260863338676442497729 16143945647504007331873297)
            ·
              refine ⟨12107959235628005498904973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16143945647504007331873297 12107959235628005498904973)
              ·
                refine ⟨4540484713360502062089365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12107959235628005498904973 4540484713360502062089365)
                ·
                  refine ⟨212835220938773534160439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4540484713360502062089365 212835220938773534160439)
                  ·
                    rfl

theorem cell23_3730456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 6].length) (baseStart_3730456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730456 prefixEnd_3730456 := by exact prefixLift 3730456
  have htrace : WordTrace (prefixWord ++ tailWord_3730456) baseStart_3730456 baseEnd_3730456 := by
    simpa [prefixWord, tailWord_3730456, baseEnd_3730456] using wordTrace_append hprefix tailTrace_3730456
  have hstable : (prefixWord ++ tailWord_3730456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730456).length < 2 ^ (prefixWord ++ tailWord_3730456).sum := by decide
  have hdescent : baseEnd_3730456 < baseStart_3730456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730506 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 5, 1, 4]
def baseStart_3730506 : Nat := 118140960795 + 3730506 * 2 ^ 59
def prefixEnd_3730506 : Nat := 4983230072969 + 3 ^ 40 * 3730506 * 2
def baseEnd_3730506 : Nat := 1915542662481686611818721

theorem tailTrace_3730506 : CollatzResearch.WordTrace tailWord_3730506 prefixEnd_3730506 1915542662481686611818721 := by
  unfold tailWord_3730506
  simp only [CollatzResearch.WordTrace]
  refine ⟨34015682955755339136554843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90708487882014237697479581 34015682955755339136554843)
  ·
    refine ⟨51023524433633008704832265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34015682955755339136554843 51023524433633008704832265)
    ·
      refine ⟨38267643325224756528624199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51023524433633008704832265 38267643325224756528624199)
      ·
        refine ⟨57401464987837134792936299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38267643325224756528624199 57401464987837134792936299)
        ·
          refine ⟨86102197481755702189404449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57401464987837134792936299 86102197481755702189404449)
          ·
            refine ⟨64576648111316776642053337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86102197481755702189404449 64576648111316776642053337)
            ·
              refine ⟨48432486083487582481540003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64576648111316776642053337 48432486083487582481540003)
              ·
                refine ⟨72648729125231373722310005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48432486083487582481540003 72648729125231373722310005)
                ·
                  refine ⟨6810818355490441286466563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72648729125231373722310005 6810818355490441286466563)
                  ·
                    refine ⟨10216227533235661929699845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6810818355490441286466563 10216227533235661929699845)
                    ·
                      refine ⟨1915542662481686611818721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10216227533235661929699845 1915542662481686611818721)
                      ·
                        rfl

theorem cell23_3730506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_3730506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730506 prefixEnd_3730506 := by exact prefixLift 3730506
  have htrace : WordTrace (prefixWord ++ tailWord_3730506) baseStart_3730506 baseEnd_3730506 := by
    simpa [prefixWord, tailWord_3730506, baseEnd_3730506] using wordTrace_append hprefix tailTrace_3730506
  have hstable : (prefixWord ++ tailWord_3730506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730506).length < 2 ^ (prefixWord ++ tailWord_3730506).sum := by decide
  have hdescent : baseEnd_3730506 < baseStart_3730506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730543 : List Nat := [1, 1, 2, 1, 3, 3, 1, 5, 1, 2, 3]
def baseStart_3730543 : Nat := 118140960795 + 3730543 * 2 ^ 59
def prefixEnd_3730543 : Nat := 4983230072969 + 3 ^ 40 * 3730543 * 2
def baseEnd_3730543 : Nat := 1915561661265902967056051

theorem tailTrace_3730543 : CollatzResearch.WordTrace tailWord_3730543 prefixEnd_3730543 1915561661265902967056051 := by
  unfold tailWord_3730543
  simp only [CollatzResearch.WordTrace]
  refine ⟨136064081323887311865316283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90709387549258207910210855 136064081323887311865316283)
  ·
    refine ⟨204096121985830967797974425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136064081323887311865316283 204096121985830967797974425)
    ·
      refine ⟨153072091489373225848480819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204096121985830967797974425 153072091489373225848480819)
      ·
        refine ⟨229608137234059838772721229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153072091489373225848480819 229608137234059838772721229)
        ·
          refine ⟨86103051462772439539770461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229608137234059838772721229 86103051462772439539770461)
          ·
            refine ⟨32288644298539664827413923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86103051462772439539770461 32288644298539664827413923)
            ·
              refine ⟨48432966447809497241120885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32288644298539664827413923 48432966447809497241120885)
              ·
                refine ⟨4540590604482140366355083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48432966447809497241120885 4540590604482140366355083)
                ·
                  refine ⟨6810885906723210549532625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4540590604482140366355083 6810885906723210549532625)
                  ·
                    refine ⟨5108164430042407912149469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6810885906723210549532625 5108164430042407912149469)
                    ·
                      refine ⟨1915561661265902967056051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5108164430042407912149469 1915561661265902967056051)
                      ·
                        rfl

theorem cell23_3730543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 2, 3].length) (baseStart_3730543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730543 prefixEnd_3730543 := by exact prefixLift 3730543
  have htrace : WordTrace (prefixWord ++ tailWord_3730543) baseStart_3730543 baseEnd_3730543 := by
    simpa [prefixWord, tailWord_3730543, baseEnd_3730543] using wordTrace_append hprefix tailTrace_3730543
  have hstable : (prefixWord ++ tailWord_3730543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730543).length < 2 ^ (prefixWord ++ tailWord_3730543).sum := by decide
  have hdescent : baseEnd_3730543 < baseStart_3730543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730550 : List Nat := [5, 1, 1, 2, 1, 1, 2, 4, 2, 4]
def baseStart_3730550 : Nat := 118140960795 + 3730550 * 2 ^ 59
def prefixEnd_3730550 : Nat := 4983230072969 + 3 ^ 40 * 3730550 * 2
def baseEnd_3730550 : Nat := 638521751876828146556173

theorem tailTrace_3730550 : CollatzResearch.WordTrace tailWord_3730550 prefixEnd_3730550 638521751876828146556173 := by
  unfold tailWord_3730550
  simp only [CollatzResearch.WordTrace]
  refine ⟨8504021039678872003801319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90709557756574634707214069 8504021039678872003801319)
  ·
    refine ⟨12756031559518308005701979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8504021039678872003801319 12756031559518308005701979)
    ·
      refine ⟨19134047339277462008552969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12756031559518308005701979 19134047339277462008552969)
      ·
        refine ⟨14350535504458096506414727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19134047339277462008552969 14350535504458096506414727)
        ·
          refine ⟨21525803256687144759622091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14350535504458096506414727 21525803256687144759622091)
          ·
            refine ⟨32288704885030717139433137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21525803256687144759622091 32288704885030717139433137)
            ·
              refine ⟨24216528663773037854574853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32288704885030717139433137 24216528663773037854574853)
              ·
                refine ⟨4540599124457444597732785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24216528663773037854574853 4540599124457444597732785)
                ·
                  refine ⟨3405449343343083448299589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4540599124457444597732785 3405449343343083448299589)
                  ·
                    refine ⟨638521751876828146556173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3405449343343083448299589 638521751876828146556173)
                    ·
                      rfl

theorem cell23_3730550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_3730550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730550 prefixEnd_3730550 := by exact prefixLift 3730550
  have htrace : WordTrace (prefixWord ++ tailWord_3730550) baseStart_3730550 baseEnd_3730550 := by
    simpa [prefixWord, tailWord_3730550, baseEnd_3730550] using wordTrace_append hprefix tailTrace_3730550
  have hstable : (prefixWord ++ tailWord_3730550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730550).length < 2 ^ (prefixWord ++ tailWord_3730550).sum := by decide
  have hdescent : baseEnd_3730550 < baseStart_3730550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730590 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_3730590 : Nat := 118140960795 + 3730590 * 2 ^ 59
def prefixEnd_3730590 : Nat := 4983230072969 + 3 ^ 40 * 3730590 * 2
def baseEnd_3730590 : Nat := 1915585794856664283168335

theorem tailTrace_3730590 : CollatzResearch.WordTrace tailWord_3730590 prefixEnd_3730590 1915585794856664283168335 := by
  unfold tailWord_3730590
  simp only [CollatzResearch.WordTrace]
  refine ⟨17008224444339629861534653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90710530369811359261518149 17008224444339629861534653)
  ·
    refine ⟨6378084166627361198075495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17008224444339629861534653 6378084166627361198075495)
    ·
      refine ⟨9567126249941041797113243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6378084166627361198075495 9567126249941041797113243)
      ·
        refine ⟨14350689374911562695669865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9567126249941041797113243 14350689374911562695669865)
        ·
          refine ⟨10763017031183672021752399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14350689374911562695669865 10763017031183672021752399)
          ·
            refine ⟨16144525546775508032628599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10763017031183672021752399 16144525546775508032628599)
            ·
              refine ⟨24216788320163262048942899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16144525546775508032628599 24216788320163262048942899)
              ·
                refine ⟨36325182480244893073414349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24216788320163262048942899 36325182480244893073414349)
                ·
                  refine ⟨13621943430091834902530381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36325182480244893073414349 13621943430091834902530381)
                  ·
                    refine ⟨5108228786284438088448893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13621943430091834902530381 5108228786284438088448893)
                    ·
                      refine ⟨1915585794856664283168335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5108228786284438088448893 1915585794856664283168335)
                      ·
                        rfl

theorem cell23_3730590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_3730590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730590 prefixEnd_3730590 := by exact prefixLift 3730590
  have htrace : WordTrace (prefixWord ++ tailWord_3730590) baseStart_3730590 baseEnd_3730590 := by
    simpa [prefixWord, tailWord_3730590, baseEnd_3730590] using wordTrace_append hprefix tailTrace_3730590
  have hstable : (prefixWord ++ tailWord_3730590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730590).length < 2 ^ (prefixWord ++ tailWord_3730590).sum := by decide
  have hdescent : baseEnd_3730590 < baseStart_3730590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730594 : List Nat := [3, 3, 1, 3, 2, 1, 3, 1, 1, 2, 3]
def baseStart_3730594 : Nat := 118140960795 + 3730594 * 2 ^ 59
def prefixEnd_3730594 : Nat := 4983230072969 + 3 ^ 40 * 3730594 * 2
def baseEnd_3730594 : Nat := 1915587848779282267518317

theorem tailTrace_3730594 : CollatzResearch.WordTrace tailWord_3730594 prefixEnd_3730594 1915587848779282267518317 := by
  unfold tailWord_3730594
  simp only [CollatzResearch.WordTrace]
  refine ⟨34016485361675636893855709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90710627631135031716948557 34016485361675636893855709)
  ·
    refine ⟨12756182010628363835195891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34016485361675636893855709 12756182010628363835195891)
    ·
      refine ⟨19134273015942545752793837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12756182010628363835195891 19134273015942545752793837)
      ·
        refine ⟨7175352380978454657297689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19134273015942545752793837 7175352380978454657297689)
        ·
          refine ⟨5381514285733840992973267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7175352380978454657297689 5381514285733840992973267)
          ·
            refine ⟨8072271428600761489459901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5381514285733840992973267 8072271428600761489459901)
            ·
              refine ⟨3027101785725285558547463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8072271428600761489459901 3027101785725285558547463)
              ·
                refine ⟨4540652678587928337821195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3027101785725285558547463 4540652678587928337821195)
                ·
                  refine ⟨6810979017881892506731793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4540652678587928337821195 6810979017881892506731793)
                  ·
                    refine ⟨5108234263411419380048845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6810979017881892506731793 5108234263411419380048845)
                    ·
                      refine ⟨1915587848779282267518317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5108234263411419380048845 1915587848779282267518317)
                      ·
                        rfl

theorem cell23_3730594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_3730594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730594 prefixEnd_3730594 := by exact prefixLift 3730594
  have htrace : WordTrace (prefixWord ++ tailWord_3730594) baseStart_3730594 baseEnd_3730594 := by
    simpa [prefixWord, tailWord_3730594, baseEnd_3730594] using wordTrace_append hprefix tailTrace_3730594
  have hstable : (prefixWord ++ tailWord_3730594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730594).length < 2 ^ (prefixWord ++ tailWord_3730594).sum := by decide
  have hdescent : baseEnd_3730594 < baseStart_3730594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730614 : List Nat := [5, 1, 3, 2, 2, 1, 1, 8]
def baseStart_3730614 : Nat := 118140960795 + 3730614 * 2 ^ 59
def prefixEnd_3730614 : Nat := 4983230072969 + 3 ^ 40 * 3730614 * 2
def baseEnd_3730614 : Nat := 70948078458976747750675

theorem tailTrace_3730614 : CollatzResearch.WordTrace tailWord_3730614 prefixEnd_3730614 70948078458976747750675 := by
  unfold tailWord_3730614
  simp only [CollatzResearch.WordTrace]
  refine ⟨8504166931664380686946931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90711113937753393994100597 8504166931664380686946931)
  ·
    refine ⟨12756250397496571030420397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8504166931664380686946931 12756250397496571030420397)
    ·
      refine ⟨4783593899061214136407649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12756250397496571030420397 4783593899061214136407649)
      ·
        refine ⟨3587695424295910602305737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4783593899061214136407649 3587695424295910602305737)
        ·
          refine ⟨2690771568221932951729303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3587695424295910602305737 2690771568221932951729303)
          ·
            refine ⟨4036157352332899427593955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2690771568221932951729303 4036157352332899427593955)
            ·
              refine ⟨6054236028499349141390933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4036157352332899427593955 6054236028499349141390933)
              ·
                refine ⟨70948078458976747750675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6054236028499349141390933 70948078458976747750675)
                ·
                  rfl

theorem cell23_3730614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_3730614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730614 prefixEnd_3730614 := by exact prefixLift 3730614
  have htrace : WordTrace (prefixWord ++ tailWord_3730614) baseStart_3730614 baseEnd_3730614 := by
    simpa [prefixWord, tailWord_3730614, baseEnd_3730614] using wordTrace_append hprefix tailTrace_3730614
  have hstable : (prefixWord ++ tailWord_3730614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730614).length < 2 ^ (prefixWord ++ tailWord_3730614).sum := by decide
  have hdescent : baseEnd_3730614 < baseStart_3730614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730616 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 4, 1, 5]
def baseStart_3730616 : Nat := 118140960795 + 3730616 * 2 ^ 59
def prefixEnd_3730616 : Nat := 4983230072969 + 3 ^ 40 * 3730616 * 2
def baseEnd_3730616 : Nat := 1915599145353681181443215

theorem tailTrace_3730616 : CollatzResearch.WordTrace tailWord_3730616 prefixEnd_3730616 1915599145353681181443215 := by
  unfold tailWord_3730616
  simp only [CollatzResearch.WordTrace]
  refine ⟨68033371926311422666361851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90711162568415230221815801 68033371926311422666361851)
  ·
    refine ⟨102050057889467133999542777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68033371926311422666361851 102050057889467133999542777)
    ·
      refine ⟨76537543417100350499657083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102050057889467133999542777 76537543417100350499657083)
      ·
        refine ⟨114806315125650525749485625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76537543417100350499657083 114806315125650525749485625)
        ·
          refine ⟨86104736344237894312114219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114806315125650525749485625 86104736344237894312114219)
          ·
            refine ⟨129157104516356841468171329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86104736344237894312114219 129157104516356841468171329)
            ·
              refine ⟨96867828387267631101128497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129157104516356841468171329 96867828387267631101128497)
              ·
                refine ⟨72650871290450723325846373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96867828387267631101128497 72650871290450723325846373)
                ·
                  refine ⟨13622038366959510623596195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72650871290450723325846373 13622038366959510623596195)
                  ·
                    refine ⟨20433057550439265935394293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13622038366959510623596195 20433057550439265935394293)
                    ·
                      refine ⟨1915599145353681181443215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20433057550439265935394293 1915599145353681181443215)
                      ·
                        rfl

theorem cell23_3730616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_3730616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730616 prefixEnd_3730616 := by exact prefixLift 3730616
  have htrace : WordTrace (prefixWord ++ tailWord_3730616) baseStart_3730616 baseEnd_3730616 := by
    simpa [prefixWord, tailWord_3730616, baseEnd_3730616] using wordTrace_append hprefix tailTrace_3730616
  have hstable : (prefixWord ++ tailWord_3730616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730616).length < 2 ^ (prefixWord ++ tailWord_3730616).sum := by decide
  have hdescent : baseEnd_3730616 < baseStart_3730616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730670 : List Nat := [4, 1, 2, 1, 1, 1, 4, 4, 5]
def baseStart_3730670 : Nat := 118140960795 + 3730670 * 2 ^ 59
def prefixEnd_3730670 : Nat := 4983230072969 + 3 ^ 40 * 3730670 * 2
def baseEnd_3730670 : Nat := 212847430367669330018663

theorem tailTrace_3730670 : CollatzResearch.WordTrace tailWord_3730670 prefixEnd_3730670 212847430367669330018663 := by
  unfold tailWord_3730670
  simp only [CollatzResearch.WordTrace]
  refine ⟨17008589174303401569398683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90712475596284808370126309 17008589174303401569398683)
  ·
    refine ⟨25512883761455102354098025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17008589174303401569398683 25512883761455102354098025)
    ·
      refine ⟨19134662821091326765573519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25512883761455102354098025 19134662821091326765573519)
      ·
        refine ⟨28701994231636990148360279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19134662821091326765573519 28701994231636990148360279)
        ·
          refine ⟨43052991347455485222540419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28701994231636990148360279 43052991347455485222540419)
          ·
            refine ⟨64579487021183227833810629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43052991347455485222540419 64579487021183227833810629)
            ·
              refine ⟨12108653816471855218839493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64579487021183227833810629 12108653816471855218839493)
              ·
                refine ⟨2270372590588472853532405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12108653816471855218839493 2270372590588472853532405)
                ·
                  refine ⟨212847430367669330018663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2270372590588472853532405 212847430367669330018663)
                  ·
                    rfl

theorem cell23_3730670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4, 5].length) (baseStart_3730670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730670 prefixEnd_3730670 := by exact prefixLift 3730670
  have htrace : WordTrace (prefixWord ++ tailWord_3730670) baseStart_3730670 baseEnd_3730670 := by
    simpa [prefixWord, tailWord_3730670, baseEnd_3730670] using wordTrace_append hprefix tailTrace_3730670
  have hstable : (prefixWord ++ tailWord_3730670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730670).length < 2 ^ (prefixWord ++ tailWord_3730670).sum := by decide
  have hdescent : baseEnd_3730670 < baseStart_3730670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730810 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2]
def baseStart_3730810 : Nat := 118140960795 + 3730810 * 2 ^ 59
def prefixEnd_3730810 : Nat := 4983230072969 + 3 ^ 40 * 3730810 * 2
def baseEnd_3730810 : Nat := 1915698760600653422417323

theorem tailTrace_3730810 : CollatzResearch.WordTrace tailWord_3730810 prefixEnd_3730810 1915698760600653422417323 := by
  unfold tailWord_3730810
  simp only [CollatzResearch.WordTrace]
  refine ⟨34018454903480004116321471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90715879742613344310190589 34018454903480004116321471)
  ·
    refine ⟨51027682355220006174482207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34018454903480004116321471 51027682355220006174482207)
    ·
      refine ⟨76541523532830009261723311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51027682355220006174482207 76541523532830009261723311)
      ·
        refine ⟨114812285299245013892584967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76541523532830009261723311 114812285299245013892584967)
        ·
          refine ⟨172218427948867520838877451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114812285299245013892584967 172218427948867520838877451)
          ·
            refine ⟨258327641923301281258316177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172218427948867520838877451 258327641923301281258316177)
            ·
              refine ⟨193745731442475960943737133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258327641923301281258316177 193745731442475960943737133)
              ·
                refine ⟨72654649290928485353901425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193745731442475960943737133 72654649290928485353901425)
                ·
                  refine ⟨54490986968196364015426069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72654649290928485353901425 54490986968196364015426069)
                  ·
                    refine ⟨2554265014134204563223097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54490986968196364015426069 2554265014134204563223097)
                    ·
                      refine ⟨1915698760600653422417323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2554265014134204563223097 1915698760600653422417323)
                      ·
                        rfl

theorem cell23_3730810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2].length) (baseStart_3730810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730810 prefixEnd_3730810 := by exact prefixLift 3730810
  have htrace : WordTrace (prefixWord ++ tailWord_3730810) baseStart_3730810 baseEnd_3730810 := by
    simpa [prefixWord, tailWord_3730810, baseEnd_3730810] using wordTrace_append hprefix tailTrace_3730810
  have hstable : (prefixWord ++ tailWord_3730810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730810).length < 2 ^ (prefixWord ++ tailWord_3730810).sum := by decide
  have hdescent : baseEnd_3730810 < baseStart_3730810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730820 : List Nat := [2, 3, 2, 1, 1, 3, 2, 2, 1, 6]
def baseStart_3730820 : Nat := 118140960795 + 3730820 * 2 ^ 59
def prefixEnd_3730820 : Nat := 4983230072969 + 3 ^ 40 * 3730820 * 2
def baseEnd_3730820 : Nat := 638567965135732794430759

theorem tailTrace_3730820 : CollatzResearch.WordTrace tailWord_3730820 prefixEnd_3730820 638567965135732794430759 := by
  unfold tailWord_3730820
  simp only [CollatzResearch.WordTrace]
  refine ⟨68037092171941894086574957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90716122895922525448766609 68037092171941894086574957)
  ·
    refine ⟨25513909564478210282465609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68037092171941894086574957 25513909564478210282465609)
    ·
      refine ⟨19135432173358657711849207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25513909564478210282465609 19135432173358657711849207)
      ·
        refine ⟨28703148260037986567773811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19135432173358657711849207 28703148260037986567773811)
        ·
          refine ⟨43054722390056979851660717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28703148260037986567773811 43054722390056979851660717)
          ·
            refine ⟨16145520896271367444372769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43054722390056979851660717 16145520896271367444372769)
            ·
              refine ⟨12109140672203525583279577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16145520896271367444372769 12109140672203525583279577)
              ·
                refine ⟨9081855504152644187459683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12109140672203525583279577 9081855504152644187459683)
                ·
                  refine ⟨13622783256228966281189525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9081855504152644187459683 13622783256228966281189525)
                  ·
                    refine ⟨638567965135732794430759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13622783256228966281189525 638567965135732794430759)
                    ·
                      rfl

theorem cell23_3730820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_3730820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730820 prefixEnd_3730820 := by exact prefixLift 3730820
  have htrace : WordTrace (prefixWord ++ tailWord_3730820) baseStart_3730820 baseEnd_3730820 := by
    simpa [prefixWord, tailWord_3730820, baseEnd_3730820] using wordTrace_append hprefix tailTrace_3730820
  have hstable : (prefixWord ++ tailWord_3730820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730820).length < 2 ^ (prefixWord ++ tailWord_3730820).sum := by decide
  have hdescent : baseEnd_3730820 < baseStart_3730820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730824 : List Nat := [2, 1, 3, 3, 1, 4, 2, 1, 1, 5]
def baseStart_3730824 : Nat := 118140960795 + 3730824 * 2 ^ 59
def prefixEnd_3730824 : Nat := 4983230072969 + 3 ^ 40 * 3730824 * 2
def baseEnd_3730824 : Nat := 638568649776605455880753

theorem tailTrace_3730824 : CollatzResearch.WordTrace tailWord_3730824 prefixEnd_3730824 638568649776605455880753 := by
  unfold tailWord_3730824
  simp only [CollatzResearch.WordTrace]
  refine ⟨68037165117934648428147763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90716220157246197904197017 68037165117934648428147763)
  ·
    refine ⟨102055747676901972642221645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68037165117934648428147763 102055747676901972642221645)
    ·
      refine ⟨38270905378838239740833117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102055747676901972642221645 38270905378838239740833117)
      ·
        refine ⟨14351589517064339902812419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38270905378838239740833117 14351589517064339902812419)
        ·
          refine ⟨21527384275596509854218629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14351589517064339902812419 21527384275596509854218629)
          ·
            refine ⟨4036384551674345597665993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21527384275596509854218629 4036384551674345597665993)
            ·
              refine ⟨3027288413755759198249495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4036384551674345597665993 3027288413755759198249495)
              ·
                refine ⟨4540932620633638797374243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3027288413755759198249495 4540932620633638797374243)
                ·
                  refine ⟨6811398930950458196061365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4540932620633638797374243 6811398930950458196061365)
                  ·
                    refine ⟨638568649776605455880753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6811398930950458196061365 638568649776605455880753)
                    ·
                      rfl

theorem cell23_3730824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_3730824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730824 prefixEnd_3730824 := by exact prefixLift 3730824
  have htrace : WordTrace (prefixWord ++ tailWord_3730824) baseStart_3730824 baseEnd_3730824 := by
    simpa [prefixWord, tailWord_3730824, baseEnd_3730824] using wordTrace_append hprefix tailTrace_3730824
  have hstable : (prefixWord ++ tailWord_3730824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730824).length < 2 ^ (prefixWord ++ tailWord_3730824).sum := by decide
  have hdescent : baseEnd_3730824 < baseStart_3730824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730827 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 5, 2, 2]
def baseStart_3730827 : Nat := 118140960795 + 3730827 * 2 ^ 59
def prefixEnd_3730827 : Nat := 4983230072969 + 3 ^ 40 * 3730827 * 2
def baseEnd_3730827 : Nat := 1915707489771779855904745

theorem tailTrace_3730827 : CollatzResearch.WordTrace tailWord_3730827 prefixEnd_3730827 1915707489771779855904745 := by
  unfold tailWord_3730827
  simp only [CollatzResearch.WordTrace]
  refine ⟨136074439654858428368654735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90716293103238952245769823 136074439654858428368654735)
  ·
    refine ⟨204111659482287642552982103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136074439654858428368654735 204111659482287642552982103)
    ·
      refine ⟨306167489223431463829473155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204111659482287642552982103 306167489223431463829473155)
      ·
        refine ⟨459251233835147195744209733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306167489223431463829473155 459251233835147195744209733)
        ·
          refine ⟨86109606344090099202039325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 459251233835147195744209733 86109606344090099202039325)
          ·
            refine ⟨32291102379033787200764747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86109606344090099202039325 32291102379033787200764747)
            ·
              refine ⟨48436653568550680801147121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32291102379033787200764747 48436653568550680801147121)
              ·
                refine ⟨36327490176413010600860341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48436653568550680801147121 36327490176413010600860341)
                ·
                  refine ⟨3405702204038719743830657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36327490176413010600860341 3405702204038719743830657)
                  ·
                    refine ⟨2554276653029039807872993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3405702204038719743830657 2554276653029039807872993)
                    ·
                      refine ⟨1915707489771779855904745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2554276653029039807872993 1915707489771779855904745)
                      ·
                        rfl

theorem cell23_3730827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5, 2, 2].length) (baseStart_3730827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730827 prefixEnd_3730827 := by exact prefixLift 3730827
  have htrace : WordTrace (prefixWord ++ tailWord_3730827) baseStart_3730827 baseEnd_3730827 := by
    simpa [prefixWord, tailWord_3730827, baseEnd_3730827] using wordTrace_append hprefix tailTrace_3730827
  have hstable : (prefixWord ++ tailWord_3730827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730827).length < 2 ^ (prefixWord ++ tailWord_3730827).sum := by decide
  have hdescent : baseEnd_3730827 < baseStart_3730827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730837 : List Nat := [1, 3, 2, 1, 1, 2, 5, 2, 2, 4]
def baseStart_3730837 : Nat := 118140960795 + 3730837 * 2 ^ 59
def prefixEnd_3730837 : Nat := 4983230072969 + 3 ^ 40 * 3730837 * 2
def baseEnd_3730837 : Nat := 638570874859441605593233

theorem tailTrace_3730837 : CollatzResearch.WordTrace tailWord_3730837 prefixEnd_3730837 638570874859441605593233 := by
  unfold tailWord_3730837
  simp only [CollatzResearch.WordTrace]
  refine ⟨136074804384822200076518765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90716536256548133384345843 136074804384822200076518765)
  ·
    refine ⟨51028051644308325028694537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136074804384822200076518765 51028051644308325028694537)
    ·
      refine ⟨38271038733231243771520903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51028051644308325028694537 38271038733231243771520903)
      ·
        refine ⟨57406558099846865657281355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38271038733231243771520903 57406558099846865657281355)
        ·
          refine ⟨86109837149770298485922033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57406558099846865657281355 86109837149770298485922033)
          ·
            refine ⟨64582377862327723864441525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86109837149770298485922033 64582377862327723864441525)
            ·
              refine ⟨6054597924593224112291393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64582377862327723864441525 6054597924593224112291393)
              ·
                refine ⟨4540948443444918084218545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6054597924593224112291393 4540948443444918084218545)
                ·
                  refine ⟨3405711332583688563163909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4540948443444918084218545 3405711332583688563163909)
                  ·
                    refine ⟨638570874859441605593233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3405711332583688563163909 638570874859441605593233)
                    ·
                      rfl

theorem cell23_3730837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_3730837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730837 prefixEnd_3730837 := by exact prefixLift 3730837
  have htrace : WordTrace (prefixWord ++ tailWord_3730837) baseStart_3730837 baseEnd_3730837 := by
    simpa [prefixWord, tailWord_3730837, baseEnd_3730837] using wordTrace_append hprefix tailTrace_3730837
  have hstable : (prefixWord ++ tailWord_3730837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730837).length < 2 ^ (prefixWord ++ tailWord_3730837).sum := by decide
  have hdescent : baseEnd_3730837 < baseStart_3730837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730853 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 1, 4, 6]
def baseStart_3730853 : Nat := 118140960795 + 3730853 * 2 ^ 59
def prefixEnd_3730853 : Nat := 4983230072969 + 3 ^ 40 * 3730853 * 2
def baseEnd_3730853 : Nat := 1915720840268796754179625

theorem tailTrace_3730853 : CollatzResearch.WordTrace tailWord_3730853 prefixEnd_3730853 1915720840268796754179625 := by
  unfold tailWord_3730853
  simp only [CollatzResearch.WordTrace]
  refine ⟨136075387952764234809101213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90716925301842823206067475 136075387952764234809101213)
  ·
    refine ⟨51028270482286588053412955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136075387952764234809101213 51028270482286588053412955)
    ·
      refine ⟨76542405723429882080119433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51028270482286588053412955 76542405723429882080119433)
      ·
        refine ⟨57406804292572411560089575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76542405723429882080119433 57406804292572411560089575)
        ·
          refine ⟨86110206438858617340134363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57406804292572411560089575 86110206438858617340134363)
          ·
            refine ⟨129165309658287926010201545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86110206438858617340134363 129165309658287926010201545)
            ·
              refine ⟨96873982243715944507651159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129165309658287926010201545 96873982243715944507651159)
              ·
                refine ⟨145310973365573916761476739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96873982243715944507651159 145310973365573916761476739)
                ·
                  refine ⟨217966460048360875142215109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145310973365573916761476739 217966460048360875142215109)
                  ·
                    refine ⟨40868711259067664089165333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 217966460048360875142215109 40868711259067664089165333)
                    ·
                      refine ⟨1915720840268796754179625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40868711259067664089165333 1915720840268796754179625)
                      ·
                        rfl

theorem cell23_3730853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_3730853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730853 prefixEnd_3730853 := by exact prefixLift 3730853
  have htrace : WordTrace (prefixWord ++ tailWord_3730853) baseStart_3730853 baseEnd_3730853 := by
    simpa [prefixWord, tailWord_3730853, baseEnd_3730853] using wordTrace_append hprefix tailTrace_3730853
  have hstable : (prefixWord ++ tailWord_3730853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730853).length < 2 ^ (prefixWord ++ tailWord_3730853).sum := by decide
  have hdescent : baseEnd_3730853 < baseStart_3730853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730861 : List Nat := [1, 5, 2, 2, 1, 1, 2, 2, 3, 2, 2]
def baseStart_3730861 : Nat := 118140960795 + 3730861 * 2 ^ 59
def prefixEnd_3730861 : Nat := 4983230072969 + 3 ^ 40 * 3730861 * 2
def baseEnd_3730861 : Nat := 1915724948114032722879589

theorem tailTrace_3730861 : CollatzResearch.WordTrace tailWord_3730861 prefixEnd_3730861 1915724948114032722879589 := by
  unfold tailWord_3730861
  simp only [CollatzResearch.WordTrace]
  refine ⟨136075679736735252175392437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90717119824490168116928291 136075679736735252175392437)
  ·
    refine ⟨12757094975318929891443041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136075679736735252175392437 12757094975318929891443041)
    ·
      refine ⟨9567821231489197418582281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12757094975318929891443041 9567821231489197418582281)
      ·
        refine ⟨7175865923616898063936711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9567821231489197418582281 7175865923616898063936711)
        ·
          refine ⟨10763798885425347095905067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7175865923616898063936711 10763798885425347095905067)
          ·
            refine ⟨16145698328138020643857601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10763798885425347095905067 16145698328138020643857601)
            ·
              refine ⟨12109273746103515482893201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16145698328138020643857601 12109273746103515482893201)
              ·
                refine ⟨9081955309577636612169901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12109273746103515482893201 9081955309577636612169901)
                ·
                  refine ⟨3405733241091613729563713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9081955309577636612169901 3405733241091613729563713)
                  ·
                    refine ⟨2554299930818710297172785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3405733241091613729563713 2554299930818710297172785)
                    ·
                      refine ⟨1915724948114032722879589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2554299930818710297172785 1915724948114032722879589)
                      ·
                        rfl

theorem cell23_3730861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_3730861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730861 prefixEnd_3730861 := by exact prefixLift 3730861
  have htrace : WordTrace (prefixWord ++ tailWord_3730861) baseStart_3730861 baseEnd_3730861 := by
    simpa [prefixWord, tailWord_3730861, baseEnd_3730861] using wordTrace_append hprefix tailTrace_3730861
  have hstable : (prefixWord ++ tailWord_3730861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730861).length < 2 ^ (prefixWord ++ tailWord_3730861).sum := by decide
  have hdescent : baseEnd_3730861 < baseStart_3730861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730863 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 2, 7]
def baseStart_3730863 : Nat := 118140960795 + 3730863 * 2 ^ 59
def prefixEnd_3730863 : Nat := 4983230072969 + 3 ^ 40 * 3730863 * 2
def baseEnd_3730863 : Nat := 638575325025113905018193

theorem tailTrace_3730863 : CollatzResearch.WordTrace tailWord_3730863 prefixEnd_3730863 638575325025113905018193 := by
  unfold tailWord_3730863
  simp only [CollatzResearch.WordTrace]
  refine ⟨136075752682728006516965243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90717168455152004344643495 136075752682728006516965243)
  ·
    refine ⟨204113629024092009775447865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136075752682728006516965243 204113629024092009775447865)
    ·
      refine ⟨153085221768069007331585899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204113629024092009775447865 153085221768069007331585899)
      ·
        refine ⟨229627832652103510997378849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153085221768069007331585899 229627832652103510997378849)
        ·
          refine ⟨172220874489077633248034137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229627832652103510997378849 172220874489077633248034137)
          ·
            refine ⟨129165655866808224936025603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172220874489077633248034137 129165655866808224936025603)
            ·
              refine ⟨193748483800212337404038405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129165655866808224936025603 193748483800212337404038405)
              ·
                refine ⟨36327840712539813263257201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193748483800212337404038405 36327840712539813263257201)
                ·
                  refine ⟨27245880534404859947442901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36327840712539813263257201 27245880534404859947442901)
                  ·
                    refine ⟨638575325025113905018193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27245880534404859947442901 638575325025113905018193)
                    ·
                      rfl

theorem cell23_3730863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 7].length) (baseStart_3730863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730863 prefixEnd_3730863 := by exact prefixLift 3730863
  have htrace : WordTrace (prefixWord ++ tailWord_3730863) baseStart_3730863 baseEnd_3730863 := by
    simpa [prefixWord, tailWord_3730863, baseEnd_3730863] using wordTrace_append hprefix tailTrace_3730863
  have hstable : (prefixWord ++ tailWord_3730863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730863).length < 2 ^ (prefixWord ++ tailWord_3730863).sum := by decide
  have hdescent : baseEnd_3730863 < baseStart_3730863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730877 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 6, 1, 3]
def baseStart_3730877 : Nat := 118140960795 + 3730877 * 2 ^ 59
def prefixEnd_3730877 : Nat := 4983230072969 + 3 ^ 40 * 3730877 * 2
def baseEnd_3730877 : Nat := 1915733163804504660279515

theorem tailTrace_3730877 : CollatzResearch.WordTrace tailWord_3730877 prefixEnd_3730877 1915733163804504660279515 := by
  unfold tailWord_3730877
  simp only [CollatzResearch.WordTrace]
  refine ⟨136076263304677286907974885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90717508869784857938649923 136076263304677286907974885)
  ·
    refine ⟨25514299369626991295245291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136076263304677286907974885 25514299369626991295245291)
    ·
      refine ⟨38271449054440486942867937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25514299369626991295245291 38271449054440486942867937)
      ·
        refine ⟨28703586790830365207150953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38271449054440486942867937 28703586790830365207150953)
        ·
          refine ⟨21527690093122773905363215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28703586790830365207150953 21527690093122773905363215)
          ·
            refine ⟨32291535139684160858044823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21527690093122773905363215 32291535139684160858044823)
            ·
              refine ⟨48437302709526241287067235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32291535139684160858044823 48437302709526241287067235)
              ·
                refine ⟨72655954064289361930600853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48437302709526241287067235 72655954064289361930600853)
                ·
                  refine ⟨3405747846763563840496915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72655954064289361930600853 3405747846763563840496915)
                  ·
                    refine ⟨5108621770145345760745373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3405747846763563840496915 5108621770145345760745373)
                    ·
                      refine ⟨1915733163804504660279515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5108621770145345760745373 1915733163804504660279515)
                      ·
                        rfl

theorem cell23_3730877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_3730877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730877 prefixEnd_3730877 := by exact prefixLift 3730877
  have htrace : WordTrace (prefixWord ++ tailWord_3730877) baseStart_3730877 baseEnd_3730877 := by
    simpa [prefixWord, tailWord_3730877, baseEnd_3730877] using wordTrace_append hprefix tailTrace_3730877
  have hstable : (prefixWord ++ tailWord_3730877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730877).length < 2 ^ (prefixWord ++ tailWord_3730877).sum := by decide
  have hdescent : baseEnd_3730877 < baseStart_3730877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730920 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_3730920 : Nat := 118140960795 + 3730920 * 2 ^ 59
def prefixEnd_3730920 : Nat := 4983230072969 + 3 ^ 40 * 3730920 * 2
def baseEnd_3730920 : Nat := 1915755243472647992041817

theorem tailTrace_3730920 : CollatzResearch.WordTrace tailWord_3730920 prefixEnd_3730920 1915755243472647992041817 := by
  unfold tailWord_3730920
  simp only [CollatzResearch.WordTrace]
  refine ⟨68038915821760752625895107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90718554429014336834526809 68038915821760752625895107)
  ·
    refine ⟨102058373732641128938842661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68038915821760752625895107 102058373732641128938842661)
    ·
      refine ⟨19135945074870211676032999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102058373732641128938842661 19135945074870211676032999)
      ·
        refine ⟨28703917612305317514049499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19135945074870211676032999 28703917612305317514049499)
        ·
          refine ⟨43055876418457976271074249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28703917612305317514049499 43055876418457976271074249)
          ·
            refine ⟨32291907313843482203305687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43055876418457976271074249 32291907313843482203305687)
            ·
              refine ⟨48437860970765223304958531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32291907313843482203305687 48437860970765223304958531)
              ·
                refine ⟨72656791456147834957437797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48437860970765223304958531 72656791456147834957437797)
                ·
                  refine ⟨13623148398027719054519587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72656791456147834957437797 13623148398027719054519587)
                  ·
                    refine ⟨20434722597041578581779381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13623148398027719054519587 20434722597041578581779381)
                    ·
                      refine ⟨1915755243472647992041817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20434722597041578581779381 1915755243472647992041817)
                      ·
                        rfl

theorem cell23_3730920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_3730920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730920 prefixEnd_3730920 := by exact prefixLift 3730920
  have htrace : WordTrace (prefixWord ++ tailWord_3730920) baseStart_3730920 baseEnd_3730920 := by
    simpa [prefixWord, tailWord_3730920, baseEnd_3730920] using wordTrace_append hprefix tailTrace_3730920
  have hstable : (prefixWord ++ tailWord_3730920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730920).length < 2 ^ (prefixWord ++ tailWord_3730920).sum := by decide
  have hdescent : baseEnd_3730920 < baseStart_3730920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730934 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2]
def baseStart_3730934 : Nat := 118140960795 + 3730934 * 2 ^ 59
def prefixEnd_3730934 : Nat := 4983230072969 + 3 ^ 40 * 3730934 * 2
def baseEnd_3730934 : Nat := 1915762432201810937266753

theorem tailTrace_3730934 : CollatzResearch.WordTrace tailWord_3730934 prefixEnd_3730934 1915762432201810937266753 := by
  unfold tailWord_3730934
  simp only [CollatzResearch.WordTrace]
  refine ⟨8504896391591924102674991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90718894843647190428533237 8504896391591924102674991)
  ·
    refine ⟨12757344587387886154012487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8504896391591924102674991 12757344587387886154012487)
    ·
      refine ⟨19136016881081829231018731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12757344587387886154012487 19136016881081829231018731)
      ·
        refine ⟨28704025321622743846528097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19136016881081829231018731 28704025321622743846528097)
        ·
          refine ⟨21528018991217057884896073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28704025321622743846528097 21528018991217057884896073)
          ·
            refine ⟨16146014243412793413672055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21528018991217057884896073 16146014243412793413672055)
            ·
              refine ⟨24219021365119190120508083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16146014243412793413672055 24219021365119190120508083)
              ·
                refine ⟨36328532047678785180762125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24219021365119190120508083 36328532047678785180762125)
                ·
                  refine ⟨13623199517879544442785797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36328532047678785180762125 13623199517879544442785797)
                  ·
                    refine ⟨2554349909602414583022337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13623199517879544442785797 2554349909602414583022337)
                    ·
                      refine ⟨1915762432201810937266753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2554349909602414583022337 1915762432201810937266753)
                      ·
                        rfl

theorem cell23_3730934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_3730934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730934 prefixEnd_3730934 := by exact prefixLift 3730934
  have htrace : WordTrace (prefixWord ++ tailWord_3730934) baseStart_3730934 baseEnd_3730934 := by
    simpa [prefixWord, tailWord_3730934, baseEnd_3730934] using wordTrace_append hprefix tailTrace_3730934
  have hstable : (prefixWord ++ tailWord_3730934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730934).length < 2 ^ (prefixWord ++ tailWord_3730934).sum := by decide
  have hdescent : baseEnd_3730934 < baseStart_3730934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730951 : List Nat := [1, 1, 4, 3, 2, 1, 1, 4, 2, 2, 2]
def baseStart_3730951 : Nat := 118140960795 + 3730951 * 2 ^ 59
def prefixEnd_3730951 : Nat := 4983230072969 + 3 ^ 40 * 3730951 * 2
def baseEnd_3730951 : Nat := 1915771161372937370754175

theorem tailTrace_3730951 : CollatzResearch.WordTrace tailWord_3730951 prefixEnd_3730951 1915771161372937370754175 := by
  unfold tailWord_3730951
  simp only [CollatzResearch.WordTrace]
  refine ⟨136078962306409197546168707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90719308204272798364112471 136078962306409197546168707)
  ·
    refine ⟨204118443459613796319253061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136078962306409197546168707 204118443459613796319253061)
    ·
      refine ⟨38272208148677586809859949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204118443459613796319253061 38272208148677586809859949)
      ·
        refine ⟨14352078055754095053697481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38272208148677586809859949 14352078055754095053697481)
        ·
          refine ⟨10764058541815571290273111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14352078055754095053697481 10764058541815571290273111)
          ·
            refine ⟨16146087812723356935409667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10764058541815571290273111 16146087812723356935409667)
            ·
              refine ⟨24219131719085035403114501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16146087812723356935409667 24219131719085035403114501)
              ·
                refine ⟨4541087197328444138083969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24219131719085035403114501 4541087197328444138083969)
                ·
                  refine ⟨3405815397996333103562977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4541087197328444138083969 3405815397996333103562977)
                  ·
                    refine ⟨2554361548497249827672233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3405815397996333103562977 2554361548497249827672233)
                    ·
                      refine ⟨1915771161372937370754175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2554361548497249827672233 1915771161372937370754175)
                      ·
                        rfl

theorem cell23_3730951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_3730951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730951 prefixEnd_3730951 := by exact prefixLift 3730951
  have htrace : WordTrace (prefixWord ++ tailWord_3730951) baseStart_3730951 baseEnd_3730951 := by
    simpa [prefixWord, tailWord_3730951, baseEnd_3730951] using wordTrace_append hprefix tailTrace_3730951
  have hstable : (prefixWord ++ tailWord_3730951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730951).length < 2 ^ (prefixWord ++ tailWord_3730951).sum := by decide
  have hdescent : baseEnd_3730951 < baseStart_3730951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3730970 : List Nat := [3, 1, 1, 3, 1, 1, 1, 4, 1, 7]
def baseStart_3730970 : Nat := 118140960795 + 3730970 * 2 ^ 59
def prefixEnd_3730970 : Nat := 4983230072969 + 3 ^ 40 * 3730970 * 2
def baseEnd_3730970 : Nat := 638593639168457598805529

theorem tailTrace_3730970 : CollatzResearch.WordTrace tailWord_3730970 prefixEnd_3730970 638593639168457598805529 := by
  unfold tailWord_3730970
  simp only [CollatzResearch.WordTrace]
  refine ⟨34019913823335090947777591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90719770195560242527406909 34019913823335090947777591)
  ·
    refine ⟨51029870735002636421666387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34019913823335090947777591 51029870735002636421666387)
    ·
      refine ⟨76544806102503954632499581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51029870735002636421666387 76544806102503954632499581)
      ·
        refine ⟨28704302288438982987187343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76544806102503954632499581 28704302288438982987187343)
        ·
          refine ⟨43056453432658474480781015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28704302288438982987187343 43056453432658474480781015)
          ·
            refine ⟨64584680148987711721171523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43056453432658474480781015 64584680148987711721171523)
            ·
              refine ⟨96877020223481567581757285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64584680148987711721171523 96877020223481567581757285)
              ·
                refine ⟨18164441291902793921579491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96877020223481567581757285 18164441291902793921579491)
                ·
                  refine ⟨27246661937854190882369237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18164441291902793921579491 27246661937854190882369237)
                  ·
                    refine ⟨638593639168457598805529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27246661937854190882369237 638593639168457598805529)
                    ·
                      rfl

theorem cell23_3730970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 1, 7].length) (baseStart_3730970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3730970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3730970 prefixEnd_3730970 := by exact prefixLift 3730970
  have htrace : WordTrace (prefixWord ++ tailWord_3730970) baseStart_3730970 baseEnd_3730970 := by
    simpa [prefixWord, tailWord_3730970, baseEnd_3730970] using wordTrace_append hprefix tailTrace_3730970
  have hstable : (prefixWord ++ tailWord_3730970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3730970).length < 2 ^ (prefixWord ++ tailWord_3730970).sum := by decide
  have hdescent : baseEnd_3730970 < baseStart_3730970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3730970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731061 : List Nat := [1, 3, 4, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_3731061 : Nat := 118140960795 + 3731061 * 2 ^ 59
def prefixEnd_3731061 : Nat := 4983230072969 + 3 ^ 40 * 3731061 * 2
def baseEnd_3731061 : Nat := 1915827644244931940378669

theorem tailTrace_3731061 : CollatzResearch.WordTrace tailWord_3731061 prefixEnd_3731061 1915827644244931940378669 := by
  unfold tailWord_3731061
  simp only [CollatzResearch.WordTrace]
  refine ⟨136082974336010686332673037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90721982890673790888448691 136082974336010686332673037)
  ·
    refine ⟨51031115376004007374752389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136082974336010686332673037 51031115376004007374752389)
    ·
      refine ⟨9568334133000751382766073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51031115376004007374752389 9568334133000751382766073)
      ·
        refine ⟨7176250599750563537074555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9568334133000751382766073 7176250599750563537074555)
        ·
          refine ⟨10764375899625845305611833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7176250599750563537074555 10764375899625845305611833)
          ·
            refine ⟨8073281924719383979208875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10764375899625845305611833 8073281924719383979208875)
            ·
              refine ⟨12109922887079075968813313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8073281924719383979208875 12109922887079075968813313)
              ·
                refine ⟨9082442165309306976609985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12109922887079075968813313 9082442165309306976609985)
                ·
                  refine ⟨6811831623981980232457489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9082442165309306976609985 6811831623981980232457489)
                  ·
                    refine ⟨5108873717986485174343117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6811831623981980232457489 5108873717986485174343117)
                    ·
                      refine ⟨1915827644244931940378669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5108873717986485174343117 1915827644244931940378669)
                      ·
                        rfl

theorem cell23_3731061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_3731061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731061 prefixEnd_3731061 := by exact prefixLift 3731061
  have htrace : WordTrace (prefixWord ++ tailWord_3731061) baseStart_3731061 baseEnd_3731061 := by
    simpa [prefixWord, tailWord_3731061, baseEnd_3731061] using wordTrace_append hprefix tailTrace_3731061
  have hstable : (prefixWord ++ tailWord_3731061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731061).length < 2 ^ (prefixWord ++ tailWord_3731061).sum := by decide
  have hdescent : baseEnd_3731061 < baseStart_3731061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731077 : List Nat := [1, 3, 1, 1, 4, 1, 2, 2, 3, 5]
def baseStart_3731077 : Nat := 118140960795 + 3731077 * 2 ^ 59
def prefixEnd_3731077 : Nat := 4983230072969 + 3 ^ 40 * 3731077 * 2
def baseEnd_3731077 : Nat := 638611953311801292592865

theorem tailTrace_3731077 : CollatzResearch.WordTrace tailWord_3731077 prefixEnd_3731077 638611953311801292592865 := by
  unfold tailWord_3731077
  simp only [CollatzResearch.WordTrace]
  refine ⟨136083557903952721065255485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90722371935968480710170323 136083557903952721065255485)
  ·
    refine ⟨51031334213982270399470807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136083557903952721065255485 51031334213982270399470807)
    ·
      refine ⟨76547001320973405599206211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51031334213982270399470807 76547001320973405599206211)
      ·
        refine ⟨114820501981460108398809317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76547001320973405599206211 114820501981460108398809317)
        ·
          refine ⟨21528844121523770324776747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114820501981460108398809317 21528844121523770324776747)
          ·
            refine ⟨32293266182285655487165121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21528844121523770324776747 32293266182285655487165121)
            ·
              refine ⟨24219949636714241615373841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32293266182285655487165121 24219949636714241615373841)
              ·
                refine ⟨18164962227535681211530381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24219949636714241615373841 18164962227535681211530381)
                ·
                  refine ⟨6811860835325880454323893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18164962227535681211530381 6811860835325880454323893)
                  ·
                    refine ⟨638611953311801292592865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6811860835325880454323893 638611953311801292592865)
                    ·
                      rfl

theorem cell23_3731077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 5].length) (baseStart_3731077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731077 prefixEnd_3731077 := by exact prefixLift 3731077
  have htrace : WordTrace (prefixWord ++ tailWord_3731077) baseStart_3731077 baseEnd_3731077 := by
    simpa [prefixWord, tailWord_3731077, baseEnd_3731077] using wordTrace_append hprefix tailTrace_3731077
  have hstable : (prefixWord ++ tailWord_3731077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731077).length < 2 ^ (prefixWord ++ tailWord_3731077).sum := by decide
  have hdescent : baseEnd_3731077 < baseStart_3731077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731084 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 4, 3, 2]
def baseStart_3731084 : Nat := 118140960795 + 3731084 * 2 ^ 59
def prefixEnd_3731084 : Nat := 4983230072969 + 3 ^ 40 * 3731084 * 2
def baseEnd_3731084 : Nat := 1915839454299985350391063

theorem tailTrace_3731084 : CollatzResearch.WordTrace tailWord_3731084 prefixEnd_3731084 1915839454299985350391063 := by
  unfold tailWord_3731084
  simp only [CollatzResearch.WordTrace]
  refine ⟨68041906607463680630380153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90722542143284907507173537 68041906607463680630380153)
  ·
    refine ⟨51031429955597760472785115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68041906607463680630380153 51031429955597760472785115)
    ·
      refine ⟨76547144933396640709177673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51031429955597760472785115 76547144933396640709177673)
      ·
        refine ⟨57410358700047480531883255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76547144933396640709177673 57410358700047480531883255)
        ·
          refine ⟨86115538050071220797824883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57410358700047480531883255 86115538050071220797824883)
          ·
            refine ⟨129173307075106831196737325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86115538050071220797824883 129173307075106831196737325)
            ·
              refine ⟨48439990153165061698776497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129173307075106831196737325 48439990153165061698776497)
              ·
                refine ⟨36329992614873796274082373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48439990153165061698776497 36329992614873796274082373)
                ·
                  refine ⟨6811873615288836801390445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36329992614873796274082373 6811873615288836801390445)
                  ·
                    refine ⟨2554452605733313800521417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6811873615288836801390445 2554452605733313800521417)
                    ·
                      refine ⟨1915839454299985350391063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2554452605733313800521417 1915839454299985350391063)
                      ·
                        rfl

theorem cell23_3731084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 4, 3, 2].length) (baseStart_3731084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731084 prefixEnd_3731084 := by exact prefixLift 3731084
  have htrace : WordTrace (prefixWord ++ tailWord_3731084) baseStart_3731084 baseEnd_3731084 := by
    simpa [prefixWord, tailWord_3731084, baseEnd_3731084] using wordTrace_append hprefix tailTrace_3731084
  have hstable : (prefixWord ++ tailWord_3731084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731084).length < 2 ^ (prefixWord ++ tailWord_3731084).sum := by decide
  have hdescent : baseEnd_3731084 < baseStart_3731084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731107 : List Nat := [1, 1, 1, 4, 1, 1, 5, 2, 1, 6]
def baseStart_3731107 : Nat := 118140960795 + 3731107 * 2 ^ 59
def prefixEnd_3731107 : Nat := 4983230072969 + 3 ^ 40 * 3731107 * 2
def baseEnd_3731107 : Nat := 638617088118346253467819

theorem tailTrace_3731107 : CollatzResearch.WordTrace tailWord_3731107 prefixEnd_3731107 638617088118346253467819 := by
  unfold tailWord_3731107
  simp only [CollatzResearch.WordTrace]
  refine ⟨136084652093844036188847575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90723101395896024125898383 136084652093844036188847575)
  ·
    refine ⟨204126978140766054283271363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136084652093844036188847575 204126978140766054283271363)
    ·
      refine ⟨306190467211149081424907045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204126978140766054283271363 306190467211149081424907045)
      ·
        refine ⟨57410712602090452767170071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 306190467211149081424907045 57410712602090452767170071)
        ·
          refine ⟨86116068903135679150755107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57410712602090452767170071 86116068903135679150755107)
          ·
            refine ⟨129174103354703518726132661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86116068903135679150755107 129174103354703518726132661)
            ·
              refine ⟨12110072189503454880574937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129174103354703518726132661 12110072189503454880574937)
              ·
                refine ⟨9082554142127591160431203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12110072189503454880574937 9082554142127591160431203)
                ·
                  refine ⟨13623831213191386740646805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9082554142127591160431203 13623831213191386740646805)
                  ·
                    refine ⟨638617088118346253467819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13623831213191386740646805 638617088118346253467819)
                    ·
                      rfl

theorem cell23_3731107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 6].length) (baseStart_3731107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731107 prefixEnd_3731107 := by exact prefixLift 3731107
  have htrace : WordTrace (prefixWord ++ tailWord_3731107) baseStart_3731107 baseEnd_3731107 := by
    simpa [prefixWord, tailWord_3731107, baseEnd_3731107] using wordTrace_append hprefix tailTrace_3731107
  have hstable : (prefixWord ++ tailWord_3731107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731107).length < 2 ^ (prefixWord ++ tailWord_3731107).sum := by decide
  have hdescent : baseEnd_3731107 < baseStart_3731107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731125 : List Nat := [1, 3, 3, 3, 2, 1, 1, 4, 1, 1, 3]
def baseStart_3731125 : Nat := 118140960795 + 3731125 * 2 ^ 59
def prefixEnd_3731125 : Nat := 4983230072969 + 3 ^ 40 * 3731125 * 2
def baseEnd_3731125 : Nat := 1915860507006819689978375

theorem tailTrace_3731125 : CollatzResearch.WordTrace tailWord_3731125 prefixEnd_3731125 1915860507006819689978375 := by
  unfold tailWord_3731125
  simp only [CollatzResearch.WordTrace]
  refine ⟨136085308607778825263002829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90723539071852550175335219 136085308607778825263002829)
  ·
    refine ⟨51031990727917059473626061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136085308607778825263002829 51031990727917059473626061)
    ·
      refine ⟨19136996522968897302609773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51031990727917059473626061 19136996522968897302609773)
      ·
        refine ⟨7176373696113336488478665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19136996522968897302609773 7176373696113336488478665)
        ·
          refine ⟨5382280272085002366358999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7176373696113336488478665 5382280272085002366358999)
          ·
            refine ⟨8073420408127503549538499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5382280272085002366358999 8073420408127503549538499)
            ·
              refine ⟨12110130612191255324307749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8073420408127503549538499 12110130612191255324307749)
              ·
                refine ⟨2270649489785860373307703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12110130612191255324307749 2270649489785860373307703)
                ·
                  refine ⟨3405974234678790559961555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2270649489785860373307703 3405974234678790559961555)
                  ·
                    refine ⟨5108961352018185839942333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3405974234678790559961555 5108961352018185839942333)
                    ·
                      refine ⟨1915860507006819689978375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5108961352018185839942333 1915860507006819689978375)
                      ·
                        rfl

theorem cell23_3731125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_3731125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731125 prefixEnd_3731125 := by exact prefixLift 3731125
  have htrace : WordTrace (prefixWord ++ tailWord_3731125) baseStart_3731125 baseEnd_3731125 := by
    simpa [prefixWord, tailWord_3731125, baseEnd_3731125] using wordTrace_append hprefix tailTrace_3731125
  have hstable : (prefixWord ++ tailWord_3731125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731125).length < 2 ^ (prefixWord ++ tailWord_3731125).sum := by decide
  have hdescent : baseEnd_3731125 < baseStart_3731125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731144 : List Nat := [2, 1, 3, 1, 2, 2, 4, 1, 1, 2, 4]
def baseStart_3731144 : Nat := 118140960795 + 3731144 * 2 ^ 59
def prefixEnd_3731144 : Nat := 4983230072969 + 3 ^ 40 * 3731144 * 2
def baseEnd_3731144 : Nat := 1915870263139255115640787

theorem tailTrace_3731144 : CollatzResearch.WordTrace tailWord_3731144 prefixEnd_3731144 1915870263139255115640787 := by
  unfold tailWord_3731144
  simp only [CollatzResearch.WordTrace]
  refine ⟨68043000797354995753972243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90724001063139994338629657 68043000797354995753972243)
  ·
    refine ⟨102064501196032493630958365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68043000797354995753972243 102064501196032493630958365)
    ·
      refine ⟨38274187948512185111609387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102064501196032493630958365 38274187948512185111609387)
      ·
        refine ⟨57411281922768277667414081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38274187948512185111609387 57411281922768277667414081)
        ·
          refine ⟨43058461442076208250560561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57411281922768277667414081 43058461442076208250560561)
          ·
            refine ⟨32293846081557156187920421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43058461442076208250560561 32293846081557156187920421)
            ·
              refine ⟨6055096140291966785235079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32293846081557156187920421 6055096140291966785235079)
              ·
                refine ⟨9082644210437950177852619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6055096140291966785235079 9082644210437950177852619)
                ·
                  refine ⟨13623966315656925266778929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9082644210437950177852619 13623966315656925266778929)
                  ·
                    refine ⟨10217974736742693950084197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13623966315656925266778929 10217974736742693950084197)
                    ·
                      refine ⟨1915870263139255115640787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10217974736742693950084197 1915870263139255115640787)
                      ·
                        rfl

theorem cell23_3731144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_3731144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731144 prefixEnd_3731144 := by exact prefixLift 3731144
  have htrace : WordTrace (prefixWord ++ tailWord_3731144) baseStart_3731144 baseEnd_3731144 := by
    simpa [prefixWord, tailWord_3731144, baseEnd_3731144] using wordTrace_append hprefix tailTrace_3731144
  have hstable : (prefixWord ++ tailWord_3731144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731144).length < 2 ^ (prefixWord ++ tailWord_3731144).sum := by decide
  have hdescent : baseEnd_3731144 < baseStart_3731144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731175 : List Nat := [1, 1, 5, 4, 1, 2, 1, 2, 2, 4]
def baseStart_3731175 : Nat := 118140960795 + 3731175 * 2 ^ 59
def prefixEnd_3731175 : Nat := 4983230072969 + 3 ^ 40 * 3731175 * 2
def baseEnd_3731175 : Nat := 638628727013181498117715

theorem tailTrace_3731175 : CollatzResearch.WordTrace tailWord_3731175 prefixEnd_3731175 638628727013181498117715 := by
  unfold tailWord_3731175
  simp only [CollatzResearch.WordTrace]
  refine ⟨136087132257597683802322979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90724754838398455868215319 136087132257597683802322979)
  ·
    refine ⟨204130698386396525703484469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136087132257597683802322979 204130698386396525703484469)
    ·
      refine ⟨19137252973724674284701669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204130698386396525703484469 19137252973724674284701669)
      ·
        refine ⟨3588234932573376428381563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19137252973724674284701669 3588234932573376428381563)
        ·
          refine ⟨5382352398860064642572345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3588234932573376428381563 5382352398860064642572345)
          ·
            refine ⟨4036764299145048481929259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5382352398860064642572345 4036764299145048481929259)
            ·
              refine ⟨6055146448717572722893889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4036764299145048481929259 6055146448717572722893889)
              ·
                refine ⟨4541359836538179542170417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6055146448717572722893889 4541359836538179542170417)
                ·
                  refine ⟨3406019877403634656627813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4541359836538179542170417 3406019877403634656627813)
                  ·
                    refine ⟨638628727013181498117715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3406019877403634656627813 638628727013181498117715)
                    ·
                      rfl

theorem cell23_3731175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_3731175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731175 prefixEnd_3731175 := by exact prefixLift 3731175
  have htrace : WordTrace (prefixWord ++ tailWord_3731175) baseStart_3731175 baseEnd_3731175 := by
    simpa [prefixWord, tailWord_3731175, baseEnd_3731175] using wordTrace_append hprefix tailTrace_3731175
  have hstable : (prefixWord ++ tailWord_3731175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731175).length < 2 ^ (prefixWord ++ tailWord_3731175).sum := by decide
  have hdescent : baseEnd_3731175 < baseStart_3731175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731187 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 4]
def baseStart_3731187 : Nat := 118140960795 + 3731187 * 2 ^ 59
def prefixEnd_3731187 : Nat := 4983230072969 + 3 ^ 40 * 3731187 * 2
def baseEnd_3731187 : Nat := 1915892342807398447403089

theorem tailTrace_3731187 : CollatzResearch.WordTrace tailWord_3731187 prefixEnd_3731187 1915892342807398447403089 := by
  unfold tailWord_3731187
  simp only [CollatzResearch.WordTrace]
  refine ⟨136087569933554209851759815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90725046622369473234506543 136087569933554209851759815)
  ·
    refine ⟨204131354900331314777639723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136087569933554209851759815 204131354900331314777639723)
    ·
      refine ⟨306197032350496972166459585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204131354900331314777639723 306197032350496972166459585)
      ·
        refine ⟨229647774262872729124844689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306197032350496972166459585 229647774262872729124844689)
        ·
          refine ⟨172235830697154546843633517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229647774262872729124844689 172235830697154546843633517)
          ·
            refine ⟨64588436511432955066362569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172235830697154546843633517 64588436511432955066362569)
            ·
              refine ⟨48441327383574716299771927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64588436511432955066362569 48441327383574716299771927)
              ·
                refine ⟨72661991075362074449657891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48441327383574716299771927 72661991075362074449657891)
                ·
                  refine ⟨108992986613043111674486837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72661991075362074449657891 108992986613043111674486837)
                  ·
                    refine ⟨10218092494972791719483141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108992986613043111674486837 10218092494972791719483141)
                    ·
                      refine ⟨1915892342807398447403089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10218092494972791719483141 1915892342807398447403089)
                      ·
                        rfl

theorem cell23_3731187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 4].length) (baseStart_3731187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731187 prefixEnd_3731187 := by exact prefixLift 3731187
  have htrace : WordTrace (prefixWord ++ tailWord_3731187) baseStart_3731187 baseEnd_3731187 := by
    simpa [prefixWord, tailWord_3731187, baseEnd_3731187] using wordTrace_append hprefix tailTrace_3731187
  have hstable : (prefixWord ++ tailWord_3731187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731187).length < 2 ^ (prefixWord ++ tailWord_3731187).sum := by decide
  have hdescent : baseEnd_3731187 < baseStart_3731187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731197 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 1, 8]
def baseStart_3731197 : Nat := 118140960795 + 3731197 * 2 ^ 59
def prefixEnd_3731197 : Nat := 4983230072969 + 3 ^ 40 * 3731197 * 2
def baseEnd_3731197 : Nat := 638632492537981136092681

theorem tailTrace_3731197 : CollatzResearch.WordTrace tailWord_3731197 prefixEnd_3731197 638632492537981136092681 := by
  unfold tailWord_3731197
  simp only [CollatzResearch.WordTrace]
  refine ⟨136087934663517981559623845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90725289775678654373082563 136087934663517981559623845)
  ·
    refine ⟨25516487749409621542429471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136087934663517981559623845 25516487749409621542429471)
    ·
      refine ⟨38274731624114432313644207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25516487749409621542429471 38274731624114432313644207)
      ·
        refine ⟨57412097436171648470466311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38274731624114432313644207 57412097436171648470466311)
        ·
          refine ⟨86118146154257472705699467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57412097436171648470466311 86118146154257472705699467)
          ·
            refine ⟨129177219231386209058549201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86118146154257472705699467 129177219231386209058549201)
            ·
              refine ⟨96882914423539656793911901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129177219231386209058549201 96882914423539656793911901)
              ·
                refine ⟨36331092908827371297716963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96882914423539656793911901 36331092908827371297716963)
                ·
                  refine ⟨54496639363241056946575445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36331092908827371297716963 54496639363241056946575445)
                  ·
                    refine ⟨638632492537981136092681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54496639363241056946575445 638632492537981136092681)
                    ·
                      rfl

theorem cell23_3731197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_3731197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731197 prefixEnd_3731197 := by exact prefixLift 3731197
  have htrace : WordTrace (prefixWord ++ tailWord_3731197) baseStart_3731197 baseEnd_3731197 := by
    simpa [prefixWord, tailWord_3731197, baseEnd_3731197] using wordTrace_append hprefix tailTrace_3731197
  have hstable : (prefixWord ++ tailWord_3731197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731197).length < 2 ^ (prefixWord ++ tailWord_3731197).sum := by decide
  have hdescent : baseEnd_3731197 < baseStart_3731197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731208 : List Nat := [2, 1, 3, 2, 2, 1, 4, 2, 1, 3, 2]
def baseStart_3731208 : Nat := 118140960795 + 3731208 * 2 ^ 59
def prefixEnd_3731208 : Nat := 4983230072969 + 3 ^ 40 * 3731208 * 2
def baseEnd_3731208 : Nat := 1915903125901142865240493

theorem tailTrace_3731208 : CollatzResearch.WordTrace tailWord_3731208 prefixEnd_3731208 1915903125901142865240493 := by
  unfold tailWord_3731208
  simp only [CollatzResearch.WordTrace]
  refine ⟨68044167933239065219137139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90725557244318753625516185 68044167933239065219137139)
  ·
    refine ⟨102066251899858597828705709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68044167933239065219137139 102066251899858597828705709)
    ·
      refine ⟨38274844462446974185764641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102066251899858597828705709 38274844462446974185764641)
      ·
        refine ⟨28706133346835230639323481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38274844462446974185764641 28706133346835230639323481)
        ·
          refine ⟨21529600010126422979492611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28706133346835230639323481 21529600010126422979492611)
          ·
            refine ⟨32294400015189634469238917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21529600010126422979492611 32294400015189634469238917)
            ·
              refine ⟨6055200002848056462982297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32294400015189634469238917 6055200002848056462982297)
              ·
                refine ⟨4541400002136042347236723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6055200002848056462982297 4541400002136042347236723)
                ·
                  refine ⟨6812100003204063520855085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4541400002136042347236723 6812100003204063520855085)
                  ·
                    refine ⟨2554537501201523820320657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6812100003204063520855085 2554537501201523820320657)
                    ·
                      refine ⟨1915903125901142865240493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2554537501201523820320657 1915903125901142865240493)
                      ·
                        rfl

theorem cell23_3731208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_3731208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731208 prefixEnd_3731208 := by exact prefixLift 3731208
  have htrace : WordTrace (prefixWord ++ tailWord_3731208) baseStart_3731208 baseEnd_3731208 := by
    simpa [prefixWord, tailWord_3731208, baseEnd_3731208] using wordTrace_append hprefix tailTrace_3731208
  have hstable : (prefixWord ++ tailWord_3731208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731208).length < 2 ^ (prefixWord ++ tailWord_3731208).sum := by decide
  have hdescent : baseEnd_3731208 < baseStart_3731208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731244 : List Nat := [2, 2, 1, 1, 1, 5, 3, 1, 7]
def baseStart_3731244 : Nat := 118140960795 + 3731244 * 2 ^ 59
def prefixEnd_3731244 : Nat := 4983230072969 + 3 ^ 40 * 3731244 * 2
def baseEnd_3731244 : Nat := 212880179022744969376703

theorem tailTrace_3731244 : CollatzResearch.WordTrace tailWord_3731244 prefixEnd_3731244 212880179022744969376703 := by
  unfold tailWord_3731244
  simp only [CollatzResearch.WordTrace]
  refine ⟨68044824447173854293292393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90726432596231805724389857 68044824447173854293292393)
  ·
    refine ⟨51033618335380390719969295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68044824447173854293292393 51033618335380390719969295)
    ·
      refine ⟨76550427503070586079953943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51033618335380390719969295 76550427503070586079953943)
      ·
        refine ⟨114825641254605879119930915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76550427503070586079953943 114825641254605879119930915)
        ·
          refine ⟨172238461881908818679896373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114825641254605879119930915 172238461881908818679896373)
          ·
            refine ⟨16147355801428951751240285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 172238461881908818679896373 16147355801428951751240285)
            ·
              refine ⟨6055258425535856906715107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16147355801428951751240285 6055258425535856906715107)
              ·
                refine ⟨9082887638303785360072661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6055258425535856906715107 9082887638303785360072661)
                ·
                  refine ⟨212880179022744969376703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9082887638303785360072661 212880179022744969376703)
                  ·
                    rfl

theorem cell23_3731244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 7].length) (baseStart_3731244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731244 prefixEnd_3731244 := by exact prefixLift 3731244
  have htrace : WordTrace (prefixWord ++ tailWord_3731244) baseStart_3731244 baseEnd_3731244 := by
    simpa [prefixWord, tailWord_3731244, baseEnd_3731244] using wordTrace_append hprefix tailTrace_3731244
  have hstable : (prefixWord ++ tailWord_3731244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731244).length < 2 ^ (prefixWord ++ tailWord_3731244).sum := by decide
  have hdescent : baseEnd_3731244 < baseStart_3731244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731298 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 2, 5, 2]
def baseStart_3731298 : Nat := 118140960795 + 3731298 * 2 ^ 59
def prefixEnd_3731298 : Nat := 4983230072969 + 3 ^ 40 * 3731298 * 2
def baseEnd_3731298 : Nat := 1915949339160047513115079

theorem tailTrace_3731298 : CollatzResearch.WordTrace tailWord_3731298 prefixEnd_3731298 1915949339160047513115079 := by
  unfold tailWord_3731298
  simp only [CollatzResearch.WordTrace]
  refine ⟨34022904609038018952262637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90727745624101383872700365 34022904609038018952262637)
  ·
    refine ⟨12758589228389257107098489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34022904609038018952262637 12758589228389257107098489)
    ·
      refine ⟨9568941921291942830323867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12758589228389257107098489 9568941921291942830323867)
      ·
        refine ⟨14353412881937914245485801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9568941921291942830323867 14353412881937914245485801)
        ·
          refine ⟨10765059661453435684114351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14353412881937914245485801 10765059661453435684114351)
          ·
            refine ⟨16147589492180153526171527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10765059661453435684114351 16147589492180153526171527)
            ·
              refine ⟨24221384238270230289257291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16147589492180153526171527 24221384238270230289257291)
              ·
                refine ⟨36332076357405345433885937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24221384238270230289257291 36332076357405345433885937)
                ·
                  refine ⟨27249057268054009075414453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36332076357405345433885937 27249057268054009075414453)
                  ·
                    refine ⟨2554599118880063350820105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27249057268054009075414453 2554599118880063350820105)
                    ·
                      refine ⟨1915949339160047513115079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2554599118880063350820105 1915949339160047513115079)
                      ·
                        rfl

theorem cell23_3731298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_3731298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731298 prefixEnd_3731298 := by exact prefixLift 3731298
  have htrace : WordTrace (prefixWord ++ tailWord_3731298) baseStart_3731298 baseEnd_3731298 := by
    simpa [prefixWord, tailWord_3731298, baseEnd_3731298] using wordTrace_append hprefix tailTrace_3731298
  have hstable : (prefixWord ++ tailWord_3731298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731298).length < 2 ^ (prefixWord ++ tailWord_3731298).sum := by decide
  have hdescent : baseEnd_3731298 < baseStart_3731298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731321 : List Nat := [1, 2, 1, 3, 2, 2, 3, 2, 3, 4]
def baseStart_3731321 : Nat := 118140960795 + 3731321 * 2 ^ 59
def prefixEnd_3731321 : Nat := 4983230072969 + 3 ^ 40 * 3731321 * 2
def baseEnd_3731321 : Nat := 638653716405033641042491

theorem tailTrace_3731321 : CollatzResearch.WordTrace tailWord_3731321 prefixEnd_3731321 638653716405033641042491 := by
  unfold tailWord_3731321
  simp only [CollatzResearch.WordTrace]
  refine ⟨136092457315068750737137817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90728304876712500491425211 136092457315068750737137817)
  ·
    refine ⟨102069342986301563052853363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136092457315068750737137817 102069342986301563052853363)
    ·
      refine ⟨153104014479452344579280045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102069342986301563052853363 153104014479452344579280045)
      ·
        refine ⟨57414005429794629217230017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153104014479452344579280045 57414005429794629217230017)
        ·
          refine ⟨43060504072345971912922513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57414005429794629217230017 43060504072345971912922513)
          ·
            refine ⟨32295378054259478934691885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43060504072345971912922513 32295378054259478934691885)
            ·
              refine ⟨12110766770347304600509457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32295378054259478934691885 12110766770347304600509457)
              ·
                refine ⟨9083075077760478450382093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12110766770347304600509457 9083075077760478450382093)
                ·
                  refine ⟨3406153154160179418893285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9083075077760478450382093 3406153154160179418893285)
                  ·
                    refine ⟨638653716405033641042491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3406153154160179418893285 638653716405033641042491)
                    ·
                      rfl

theorem cell23_3731321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3, 4].length) (baseStart_3731321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731321 prefixEnd_3731321 := by exact prefixLift 3731321
  have htrace : WordTrace (prefixWord ++ tailWord_3731321) baseStart_3731321 baseEnd_3731321 := by
    simpa [prefixWord, tailWord_3731321, baseEnd_3731321] using wordTrace_append hprefix tailTrace_3731321
  have hstable : (prefixWord ++ tailWord_3731321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731321).length < 2 ^ (prefixWord ++ tailWord_3731321).sum := by decide
  have hdescent : baseEnd_3731321 < baseStart_3731321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731331 : List Nat := [1, 1, 1, 3, 4, 3, 1, 1, 1, 4, 3]
def baseStart_3731331 : Nat := 118140960795 + 3731331 * 2 ^ 59
def prefixEnd_3731331 : Nat := 4983230072969 + 3 ^ 40 * 3731331 * 2
def baseEnd_3731331 : Nat := 1915966284021645884002427

theorem tailTrace_3731331 : CollatzResearch.WordTrace tailWord_3731331 prefixEnd_3731331 1915966284021645884002427 := by
  unfold tailWord_3731331
  simp only [CollatzResearch.WordTrace]
  refine ⟨136092822045032522445001847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90728548030021681630001231 136092822045032522445001847)
  ·
    refine ⟨204139233067548783667502771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136092822045032522445001847 204139233067548783667502771)
    ·
      refine ⟨306208849601323175501254157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204139233067548783667502771 306208849601323175501254157)
      ·
        refine ⟨114828318600496190812970309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306208849601323175501254157 114828318600496190812970309)
        ·
          refine ⟨21530309737593035777431933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114828318600496190812970309 21530309737593035777431933)
          ·
            refine ⟨8073866151597388416536975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21530309737593035777431933 8073866151597388416536975)
            ·
              refine ⟨12110799227396082624805463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8073866151597388416536975 12110799227396082624805463)
              ·
                refine ⟨18166198841094123937208195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12110799227396082624805463 18166198841094123937208195)
                ·
                  refine ⟨27249298261641185905812293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18166198841094123937208195 27249298261641185905812293)
                  ·
                    refine ⟨5109243424057722357339805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27249298261641185905812293 5109243424057722357339805)
                    ·
                      refine ⟨1915966284021645884002427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5109243424057722357339805 1915966284021645884002427)
                      ·
                        rfl

theorem cell23_3731331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4, 3].length) (baseStart_3731331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731331 prefixEnd_3731331 := by exact prefixLift 3731331
  have htrace : WordTrace (prefixWord ++ tailWord_3731331) baseStart_3731331 baseEnd_3731331 := by
    simpa [prefixWord, tailWord_3731331, baseEnd_3731331] using wordTrace_append hprefix tailTrace_3731331
  have hstable : (prefixWord ++ tailWord_3731331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731331).length < 2 ^ (prefixWord ++ tailWord_3731331).sum := by decide
  have hdescent : baseEnd_3731331 < baseStart_3731331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731351 : List Nat := [1, 1, 3, 3, 1, 3, 3, 2, 6]
def baseStart_3731351 : Nat := 118140960795 + 3731351 * 2 ^ 59
def prefixEnd_3731351 : Nat := 4983230072969 + 3 ^ 40 * 3731351 * 2
def baseEnd_3731351 : Nat := 212886283737192867305815

theorem tailTrace_3731351 : CollatzResearch.WordTrace tailWord_3731351 prefixEnd_3731351 212886283737192867305815 := by
  unfold tailWord_3731351
  simp only [CollatzResearch.WordTrace]
  refine ⟨136093551504960065860729907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90729034336640043907153271 136093551504960065860729907)
  ·
    refine ⟨204140327257440098791094861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136093551504960065860729907 204140327257440098791094861)
    ·
      refine ⟨76552622721540037046660573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204140327257440098791094861 76552622721540037046660573)
      ·
        refine ⟨28707233520577513892497715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76552622721540037046660573 28707233520577513892497715)
        ·
          refine ⟨43060850280866270838746573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28707233520577513892497715 43060850280866270838746573)
          ·
            refine ⟨16147818855324851564529965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43060850280866270838746573 16147818855324851564529965)
            ·
              refine ⟨6055432070746819336698737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16147818855324851564529965 6055432070746819336698737)
              ·
                refine ⟨4541574053060114502524053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6055432070746819336698737 4541574053060114502524053)
                ·
                  refine ⟨212886283737192867305815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4541574053060114502524053 212886283737192867305815)
                  ·
                    rfl

theorem cell23_3731351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 6].length) (baseStart_3731351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731351 prefixEnd_3731351 := by exact prefixLift 3731351
  have htrace : WordTrace (prefixWord ++ tailWord_3731351) baseStart_3731351 baseEnd_3731351 := by
    simpa [prefixWord, tailWord_3731351, baseEnd_3731351] using wordTrace_append hprefix tailTrace_3731351
  have hstable : (prefixWord ++ tailWord_3731351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731351).length < 2 ^ (prefixWord ++ tailWord_3731351).sum := by decide
  have hdescent : baseEnd_3731351 < baseStart_3731351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731401 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 1, 8, 2]
def baseStart_3731401 : Nat := 118140960795 + 3731401 * 2 ^ 59
def prefixEnd_3731401 : Nat := 4983230072969 + 3 ^ 40 * 3731401 * 2
def baseEnd_3731401 : Nat := 1916002227667460610127105

theorem tailTrace_3731401 : CollatzResearch.WordTrace tailWord_3731401 prefixEnd_3731401 1916002227667460610127105 := by
  unfold tailWord_3731401
  simp only [CollatzResearch.WordTrace]
  refine ⟨136095375154778924400050057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90730250103185949600033371 136095375154778924400050057)
  ·
    refine ⟨102071531366084193300037543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136095375154778924400050057 102071531366084193300037543)
    ·
      refine ⟨153107297049126289950056315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102071531366084193300037543 153107297049126289950056315)
      ·
        refine ⟨229660945573689434925084473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153107297049126289950056315 229660945573689434925084473)
        ·
          refine ⟨172245709180267076193813355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229660945573689434925084473 172245709180267076193813355)
          ·
            refine ⟨258368563770400614290720033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172245709180267076193813355 258368563770400614290720033)
            ·
              refine ⟨193776422827800460718040025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258368563770400614290720033 193776422827800460718040025)
              ·
                refine ⟨145332317120850345538530019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193776422827800460718040025 145332317120850345538530019)
                ·
                  refine ⟨217998475681275518307795029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145332317120850345538530019 217998475681275518307795029)
                  ·
                    refine ⟨2554669636889947480169473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 217998475681275518307795029 2554669636889947480169473)
                    ·
                      refine ⟨1916002227667460610127105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2554669636889947480169473 1916002227667460610127105)
                      ·
                        rfl

theorem cell23_3731401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 8, 2].length) (baseStart_3731401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731401 prefixEnd_3731401 := by exact prefixLift 3731401
  have htrace : WordTrace (prefixWord ++ tailWord_3731401) baseStart_3731401 baseEnd_3731401 := by
    simpa [prefixWord, tailWord_3731401, baseEnd_3731401] using wordTrace_append hprefix tailTrace_3731401
  have hstable : (prefixWord ++ tailWord_3731401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731401).length < 2 ^ (prefixWord ++ tailWord_3731401).sum := by decide
  have hdescent : baseEnd_3731401 < baseStart_3731401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731428 : List Nat := [2, 3, 1, 1, 1, 1, 5, 3, 2, 4]
def baseStart_3731428 : Nat := 118140960795 + 3731428 * 2 ^ 59
def prefixEnd_3731428 : Nat := 4983230072969 + 3 ^ 40 * 3731428 * 2
def baseEnd_3731428 : Nat := 638672030548377334829827

theorem tailTrace_3731428 : CollatzResearch.WordTrace tailWord_3731428 prefixEnd_3731428 638672030548377334829827 := by
  unfold tailWord_3731428
  simp only [CollatzResearch.WordTrace]
  refine ⟨68048179962840554005641469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90730906617120738674188625 68048179962840554005641469)
  ·
    refine ⟨25518067486065207752115551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68048179962840554005641469 25518067486065207752115551)
    ·
      refine ⟨38277101229097811628173327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25518067486065207752115551 38277101229097811628173327)
      ·
        refine ⟨57415651843646717442259991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38277101229097811628173327 57415651843646717442259991)
        ·
          refine ⟨86123477765470076163389987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57415651843646717442259991 86123477765470076163389987)
          ·
            refine ⟨129185216648205114245084981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86123477765470076163389987 129185216648205114245084981)
            ·
              refine ⟨12111114060769229460476717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129185216648205114245084981 12111114060769229460476717)
              ·
                refine ⟨4541667772788461047678769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12111114060769229460476717 4541667772788461047678769)
                ·
                  refine ⟨3406250829591345785759077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4541667772788461047678769 3406250829591345785759077)
                  ·
                    refine ⟨638672030548377334829827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3406250829591345785759077 638672030548377334829827)
                    ·
                      rfl

theorem cell23_3731428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_3731428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731428 prefixEnd_3731428 := by exact prefixLift 3731428
  have htrace : WordTrace (prefixWord ++ tailWord_3731428) baseStart_3731428 baseEnd_3731428 := by
    simpa [prefixWord, tailWord_3731428, baseEnd_3731428] using wordTrace_append hprefix tailTrace_3731428
  have hstable : (prefixWord ++ tailWord_3731428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731428).length < 2 ^ (prefixWord ++ tailWord_3731428).sum := by decide
  have hdescent : baseEnd_3731428 < baseStart_3731428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731451 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 3, 3, 3]
def baseStart_3731451 : Nat := 118140960795 + 3731451 * 2 ^ 59
def prefixEnd_3731451 : Nat := 4983230072969 + 3 ^ 40 * 3731451 * 2
def baseEnd_3731451 : Nat := 1916027901700185414501875

theorem tailTrace_3731451 : CollatzResearch.WordTrace tailWord_3731451 prefixEnd_3731451 1916027901700185414501875 := by
  unfold tailWord_3731451
  simp only [CollatzResearch.WordTrace]
  refine ⟨136097198804597782939370207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90731465869731855292913471 136097198804597782939370207)
  ·
    refine ⟨204145798206896674409055311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136097198804597782939370207 204145798206896674409055311)
    ·
      refine ⟨306218697310345011613582967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204145798206896674409055311 306218697310345011613582967)
      ·
        refine ⟨459328045965517517420374451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306218697310345011613582967 459328045965517517420374451)
        ·
          refine ⟨688992068948276276130561677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459328045965517517420374451 688992068948276276130561677)
          ·
            refine ⟨258372025855603603548960629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 688992068948276276130561677 258372025855603603548960629)
            ·
              refine ⟨24222377423962837832715059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 258372025855603603548960629 24222377423962837832715059)
              ·
                refine ⟨36333566135944256749072589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24222377423962837832715059 36333566135944256749072589)
                ·
                  refine ⟨13625087300979096280902221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36333566135944256749072589 13625087300979096280902221)
                  ·
                    refine ⟨5109407737867161105338333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13625087300979096280902221 5109407737867161105338333)
                    ·
                      refine ⟨1916027901700185414501875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5109407737867161105338333 1916027901700185414501875)
                      ·
                        rfl

theorem cell23_3731451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3, 3].length) (baseStart_3731451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731451 prefixEnd_3731451 := by exact prefixLift 3731451
  have htrace : WordTrace (prefixWord ++ tailWord_3731451) baseStart_3731451 baseEnd_3731451 := by
    simpa [prefixWord, tailWord_3731451, baseEnd_3731451] using wordTrace_append hprefix tailTrace_3731451
  have hstable : (prefixWord ++ tailWord_3731451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731451).length < 2 ^ (prefixWord ++ tailWord_3731451).sum := by decide
  have hdescent : baseEnd_3731451 < baseStart_3731451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731452 : List Nat := [2, 2, 2, 1, 2, 2, 2, 5, 1, 2, 2]
def baseStart_3731452 : Nat := 118140960795 + 3731452 * 2 ^ 59
def prefixEnd_3731452 : Nat := 4983230072969 + 3 ^ 40 * 3731452 * 2
def baseEnd_3731452 : Nat := 1916028415180839910589371

theorem tailTrace_3731452 : CollatzResearch.WordTrace tailWord_3731452 prefixEnd_3731452 1916028415180839910589371 := by
  unfold tailWord_3731452
  simp only [CollatzResearch.WordTrace]
  refine ⟨68048617638797080055078305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90731490185062773406771073 68048617638797080055078305)
  ·
    refine ⟨51036463229097810041308729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68048617638797080055078305 51036463229097810041308729)
    ·
      refine ⟨38277347421823357530981547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51036463229097810041308729 38277347421823357530981547)
      ·
        refine ⟨57416021132735036296472321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38277347421823357530981547 57416021132735036296472321)
        ·
          refine ⟨43062015849551277222354241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57416021132735036296472321 43062015849551277222354241)
          ·
            refine ⟨32296511887163457916765681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43062015849551277222354241 32296511887163457916765681)
            ·
              refine ⟨24222383915372593437574261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32296511887163457916765681 24222383915372593437574261)
              ·
                refine ⟨2270848492066180634772587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24222383915372593437574261 2270848492066180634772587)
                ·
                  refine ⟨3406272738099270952158881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2270848492066180634772587 3406272738099270952158881)
                  ·
                    refine ⟨2554704553574453214119161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3406272738099270952158881 2554704553574453214119161)
                    ·
                      refine ⟨1916028415180839910589371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2554704553574453214119161 1916028415180839910589371)
                      ·
                        rfl

theorem cell23_3731452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5, 1, 2, 2].length) (baseStart_3731452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731452 prefixEnd_3731452 := by exact prefixLift 3731452
  have htrace : WordTrace (prefixWord ++ tailWord_3731452) baseStart_3731452 baseEnd_3731452 := by
    simpa [prefixWord, tailWord_3731452, baseEnd_3731452] using wordTrace_append hprefix tailTrace_3731452
  have hstable : (prefixWord ++ tailWord_3731452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731452).length < 2 ^ (prefixWord ++ tailWord_3731452).sum := by decide
  have hdescent : baseEnd_3731452 < baseStart_3731452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731485 : List Nat := [1, 4, 2, 2, 2, 2, 2, 1, 1, 3, 3]
def baseStart_3731485 : Nat := 118140960795 + 3731485 * 2 ^ 59
def prefixEnd_3731485 : Nat := 4983230072969 + 3 ^ 40 * 3731485 * 2
def baseEnd_3731485 : Nat := 1916045360042438281476719

theorem tailTrace_3731485 : CollatzResearch.WordTrace tailWord_3731485 prefixEnd_3731485 1916045360042438281476719 := by
  unfold tailWord_3731485
  simp only [CollatzResearch.WordTrace]
  refine ⟨136098438886474606746107909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90732292590983071164071939 136098438886474606746107909)
  ·
    refine ⟨25518457291213988764895233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136098438886474606746107909 25518457291213988764895233)
    ·
      refine ⟨19138842968410491573671425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25518457291213988764895233 19138842968410491573671425)
      ·
        refine ⟨14354132226307868680253569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19138842968410491573671425 14354132226307868680253569)
        ·
          refine ⟨10765599169730901510190177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14354132226307868680253569 10765599169730901510190177)
          ·
            refine ⟨8074199377298176132642633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10765599169730901510190177 8074199377298176132642633)
            ·
              refine ⟨6055649532973632099481975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8074199377298176132642633 6055649532973632099481975)
              ·
                refine ⟨9083474299460448149222963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6055649532973632099481975 9083474299460448149222963)
                ·
                  refine ⟨13625211449190672223834445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9083474299460448149222963 13625211449190672223834445)
                  ·
                    refine ⟨5109454293446502083937917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13625211449190672223834445 5109454293446502083937917)
                    ·
                      refine ⟨1916045360042438281476719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5109454293446502083937917 1916045360042438281476719)
                      ·
                        rfl

theorem cell23_3731485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_3731485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731485 prefixEnd_3731485 := by exact prefixLift 3731485
  have htrace : WordTrace (prefixWord ++ tailWord_3731485) baseStart_3731485 baseEnd_3731485 := by
    simpa [prefixWord, tailWord_3731485, baseEnd_3731485] using wordTrace_append hprefix tailTrace_3731485
  have hstable : (prefixWord ++ tailWord_3731485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731485).length < 2 ^ (prefixWord ++ tailWord_3731485).sum := by decide
  have hdescent : baseEnd_3731485 < baseStart_3731485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731491 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 4]
def baseStart_3731491 : Nat := 118140960795 + 3731491 * 2 ^ 59
def prefixEnd_3731491 : Nat := 4983230072969 + 3 ^ 40 * 3731491 * 2
def baseEnd_3731491 : Nat := 1916048440926365258001691

theorem tailTrace_3731491 : CollatzResearch.WordTrace tailWord_3731491 prefixEnd_3731491 1916048440926365258001691 := by
  unfold tailWord_3731491
  simp only [CollatzResearch.WordTrace]
  refine ⟨136098657724452869770826327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90732438482968579847217551 136098657724452869770826327)
  ·
    refine ⟨204147986586679304656239491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136098657724452869770826327 204147986586679304656239491)
    ·
      refine ⟨306221979880018956984359237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204147986586679304656239491 306221979880018956984359237)
      ·
        refine ⟨57416621227503554434567357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 306221979880018956984359237 57416621227503554434567357)
        ·
          refine ⟨21531232960313832912962759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57416621227503554434567357 21531232960313832912962759)
          ·
            refine ⟨32296849440470749369444139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21531232960313832912962759 32296849440470749369444139)
            ·
              refine ⟨48445274160706124054166209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32296849440470749369444139 48445274160706124054166209)
              ·
                refine ⟨36333955620529593040624657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48445274160706124054166209 36333955620529593040624657)
                ·
                  refine ⟨27250466715397194780468493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36333955620529593040624657 27250466715397194780468493)
                  ·
                    refine ⟨10218925018273948042675685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27250466715397194780468493 10218925018273948042675685)
                    ·
                      refine ⟨1916048440926365258001691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10218925018273948042675685 1916048440926365258001691)
                      ·
                        rfl

theorem cell23_3731491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_3731491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731491 prefixEnd_3731491 := by exact prefixLift 3731491
  have htrace : WordTrace (prefixWord ++ tailWord_3731491) baseStart_3731491 baseEnd_3731491 := by
    simpa [prefixWord, tailWord_3731491, baseEnd_3731491] using wordTrace_append hprefix tailTrace_3731491
  have hstable : (prefixWord ++ tailWord_3731491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731491).length < 2 ^ (prefixWord ++ tailWord_3731491).sum := by decide
  have hdescent : baseEnd_3731491 < baseStart_3731491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731511 : List Nat := [1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 5]
def baseStart_3731511 : Nat := 118140960795 + 3731511 * 2 ^ 59
def prefixEnd_3731511 : Nat := 4983230072969 + 3 ^ 40 * 3731511 * 2
def baseEnd_3731511 : Nat := 1916058710539455179751599

theorem tailTrace_3731511 : CollatzResearch.WordTrace tailWord_3731511 prefixEnd_3731511 1916058710539455179751599 := by
  unfold tailWord_3731511
  simp only [CollatzResearch.WordTrace]
  refine ⟨136099387184380413186554387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90732924789586942124369591 136099387184380413186554387)
  ·
    refine ⟨204149080776570619779831581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136099387184380413186554387 204149080776570619779831581)
    ·
      refine ⟨76555905291213982417436843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204149080776570619779831581 76555905291213982417436843)
      ·
        refine ⟨114833857936820973626155265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76555905291213982417436843 114833857936820973626155265)
        ·
          refine ⟨86125393452615730219616449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114833857936820973626155265 86125393452615730219616449)
          ·
            refine ⟨64594045089461797664712337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86125393452615730219616449 64594045089461797664712337)
            ·
              refine ⟨48445533817096348248534253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64594045089461797664712337 48445533817096348248534253)
              ·
                refine ⟨18167075181411130593200345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48445533817096348248534253 18167075181411130593200345)
                ·
                  refine ⟨13625306386058347944900259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18167075181411130593200345 13625306386058347944900259)
                  ·
                    refine ⟨20437959579087521917350389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13625306386058347944900259 20437959579087521917350389)
                    ·
                      refine ⟨1916058710539455179751599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20437959579087521917350389 1916058710539455179751599)
                      ·
                        rfl

theorem cell23_3731511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_3731511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731511 prefixEnd_3731511 := by exact prefixLift 3731511
  have htrace : WordTrace (prefixWord ++ tailWord_3731511) baseStart_3731511 baseEnd_3731511 := by
    simpa [prefixWord, tailWord_3731511, baseEnd_3731511] using wordTrace_append hprefix tailTrace_3731511
  have hstable : (prefixWord ++ tailWord_3731511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731511).length < 2 ^ (prefixWord ++ tailWord_3731511).sum := by decide
  have hdescent : baseEnd_3731511 < baseStart_3731511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731512 : List Nat := [2, 1, 2, 1, 6, 1, 1, 3, 1, 3, 2]
def baseStart_3731512 : Nat := 118140960795 + 3731512 * 2 ^ 59
def prefixEnd_3731512 : Nat := 4983230072969 + 3 ^ 40 * 3731512 * 2
def baseEnd_3731512 : Nat := 1916059224020109675839095

theorem tailTrace_3731512 : CollatzResearch.WordTrace tailWord_3731512 prefixEnd_3731512 1916059224020109675839095 := by
  unfold tailWord_3731512
  simp only [CollatzResearch.WordTrace]
  refine ⟨68049711828688395178670395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90732949104917860238227193 68049711828688395178670395)
  ·
    refine ⟨102074567743032592768005593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68049711828688395178670395 102074567743032592768005593)
    ·
      refine ⟨76555925807274444576004195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102074567743032592768005593 76555925807274444576004195)
      ·
        refine ⟨114833888710911666864006293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76555925807274444576004195 114833888710911666864006293)
        ·
          refine ⟨5382838533323984384250295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 114833888710911666864006293 5382838533323984384250295)
          ·
            refine ⟨8074257799985976576375443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5382838533323984384250295 8074257799985976576375443)
            ·
              refine ⟨12111386699978964864563165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8074257799985976576375443 12111386699978964864563165)
              ·
                refine ⟨4541770012492111824211187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12111386699978964864563165 4541770012492111824211187)
                ·
                  refine ⟨6812655018738167736316781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4541770012492111824211187 6812655018738167736316781)
                  ·
                    refine ⟨2554745632026812901118793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6812655018738167736316781 2554745632026812901118793)
                    ·
                      refine ⟨1916059224020109675839095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2554745632026812901118793 1916059224020109675839095)
                      ·
                        rfl

theorem cell23_3731512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 1, 3, 2].length) (baseStart_3731512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731512 prefixEnd_3731512 := by exact prefixLift 3731512
  have htrace : WordTrace (prefixWord ++ tailWord_3731512) baseStart_3731512 baseEnd_3731512 := by
    simpa [prefixWord, tailWord_3731512, baseEnd_3731512] using wordTrace_append hprefix tailTrace_3731512
  have hstable : (prefixWord ++ tailWord_3731512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731512).length < 2 ^ (prefixWord ++ tailWord_3731512).sum := by decide
  have hdescent : baseEnd_3731512 < baseStart_3731512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731548 : List Nat := [2, 2, 4, 1, 1, 2, 2, 2, 7]
def baseStart_3731548 : Nat := 118140960795 + 3731548 * 2 ^ 59
def prefixEnd_3731548 : Nat := 4983230072969 + 3 ^ 40 * 3731548 * 2
def baseEnd_3731548 : Nat := 212897523258185726109881

theorem tailTrace_3731548 : CollatzResearch.WordTrace tailWord_3731548 prefixEnd_3731548 212897523258185726109881 := by
  unfold tailWord_3731548
  simp only [CollatzResearch.WordTrace]
  refine ⟨68050368342623184252825649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90733824456830912337100865 68050368342623184252825649)
  ·
    refine ⟨51037776256967388189619237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68050368342623184252825649 51037776256967388189619237)
    ·
      refine ⟨9569583048181385285553607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51037776256967388189619237 9569583048181385285553607)
      ·
        refine ⟨14354374572272077928330411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9569583048181385285553607 14354374572272077928330411)
        ·
          refine ⟨21531561858408116892495617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14354374572272077928330411 21531561858408116892495617)
          ·
            refine ⟨16148671393806087669371713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21531561858408116892495617 16148671393806087669371713)
            ·
              refine ⟨12111503545354565752028785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16148671393806087669371713 12111503545354565752028785)
              ·
                refine ⟨9083627659015924314021589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12111503545354565752028785 9083627659015924314021589)
                ·
                  refine ⟨212897523258185726109881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9083627659015924314021589 212897523258185726109881)
                  ·
                    rfl

theorem cell23_3731548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 7].length) (baseStart_3731548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731548 prefixEnd_3731548 := by exact prefixLift 3731548
  have htrace : WordTrace (prefixWord ++ tailWord_3731548) baseStart_3731548 baseEnd_3731548 := by
    simpa [prefixWord, tailWord_3731548, baseEnd_3731548] using wordTrace_append hprefix tailTrace_3731548
  have hstable : (prefixWord ++ tailWord_3731548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731548).length < 2 ^ (prefixWord ++ tailWord_3731548).sum := by decide
  have hdescent : baseEnd_3731548 < baseStart_3731548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731561 : List Nat := [1, 2, 1, 1, 1, 5, 1, 3, 1, 7]
def baseStart_3731561 : Nat := 118140960795 + 3731561 * 2 ^ 59
def prefixEnd_3731561 : Nat := 4983230072969 + 3 ^ 40 * 3731561 * 2
def baseEnd_3731561 : Nat := 638694794857393328042123

theorem tailTrace_3731561 : CollatzResearch.WordTrace tailWord_3731561 prefixEnd_3731561 638694794857393328042123 := by
  unfold tailWord_3731561
  simp only [CollatzResearch.WordTrace]
  refine ⟨136101210834199271725874537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90734140556132847817249691 136101210834199271725874537)
  ·
    refine ⟨102075908125649453794405903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136101210834199271725874537 102075908125649453794405903)
    ·
      refine ⟨153113862188474180691608855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102075908125649453794405903 153113862188474180691608855)
      ·
        refine ⟨229670793282711271037413283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153113862188474180691608855 229670793282711271037413283)
        ·
          refine ⟨344506189924066906556119925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229670793282711271037413283 344506189924066906556119925)
          ·
            refine ⟨32297455305381272489636243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 344506189924066906556119925 32297455305381272489636243)
            ·
              refine ⟨48446182958071908734454365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32297455305381272489636243 48446182958071908734454365)
              ·
                refine ⟨18167318609276965775420387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48446182958071908734454365 18167318609276965775420387)
                ·
                  refine ⟨27250977913915448663130581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18167318609276965775420387 27250977913915448663130581)
                  ·
                    refine ⟨638694794857393328042123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27250977913915448663130581 638694794857393328042123)
                    ·
                      rfl

theorem cell23_3731561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 7].length) (baseStart_3731561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731561 prefixEnd_3731561 := by exact prefixLift 3731561
  have htrace : WordTrace (prefixWord ++ tailWord_3731561) baseStart_3731561 baseEnd_3731561 := by
    simpa [prefixWord, tailWord_3731561, baseEnd_3731561] using wordTrace_append hprefix tailTrace_3731561
  have hstable : (prefixWord ++ tailWord_3731561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731561).length < 2 ^ (prefixWord ++ tailWord_3731561).sum := by decide
  have hdescent : baseEnd_3731561 < baseStart_3731561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731588 : List Nat := [2, 3, 2, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_3731588 : Nat := 118140960795 + 3731588 * 2 ^ 59
def prefixEnd_3731588 : Nat := 4983230072969 + 3 ^ 40 * 3731588 * 2
def baseEnd_3731588 : Nat := 1916098248549851378488745

theorem tailTrace_3731588 : CollatzResearch.WordTrace tailWord_3731588 prefixEnd_3731588 1916098248549851378488745 := by
  unfold tailWord_3731588
  simp only [CollatzResearch.WordTrace]
  refine ⟨68051097802550727668553709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90734797070067636891404945 68051097802550727668553709)
  ·
    refine ⟨25519161675956522875707641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68051097802550727668553709 25519161675956522875707641)
    ·
      refine ⟨19139371256967392156780731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25519161675956522875707641 19139371256967392156780731)
      ·
        refine ⟨28709056885451088235171097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19139371256967392156780731 28709056885451088235171097)
        ·
          refine ⟨21531792664088316176378323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28709056885451088235171097 21531792664088316176378323)
          ·
            refine ⟨32297688996132474264567485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21531792664088316176378323 32297688996132474264567485)
            ·
              refine ⟨12111633373549677849212807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32297688996132474264567485 12111633373549677849212807)
              ·
                refine ⟨18167450060324516773819211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12111633373549677849212807 18167450060324516773819211)
                ·
                  refine ⟨27251175090486775160728817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18167450060324516773819211 27251175090486775160728817)
                  ·
                    refine ⟨20438381317865081370546613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27251175090486775160728817 20438381317865081370546613)
                    ·
                      refine ⟨1916098248549851378488745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20438381317865081370546613 1916098248549851378488745)
                      ·
                        rfl

theorem cell23_3731588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_3731588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731588 prefixEnd_3731588 := by exact prefixLift 3731588
  have htrace : WordTrace (prefixWord ++ tailWord_3731588) baseStart_3731588 baseEnd_3731588 := by
    simpa [prefixWord, tailWord_3731588, baseEnd_3731588] using wordTrace_append hprefix tailTrace_3731588
  have hstable : (prefixWord ++ tailWord_3731588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731588).length < 2 ^ (prefixWord ++ tailWord_3731588).sum := by decide
  have hdescent : baseEnd_3731588 < baseStart_3731588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731601 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 5]
def baseStart_3731601 : Nat := 118140960795 + 3731601 * 2 ^ 59
def prefixEnd_3731601 : Nat := 4983230072969 + 3 ^ 40 * 3731601 * 2
def baseEnd_3731601 : Nat := 1916104923798359827626185

theorem tailTrace_3731601 : CollatzResearch.WordTrace tailWord_3731601 prefixEnd_3731601 1916104923798359827626185 := by
  unfold tailWord_3731601
  simp only [CollatzResearch.WordTrace]
  refine ⟨136102669754054358557330657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90735113169369572371553771 136102669754054358557330657)
  ·
    refine ⟨102077002315540768917997993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136102669754054358557330657 102077002315540768917997993)
    ·
      refine ⟨76557751736655576688498495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102077002315540768917997993 76557751736655576688498495)
      ·
        refine ⟨114836627604983365032747743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76557751736655576688498495 114836627604983365032747743)
        ·
          refine ⟨172254941407475047549121615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114836627604983365032747743 172254941407475047549121615)
          ·
            refine ⟨258382412111212571323682423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172254941407475047549121615 258382412111212571323682423)
            ·
              refine ⟨387573618166818856985523635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258382412111212571323682423 387573618166818856985523635)
              ·
                refine ⟨581360427250228285478285453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387573618166818856985523635 581360427250228285478285453)
                ·
                  refine ⟨218010160218835607054357045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 581360427250228285478285453 218010160218835607054357045)
                  ·
                    refine ⟨20438452520515838161345973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 218010160218835607054357045 20438452520515838161345973)
                    ·
                      refine ⟨1916104923798359827626185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20438452520515838161345973 1916104923798359827626185)
                      ·
                        rfl

theorem cell23_3731601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_3731601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731601 prefixEnd_3731601 := by exact prefixLift 3731601
  have htrace : WordTrace (prefixWord ++ tailWord_3731601) baseStart_3731601 baseEnd_3731601 := by
    simpa [prefixWord, tailWord_3731601, baseEnd_3731601] using wordTrace_append hprefix tailTrace_3731601
  have hstable : (prefixWord ++ tailWord_3731601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731601).length < 2 ^ (prefixWord ++ tailWord_3731601).sum := by decide
  have hdescent : baseEnd_3731601 < baseStart_3731601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731611 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 6]
def baseStart_3731611 : Nat := 118140960795 + 3731611 * 2 ^ 59
def prefixEnd_3731611 : Nat := 4983230072969 + 3 ^ 40 * 3731611 * 2
def baseEnd_3731611 : Nat := 1916110058604904788501139

theorem tailTrace_3731611 : CollatzResearch.WordTrace tailWord_3731611 prefixEnd_3731611 1916110058604904788501139 := by
  unfold tailWord_3731611
  simp only [CollatzResearch.WordTrace]
  refine ⟨136103034484018130265194687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90735356322678753510129791 136103034484018130265194687)
  ·
    refine ⟨204154551726027195397792031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136103034484018130265194687 204154551726027195397792031)
    ·
      refine ⟨306231827589040793096688047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204154551726027195397792031 306231827589040793096688047)
      ·
        refine ⟨459347741383561189645032071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306231827589040793096688047 459347741383561189645032071)
        ·
          refine ⟨689021612075341784467548107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459347741383561189645032071 689021612075341784467548107)
          ·
            refine ⟨1033532418113012676701322161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689021612075341784467548107 1033532418113012676701322161)
            ·
              refine ⟨775149313584759507525991621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1033532418113012676701322161 775149313584759507525991621)
              ·
                refine ⟨145340496297142407661123429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 775149313584759507525991621 145340496297142407661123429)
                ·
                  refine ⟨27251343055714201436460643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145340496297142407661123429 27251343055714201436460643)
                  ·
                    refine ⟨40877014583571302154690965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27251343055714201436460643 40877014583571302154690965)
                    ·
                      refine ⟨1916110058604904788501139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40877014583571302154690965 1916110058604904788501139)
                      ·
                        rfl

theorem cell23_3731611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 6].length) (baseStart_3731611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731611 prefixEnd_3731611 := by exact prefixLift 3731611
  have htrace : WordTrace (prefixWord ++ tailWord_3731611) baseStart_3731611 baseEnd_3731611 := by
    simpa [prefixWord, tailWord_3731611, baseEnd_3731611] using wordTrace_append hprefix tailTrace_3731611
  have hstable : (prefixWord ++ tailWord_3731611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731611).length < 2 ^ (prefixWord ++ tailWord_3731611).sum := by decide
  have hdescent : baseEnd_3731611 < baseStart_3731611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731615 : List Nat := [1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 4]
def baseStart_3731615 : Nat := 118140960795 + 3731615 * 2 ^ 59
def prefixEnd_3731615 : Nat := 4983230072969 + 3 ^ 40 * 3731615 * 2
def baseEnd_3731615 : Nat := 1916112112527522772851121

theorem tailTrace_3731615 : CollatzResearch.WordTrace tailWord_3731615 prefixEnd_3731615 1916112112527522772851121 := by
  unfold tailWord_3731615
  simp only [CollatzResearch.WordTrace]
  refine ⟨136103180376003638948340299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90735453584002425965560199 136103180376003638948340299)
  ·
    refine ⟨204154770564005458422510449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136103180376003638948340299 204154770564005458422510449)
    ·
      refine ⟨153116077923004093816882837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204154770564005458422510449 153116077923004093816882837)
      ·
        refine ⟨7177316152640816897666383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 153116077923004093816882837 7177316152640816897666383)
        ·
          refine ⟨10765974228961225346499575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7177316152640816897666383 10765974228961225346499575)
          ·
            refine ⟨16148961343441838019749363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10765974228961225346499575 16148961343441838019749363)
            ·
              refine ⟨24223442015162757029624045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16148961343441838019749363 24223442015162757029624045)
              ·
                refine ⟨9083790755686033886109017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24223442015162757029624045 9083790755686033886109017)
                ·
                  refine ⟨6812843066764525414581763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9083790755686033886109017 6812843066764525414581763)
                  ·
                    refine ⟨10219264600146788121872645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6812843066764525414581763 10219264600146788121872645)
                    ·
                      refine ⟨1916112112527522772851121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10219264600146788121872645 1916112112527522772851121)
                      ·
                        rfl

theorem cell23_3731615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_3731615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731615 prefixEnd_3731615 := by exact prefixLift 3731615
  have htrace : WordTrace (prefixWord ++ tailWord_3731615) baseStart_3731615 baseEnd_3731615 := by
    simpa [prefixWord, tailWord_3731615, baseEnd_3731615] using wordTrace_append hprefix tailTrace_3731615
  have hstable : (prefixWord ++ tailWord_3731615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731615).length < 2 ^ (prefixWord ++ tailWord_3731615).sum := by decide
  have hdescent : baseEnd_3731615 < baseStart_3731615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731649 : List Nat := [1, 2, 6, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_3731649 : Nat := 118140960795 + 3731649 * 2 ^ 59
def prefixEnd_3731649 : Nat := 4983230072969 + 3 ^ 40 * 3731649 * 2
def baseEnd_3731649 : Nat := 1916129570869775639825965

theorem tailTrace_3731649 : CollatzResearch.WordTrace tailWord_3731649 prefixEnd_3731649 1916129570869775639825965 := by
  unfold tailWord_3731649
  simp only [CollatzResearch.WordTrace]
  refine ⟨136104420457880462755078001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90736280305253641836718667 136104420457880462755078001)
  ·
    refine ⟨102078315343410347066308501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136104420457880462755078001 102078315343410347066308501)
    ·
      refine ⟨4784921031722360018733211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 102078315343410347066308501 4784921031722360018733211)
      ·
        refine ⟨7177381547583540028099817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4784921031722360018733211 7177381547583540028099817)
        ·
          refine ⟨5383036160687655021074863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7177381547583540028099817 5383036160687655021074863)
          ·
            refine ⟨8074554241031482531612295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5383036160687655021074863 8074554241031482531612295)
            ·
              refine ⟨12111831361547223797418443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8074554241031482531612295 12111831361547223797418443)
              ·
                refine ⟨18167747042320835696127665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12111831361547223797418443 18167747042320835696127665)
                ·
                  refine ⟨13625810281740626772095749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18167747042320835696127665 13625810281740626772095749)
                  ·
                    refine ⟨2554839427826367519767953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13625810281740626772095749 2554839427826367519767953)
                    ·
                      refine ⟨1916129570869775639825965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2554839427826367519767953 1916129570869775639825965)
                      ·
                        rfl

theorem cell23_3731649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_3731649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731649 prefixEnd_3731649 := by exact prefixLift 3731649
  have htrace : WordTrace (prefixWord ++ tailWord_3731649) baseStart_3731649 baseEnd_3731649 := by
    simpa [prefixWord, tailWord_3731649, baseEnd_3731649] using wordTrace_append hprefix tailTrace_3731649
  have hstable : (prefixWord ++ tailWord_3731649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731649).length < 2 ^ (prefixWord ++ tailWord_3731649).sum := by decide
  have hdescent : baseEnd_3731649 < baseStart_3731649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731665 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 5, 1, 3]
def baseStart_3731665 : Nat := 118140960795 + 3731665 * 2 ^ 59
def prefixEnd_3731665 : Nat := 4983230072969 + 3 ^ 40 * 3731665 * 2
def baseEnd_3731665 : Nat := 1916137786560247577225891

theorem tailTrace_3731665 : CollatzResearch.WordTrace tailWord_3731665 prefixEnd_3731665 1916137786560247577225891 := by
  unfold tailWord_3731665
  simp only [CollatzResearch.WordTrace]
  refine ⟨136105004025822497487660449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90736669350548331658440299 136105004025822497487660449)
  ·
    refine ⟨102078753019366873115745337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136105004025822497487660449 102078753019366873115745337)
    ·
      refine ⟨76559064764525154836809003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102078753019366873115745337 76559064764525154836809003)
      ·
        refine ⟨114838597146787732255213505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76559064764525154836809003 114838597146787732255213505)
        ·
          refine ⟨86128947860090799191410129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114838597146787732255213505 86128947860090799191410129)
          ·
            refine ⟨64596710895068099393557597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86128947860090799191410129 64596710895068099393557597)
            ·
              refine ⟨24223766585650537272584099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64596710895068099393557597 24223766585650537272584099)
              ·
                refine ⟨36335649878475805908876149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24223766585650537272584099 36335649878475805908876149)
                ·
                  refine ⟨3406467176107106803957139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36335649878475805908876149 3406467176107106803957139)
                  ·
                    refine ⟨5109700764160660205935709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3406467176107106803957139 5109700764160660205935709)
                    ·
                      refine ⟨1916137786560247577225891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5109700764160660205935709 1916137786560247577225891)
                      ·
                        rfl

theorem cell23_3731665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5, 1, 3].length) (baseStart_3731665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731665 prefixEnd_3731665 := by exact prefixLift 3731665
  have htrace : WordTrace (prefixWord ++ tailWord_3731665) baseStart_3731665 baseEnd_3731665 := by
    simpa [prefixWord, tailWord_3731665, baseEnd_3731665] using wordTrace_append hprefix tailTrace_3731665
  have hstable : (prefixWord ++ tailWord_3731665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731665).length < 2 ^ (prefixWord ++ tailWord_3731665).sum := by decide
  have hdescent : baseEnd_3731665 < baseStart_3731665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731669 : List Nat := [1, 3, 2, 4, 2, 2, 1, 1, 2, 2, 3]
def baseStart_3731669 : Nat := 118140960795 + 3731669 * 2 ^ 59
def prefixEnd_3731669 : Nat := 4983230072969 + 3 ^ 40 * 3731669 * 2
def baseEnd_3731669 : Nat := 1916139840482865561575873

theorem tailTrace_3731669 : CollatzResearch.WordTrace tailWord_3731669 prefixEnd_3731669 1916139840482865561575873 := by
  unfold tailWord_3731669
  simp only [CollatzResearch.WordTrace]
  refine ⟨136105149917808006170806061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90736766611872004113870707 136105149917808006170806061)
  ·
    refine ⟨51039431219178002314052273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136105149917808006170806061 51039431219178002314052273)
    ·
      refine ⟨38279573414383501735539205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51039431219178002314052273 38279573414383501735539205)
      ·
        refine ⟨7177420015196906575413601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38279573414383501735539205 7177420015196906575413601)
        ·
          refine ⟨5383065011397679931560201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7177420015196906575413601 5383065011397679931560201)
          ·
            refine ⟨4037298758548259948670151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5383065011397679931560201 4037298758548259948670151)
            ·
              refine ⟨6055948137822389923005227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4037298758548259948670151 6055948137822389923005227)
              ·
                refine ⟨9083922206733584884507841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6055948137822389923005227 9083922206733584884507841)
                ·
                  refine ⟨6812941655050188663380881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9083922206733584884507841 6812941655050188663380881)
                  ·
                    refine ⟨5109706241287641497535661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6812941655050188663380881 5109706241287641497535661)
                    ·
                      refine ⟨1916139840482865561575873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5109706241287641497535661 1916139840482865561575873)
                      ·
                        rfl

theorem cell23_3731669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_3731669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731669 prefixEnd_3731669 := by exact prefixLift 3731669
  have htrace : WordTrace (prefixWord ++ tailWord_3731669) baseStart_3731669 baseEnd_3731669 := by
    simpa [prefixWord, tailWord_3731669, baseEnd_3731669] using wordTrace_append hprefix tailTrace_3731669
  have hstable : (prefixWord ++ tailWord_3731669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731669).length < 2 ^ (prefixWord ++ tailWord_3731669).sum := by decide
  have hdescent : baseEnd_3731669 < baseStart_3731669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731719 : List Nat := [1, 1, 4, 5, 1, 1, 2, 2, 1, 5]
def baseStart_3731719 : Nat := 118140960795 + 3731719 * 2 ^ 59
def prefixEnd_3731719 : Nat := 4983230072969 + 3 ^ 40 * 3731719 * 2
def baseEnd_3731719 : Nat := 638721838171863455316881

theorem tailTrace_3731719 : CollatzResearch.WordTrace tailWord_3731719 prefixEnd_3731719 638721838171863455316881 := by
  unfold tailWord_3731719
  simp only [CollatzResearch.WordTrace]
  refine ⟨136106973567626864710126211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90737982378417909806750807 136106973567626864710126211)
  ·
    refine ⟨204160460351440297065189317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136106973567626864710126211 204160460351440297065189317)
    ·
      refine ⟨38280086315895055699722997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204160460351440297065189317 38280086315895055699722997)
      ·
        refine ⟨3588758092115161471849031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38280086315895055699722997 3588758092115161471849031)
        ·
          refine ⟨5383137138172742207773547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3588758092115161471849031 5383137138172742207773547)
          ·
            refine ⟨8074705707259113311660321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5383137138172742207773547 8074705707259113311660321)
            ·
              refine ⟨6056029280444334983745241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8074705707259113311660321 6056029280444334983745241)
              ·
                refine ⟨4542021960333251237808931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6056029280444334983745241 4542021960333251237808931)
                ·
                  refine ⟨6813032940499876856713397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4542021960333251237808931 6813032940499876856713397)
                  ·
                    refine ⟨638721838171863455316881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6813032940499876856713397 638721838171863455316881)
                    ·
                      rfl

theorem cell23_3731719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_3731719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731719 prefixEnd_3731719 := by exact prefixLift 3731719
  have htrace : WordTrace (prefixWord ++ tailWord_3731719) baseStart_3731719 baseEnd_3731719 := by
    simpa [prefixWord, tailWord_3731719, baseEnd_3731719] using wordTrace_append hprefix tailTrace_3731719
  have hstable : (prefixWord ++ tailWord_3731719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731719).length < 2 ^ (prefixWord ++ tailWord_3731719).sum := by decide
  have hdescent : baseEnd_3731719 < baseStart_3731719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3731812 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 3, 4, 2]
def baseStart_3731812 : Nat := 118140960795 + 3731812 * 2 ^ 59
def prefixEnd_3731812 : Nat := 4983230072969 + 3 ^ 40 * 3731812 * 2
def baseEnd_3731812 : Nat := 1916213268216458502087715

theorem tailTrace_3731812 : CollatzResearch.WordTrace tailWord_3731812 prefixEnd_3731812 1916213268216458502087715 := by
  unfold tailWord_3731812
  simp only [CollatzResearch.WordTrace]
  refine ⟨68055182778144970796630845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90740243704193294395507793 68055182778144970796630845)
  ·
    refine ⟨25520693541804364048736567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68055182778144970796630845 25520693541804364048736567)
    ·
      refine ⟨38281040312706546073104851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25520693541804364048736567 38281040312706546073104851)
      ·
        refine ⟨57421560469059819109657277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38281040312706546073104851 57421560469059819109657277)
        ·
          refine ⟨21533085175897432166121479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57421560469059819109657277 21533085175897432166121479)
          ·
            refine ⟨32299627763846148249182219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21533085175897432166121479 32299627763846148249182219)
            ·
              refine ⟨48449441645769222373773329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32299627763846148249182219 48449441645769222373773329)
              ·
                refine ⟨36337081234326916780329997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48449441645769222373773329 36337081234326916780329997)
                ·
                  refine ⟨13626405462872593792623749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36337081234326916780329997 13626405462872593792623749)
                  ·
                    refine ⟨2554951024288611336116953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13626405462872593792623749 2554951024288611336116953)
                    ·
                      refine ⟨1916213268216458502087715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2554951024288611336116953 1916213268216458502087715)
                      ·
                        rfl

theorem cell23_3731812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 3, 4, 2].length) (baseStart_3731812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3731812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3731812 prefixEnd_3731812 := by exact prefixLift 3731812
  have htrace : WordTrace (prefixWord ++ tailWord_3731812) baseStart_3731812 baseEnd_3731812 := by
    simpa [prefixWord, tailWord_3731812, baseEnd_3731812] using wordTrace_append hprefix tailTrace_3731812
  have hstable : (prefixWord ++ tailWord_3731812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3731812).length < 2 ^ (prefixWord ++ tailWord_3731812).sum := by decide
  have hdescent : baseEnd_3731812 < baseStart_3731812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3731812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
