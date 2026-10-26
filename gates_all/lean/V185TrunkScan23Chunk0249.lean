import V185TrunkScan23Chunk0248

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1473724 : List Nat := [2, 2, 2, 3, 2, 2, 1, 1, 4, 2, 2]
def baseStart_1473724 : Nat := 118140960795 + 1473724 * 2 ^ 59
def prefixEnd_1473724 : Nat := 4983230072969 + 3 ^ 40 * 1473724 * 2
def baseEnd_1473724 : Nat := 756728764066697281772473

theorem tailTrace_1473724 : CollatzResearch.WordTrace tailWord_1473724 prefixEnd_1473724 756728764066697281772473 := by
  unfold tailWord_1473724
  simp only [CollatzResearch.WordTrace]
  refine ⟨26875565056478557433042113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35834086741971409910722817 26875565056478557433042113)
  ·
    refine ⟨20156673792358918074781585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26875565056478557433042113 20156673792358918074781585)
    ·
      refine ⟨15117505344269188556086189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20156673792358918074781585 15117505344269188556086189)
      ·
        refine ⟨5669064504100945708532321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15117505344269188556086189 5669064504100945708532321)
        ·
          refine ⟨4251798378075709281399241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5669064504100945708532321 4251798378075709281399241)
          ·
            refine ⟨3188848783556781961049431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4251798378075709281399241 3188848783556781961049431)
            ·
              refine ⟨4783273175335172941574147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3188848783556781961049431 4783273175335172941574147)
              ·
                refine ⟨7174909763002759412361221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4783273175335172941574147 7174909763002759412361221)
                ·
                  refine ⟨1345295580563017389817729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7174909763002759412361221 1345295580563017389817729)
                  ·
                    refine ⟨1008971685422263042363297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1345295580563017389817729 1008971685422263042363297)
                    ·
                      refine ⟨756728764066697281772473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1008971685422263042363297 756728764066697281772473)
                      ·
                        rfl

theorem cell23_1473724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_1473724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473724 prefixEnd_1473724 := by exact prefixLift 1473724
  have htrace : WordTrace (prefixWord ++ tailWord_1473724) baseStart_1473724 baseEnd_1473724 := by
    simpa [prefixWord, tailWord_1473724, baseEnd_1473724] using wordTrace_append hprefix tailTrace_1473724
  have hstable : (prefixWord ++ tailWord_1473724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473724).length < 2 ^ (prefixWord ++ tailWord_1473724).sum := by decide
  have hdescent : baseEnd_1473724 < baseStart_1473724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473743 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 6, 5]
def baseStart_1473743 : Nat := 118140960795 + 1473743 * 2 ^ 59
def prefixEnd_1473743 : Nat := 4983230072969 + 3 ^ 40 * 1473743 * 2
def baseEnd_1473743 : Nat := 252246173399710902478295

theorem tailTrace_1473743 : CollatzResearch.WordTrace tailWord_1473743 prefixEnd_1473743 252246173399710902478295 := by
  unfold tailWord_1473743
  simp only [CollatzResearch.WordTrace]
  refine ⟨53751823099888281111025883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35834548733258854074017255 53751823099888281111025883)
  ·
    refine ⟨80627734649832421666538825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53751823099888281111025883 80627734649832421666538825)
    ·
      refine ⟨60470800987374316249904119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80627734649832421666538825 60470800987374316249904119)
      ·
        refine ⟨90706201481061474374856179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60470800987374316249904119 90706201481061474374856179)
        ·
          refine ⟨136059302221592211562284269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90706201481061474374856179 136059302221592211562284269)
          ·
            refine ⟨51022238333097079335856601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136059302221592211562284269 51022238333097079335856601)
            ·
              refine ⟨38266678749822809501892451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51022238333097079335856601 38266678749822809501892451)
              ·
                refine ⟨57400018124734214252838677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38266678749822809501892451 57400018124734214252838677)
                ·
                  refine ⟨2690625849596916293101813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57400018124734214252838677 2690625849596916293101813)
                  ·
                    refine ⟨252246173399710902478295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2690625849596916293101813 252246173399710902478295)
                    ·
                      rfl

theorem cell23_1473743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 5].length) (baseStart_1473743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473743 prefixEnd_1473743 := by exact prefixLift 1473743
  have htrace : WordTrace (prefixWord ++ tailWord_1473743) baseStart_1473743 baseEnd_1473743 := by
    simpa [prefixWord, tailWord_1473743, baseEnd_1473743] using wordTrace_append hprefix tailTrace_1473743
  have hstable : (prefixWord ++ tailWord_1473743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473743).length < 2 ^ (prefixWord ++ tailWord_1473743).sum := by decide
  have hdescent : baseEnd_1473743 < baseStart_1473743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473753 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 3, 2, 5]
def baseStart_1473753 : Nat := 118140960795 + 1473753 * 2 ^ 59
def prefixEnd_1473753 : Nat := 4983230072969 + 3 ^ 40 * 1473753 * 2
def baseEnd_1473753 : Nat := 756743655005677668309839

theorem tailTrace_1473753 : CollatzResearch.WordTrace tailWord_1473753 prefixEnd_1473753 756743655005677668309839 := by
  unfold tailWord_1473753
  simp only [CollatzResearch.WordTrace]
  refine ⟨53752187829852052818889913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35834791886568035212593275 53752187829852052818889913)
  ·
    refine ⟨40314140872389039614167435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53752187829852052818889913 40314140872389039614167435)
    ·
      refine ⟨60471211308583559421251153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40314140872389039614167435 60471211308583559421251153)
      ·
        refine ⟨45353408481437669565938365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60471211308583559421251153 45353408481437669565938365)
        ·
          refine ⟨17007528180539126087226887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45353408481437669565938365 17007528180539126087226887)
          ·
            refine ⟨25511292270808689130840331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17007528180539126087226887 25511292270808689130840331)
            ·
              refine ⟨38266938406213033696260497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25511292270808689130840331 38266938406213033696260497)
              ·
                refine ⟨28700203804659775272195373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38266938406213033696260497 28700203804659775272195373)
                ·
                  refine ⟨10762576426747415727073265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28700203804659775272195373 10762576426747415727073265)
                  ·
                    refine ⟨8071932320060561795304949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10762576426747415727073265 8071932320060561795304949)
                    ·
                      refine ⟨756743655005677668309839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8071932320060561795304949 756743655005677668309839)
                      ·
                        rfl

theorem cell23_1473753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_1473753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473753 prefixEnd_1473753 := by exact prefixLift 1473753
  have htrace : WordTrace (prefixWord ++ tailWord_1473753) baseStart_1473753 baseEnd_1473753 := by
    simpa [prefixWord, tailWord_1473753, baseEnd_1473753] using wordTrace_append hprefix tailTrace_1473753
  have hstable : (prefixWord ++ tailWord_1473753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473753).length < 2 ^ (prefixWord ++ tailWord_1473753).sum := by decide
  have hdescent : baseEnd_1473753 < baseStart_1473753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473783 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 5]
def baseStart_1473783 : Nat := 118140960795 + 1473783 * 2 ^ 59
def prefixEnd_1473783 : Nat := 4983230072969 + 3 ^ 40 * 1473783 * 2
def baseEnd_1473783 : Nat := 756759059425312550934701

theorem tailTrace_1473783 : CollatzResearch.WordTrace tailWord_1473783 prefixEnd_1473783 756759059425312550934701 := by
  unfold tailWord_1473783
  simp only [CollatzResearch.WordTrace]
  refine ⟨53753282019743367942482003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35835521346495578628321335 53753282019743367942482003)
  ·
    refine ⟨80629923029615051913723005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53753282019743367942482003 80629923029615051913723005)
    ·
      refine ⟨30236221136105644467646127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80629923029615051913723005 30236221136105644467646127)
      ·
        refine ⟨45354331704158466701469191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30236221136105644467646127 45354331704158466701469191)
        ·
          refine ⟨68031497556237700052203787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45354331704158466701469191 68031497556237700052203787)
          ·
            refine ⟨102047246334356550078305681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68031497556237700052203787 102047246334356550078305681)
            ·
              refine ⟨76535434750767412558729261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102047246334356550078305681 76535434750767412558729261)
              ·
                refine ⟨28700788031537779709523473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76535434750767412558729261 28700788031537779709523473)
                ·
                  refine ⟨21525591023653334782142605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28700788031537779709523473 21525591023653334782142605)
                  ·
                    refine ⟨8072096633870000543303477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21525591023653334782142605 8072096633870000543303477)
                    ·
                      refine ⟨756759059425312550934701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8072096633870000543303477 756759059425312550934701)
                      ·
                        rfl

theorem cell23_1473783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_1473783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473783 prefixEnd_1473783 := by exact prefixLift 1473783
  have htrace : WordTrace (prefixWord ++ tailWord_1473783) baseStart_1473783 baseEnd_1473783 := by
    simpa [prefixWord, tailWord_1473783, baseEnd_1473783] using wordTrace_append hprefix tailTrace_1473783
  have hstable : (prefixWord ++ tailWord_1473783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473783).length < 2 ^ (prefixWord ++ tailWord_1473783).sum := by decide
  have hdescent : baseEnd_1473783 < baseStart_1473783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473833 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 4, 9]
def baseStart_1473833 : Nat := 118140960795 + 1473833 * 2 ^ 59
def prefixEnd_1473833 : Nat := 4983230072969 + 3 ^ 40 * 1473833 * 2
def baseEnd_1473833 : Nat := 252261577819345785103157

theorem tailTrace_1473833 : CollatzResearch.WordTrace tailWord_1473833 prefixEnd_1473833 252261577819345785103157 := by
  unfold tailWord_1473833
  simp only [CollatzResearch.WordTrace]
  refine ⟨53755105669562226481802153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35836737113041484321201435 53755105669562226481802153)
  ·
    refine ⟨40316329252171669861351615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53755105669562226481802153 40316329252171669861351615)
    ·
      refine ⟨60474493878257504792027423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40316329252171669861351615 60474493878257504792027423)
      ·
        refine ⟨90711740817386257188041135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60474493878257504792027423 90711740817386257188041135)
        ·
          refine ⟨136067611226079385782061703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90711740817386257188041135 136067611226079385782061703)
          ·
            refine ⟨204101416839119078673092555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136067611226079385782061703 204101416839119078673092555)
            ·
              refine ⟨306152125258678618009638833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204101416839119078673092555 306152125258678618009638833)
              ·
                refine ⟨229614093944008963507229125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 306152125258678618009638833 229614093944008963507229125)
                ·
                  refine ⟨43052642614501680657605461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 229614093944008963507229125 43052642614501680657605461)
                  ·
                    refine ⟨252261577819345785103157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 43052642614501680657605461 252261577819345785103157)
                    ·
                      rfl

theorem cell23_1473833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 9].length) (baseStart_1473833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473833 prefixEnd_1473833 := by exact prefixLift 1473833
  have htrace : WordTrace (prefixWord ++ tailWord_1473833) baseStart_1473833 baseEnd_1473833 := by
    simpa [prefixWord, tailWord_1473833, baseEnd_1473833] using wordTrace_append hprefix tailTrace_1473833
  have hstable : (prefixWord ++ tailWord_1473833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473833).length < 2 ^ (prefixWord ++ tailWord_1473833).sum := by decide
  have hdescent : baseEnd_1473833 < baseStart_1473833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473834 : List Nat := [3, 1, 4, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_1473834 : Nat := 118140960795 + 1473834 * 2 ^ 59
def prefixEnd_1473834 : Nat := 4983230072969 + 3 ^ 40 * 1473834 * 2
def baseEnd_1473834 : Nat := 756785246938691851396967

theorem tailTrace_1473834 : CollatzResearch.WordTrace tailWord_1473834 prefixEnd_1473834 756785246938691851396967 := by
  unfold tailWord_1473834
  simp only [CollatzResearch.WordTrace]
  refine ⟨13438785535639650913147139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35836761428372402435059037 13438785535639650913147139)
  ·
    refine ⟨20158178303459476369720709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13438785535639650913147139 20158178303459476369720709)
    ·
      refine ⟨3779658431898651819322633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20158178303459476369720709 3779658431898651819322633)
      ·
        refine ⟨2834743823923988864491975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3779658431898651819322633 2834743823923988864491975)
        ·
          refine ⟨4252115735885983296737963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2834743823923988864491975 4252115735885983296737963)
          ·
            refine ⟨6378173603828974945106945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4252115735885983296737963 6378173603828974945106945)
            ·
              refine ⟨4783630202871731208830209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6378173603828974945106945 4783630202871731208830209)
              ·
                refine ⟨3587722652153798406622657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4783630202871731208830209 3587722652153798406622657)
                ·
                  refine ⟨2690791989115348804966993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3587722652153798406622657 2690791989115348804966993)
                  ·
                    refine ⟨2018093991836511603725245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2690791989115348804966993 2018093991836511603725245)
                    ·
                      refine ⟨756785246938691851396967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2018093991836511603725245 756785246938691851396967)
                      ·
                        rfl

theorem cell23_1473834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_1473834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473834 prefixEnd_1473834 := by exact prefixLift 1473834
  have htrace : WordTrace (prefixWord ++ tailWord_1473834) baseStart_1473834 baseEnd_1473834 := by
    simpa [prefixWord, tailWord_1473834, baseEnd_1473834] using wordTrace_append hprefix tailTrace_1473834
  have hstable : (prefixWord ++ tailWord_1473834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473834).length < 2 ^ (prefixWord ++ tailWord_1473834).sum := by decide
  have hdescent : baseEnd_1473834 < baseStart_1473834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473841 : List Nat := [1, 2, 2, 3, 3, 1, 4, 2, 1, 4]
def baseStart_1473841 : Nat := 118140960795 + 1473841 * 2 ^ 59
def prefixEnd_1473841 : Nat := 4983230072969 + 3 ^ 40 * 1473841 * 2
def baseEnd_1473841 : Nat := 252262947101091108003145

theorem tailTrace_1473841 : CollatzResearch.WordTrace tailWord_1473841 prefixEnd_1473841 252262947101091108003145 := by
  unfold tailWord_1473841
  simp only [CollatzResearch.WordTrace]
  refine ⟨53755397453533243848093377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35836931635688829232062251 53755397453533243848093377)
  ·
    refine ⟨40316548090149932886070033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53755397453533243848093377 40316548090149932886070033)
    ·
      refine ⟨30237411067612449664552525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40316548090149932886070033 30237411067612449664552525)
      ·
        refine ⟨11339029150354668624207197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30237411067612449664552525 11339029150354668624207197)
        ·
          refine ⟨4252135931383000734077699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11339029150354668624207197 4252135931383000734077699)
          ·
            refine ⟨6378203897074501101116549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4252135931383000734077699 6378203897074501101116549)
            ·
              refine ⟨1195913230701468956459353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6378203897074501101116549 1195913230701468956459353)
              ·
                refine ⟨896934923026101717344515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1195913230701468956459353 896934923026101717344515)
                ·
                  refine ⟨1345402384539152576016773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 896934923026101717344515 1345402384539152576016773)
                  ·
                    refine ⟨252262947101091108003145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1345402384539152576016773 252262947101091108003145)
                    ·
                      rfl

theorem cell23_1473841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2, 1, 4].length) (baseStart_1473841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473841 prefixEnd_1473841 := by exact prefixLift 1473841
  have htrace : WordTrace (prefixWord ++ tailWord_1473841) baseStart_1473841 baseEnd_1473841 := by
    simpa [prefixWord, tailWord_1473841, baseEnd_1473841] using wordTrace_append hprefix tailTrace_1473841
  have hstable : (prefixWord ++ tailWord_1473841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473841).length < 2 ^ (prefixWord ++ tailWord_1473841).sum := by decide
  have hdescent : baseEnd_1473841 < baseStart_1473841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473850 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 5, 5]
def baseStart_1473850 : Nat := 118140960795 + 1473850 * 2 ^ 59
def prefixEnd_1473850 : Nat := 4983230072969 + 3 ^ 40 * 1473850 * 2
def baseEnd_1473850 : Nat := 252264487543054596265631

theorem tailTrace_1473850 : CollatzResearch.WordTrace tailWord_1473850 prefixEnd_1473850 252264487543054596265631 := by
  unfold tailWord_1473850
  simp only [CollatzResearch.WordTrace]
  refine ⟨13438931427625159596292751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35837150473667092256780669 13438931427625159596292751)
  ·
    refine ⟨20158397141437739394439127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13438931427625159596292751 20158397141437739394439127)
    ·
      refine ⟨30237595712156609091658691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20158397141437739394439127 30237595712156609091658691)
      ·
        refine ⟨45356393568234913637488037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30237595712156609091658691 45356393568234913637488037)
        ·
          refine ⟨8504323794044046307029007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45356393568234913637488037 8504323794044046307029007)
          ·
            refine ⟨12756485691066069460543511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8504323794044046307029007 12756485691066069460543511)
            ·
              refine ⟨19134728536599104190815267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12756485691066069460543511 19134728536599104190815267)
              ·
                refine ⟨28702092804898656286222901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19134728536599104190815267 28702092804898656286222901)
                ·
                  refine ⟨2690821200459249026833397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28702092804898656286222901 2690821200459249026833397)
                  ·
                    refine ⟨252264487543054596265631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2690821200459249026833397 252264487543054596265631)
                    ·
                      rfl

theorem cell23_1473850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 5, 5].length) (baseStart_1473850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473850 prefixEnd_1473850 := by exact prefixLift 1473850
  have htrace : WordTrace (prefixWord ++ tailWord_1473850) baseStart_1473850 baseEnd_1473850 := by
    simpa [prefixWord, tailWord_1473850, baseEnd_1473850] using wordTrace_append hprefix tailTrace_1473850
  have hstable : (prefixWord ++ tailWord_1473850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473850).length < 2 ^ (prefixWord ++ tailWord_1473850).sum := by decide
  have hdescent : baseEnd_1473850 < baseStart_1473850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473880 : List Nat := [2, 1, 2, 2, 1, 1, 3, 4, 1, 6]
def baseStart_1473880 : Nat := 118140960795 + 1473880 * 2 ^ 59
def prefixEnd_1473880 : Nat := 4983230072969 + 3 ^ 40 * 1473880 * 2
def baseEnd_1473880 : Nat := 252269622349599557140585

theorem tailTrace_1473880 : CollatzResearch.WordTrace tailWord_1473880 prefixEnd_1473880 252269622349599557140585 := by
  unfold tailWord_1473880
  simp only [CollatzResearch.WordTrace]
  refine ⟨26878409950195976754381547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35837879933594635672508729 26878409950195976754381547)
  ·
    refine ⟨40317614925293965131572321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26878409950195976754381547 40317614925293965131572321)
    ·
      refine ⟨30238211193970473848679241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40317614925293965131572321 30238211193970473848679241)
      ·
        refine ⟨22678658395477855386509431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30238211193970473848679241 22678658395477855386509431)
        ·
          refine ⟨34017987593216783079764147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22678658395477855386509431 34017987593216783079764147)
          ·
            refine ⟨51026981389825174619646221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34017987593216783079764147 51026981389825174619646221)
            ·
              refine ⟨19135118021184440482367333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51026981389825174619646221 19135118021184440482367333)
              ·
                refine ⟨3587834628972082590443875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19135118021184440482367333 3587834628972082590443875)
                ·
                  refine ⟨5381751943458123885665813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3587834628972082590443875 5381751943458123885665813)
                  ·
                    refine ⟨252269622349599557140585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5381751943458123885665813 252269622349599557140585)
                    ·
                      rfl

theorem cell23_1473880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 1, 6].length) (baseStart_1473880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473880 prefixEnd_1473880 := by exact prefixLift 1473880
  have htrace : WordTrace (prefixWord ++ tailWord_1473880) baseStart_1473880 baseEnd_1473880 := by
    simpa [prefixWord, tailWord_1473880, baseEnd_1473880] using wordTrace_append hprefix tailTrace_1473880
  have hstable : (prefixWord ++ tailWord_1473880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473880).length < 2 ^ (prefixWord ++ tailWord_1473880).sum := by decide
  have hdescent : baseEnd_1473880 < baseStart_1473880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473897 : List Nat := [1, 2, 1, 1, 1, 3, 2, 6, 2, 4]
def baseStart_1473897 : Nat := 118140960795 + 1473897 * 2 ^ 59
def prefixEnd_1473897 : Nat := 4983230072969 + 3 ^ 40 * 1473897 * 2
def baseEnd_1473897 : Nat := 252272532073308368303059

theorem tailTrace_1473897 : CollatzResearch.WordTrace tailWord_1473897 prefixEnd_1473897 252272532073308368303059 := by
  unfold tailWord_1473897
  simp only [CollatzResearch.WordTrace]
  refine ⟨53757439941330365412131945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35838293294220243608087963 53757439941330365412131945)
  ·
    refine ⟨40318079955997774059098959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53757439941330365412131945 40318079955997774059098959)
    ·
      refine ⟨60477119933996661088648439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40318079955997774059098959 60477119933996661088648439)
      ·
        refine ⟨90715679900994991632972659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60477119933996661088648439 90715679900994991632972659)
        ·
          refine ⟨136073519851492487449458989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90715679900994991632972659 136073519851492487449458989)
          ·
            refine ⟨51027569944309682793547121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136073519851492487449458989 51027569944309682793547121)
            ·
              refine ⟨38270677458232262095160341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51027569944309682793547121 38270677458232262095160341)
              ·
                refine ⟨1793938005854637285710641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38270677458232262095160341 1793938005854637285710641)
                ·
                  refine ⟨1345453504390977964282981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1793938005854637285710641 1345453504390977964282981)
                  ·
                    refine ⟨252272532073308368303059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1345453504390977964282981 252272532073308368303059)
                    ·
                      rfl

theorem cell23_1473897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2, 4].length) (baseStart_1473897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473897 prefixEnd_1473897 := by exact prefixLift 1473897
  have htrace : WordTrace (prefixWord ++ tailWord_1473897) baseStart_1473897 baseEnd_1473897 := by
    simpa [prefixWord, tailWord_1473897, baseEnd_1473897] using wordTrace_append hprefix tailTrace_1473897
  have hstable : (prefixWord ++ tailWord_1473897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473897).length < 2 ^ (prefixWord ++ tailWord_1473897).sum := by decide
  have hdescent : baseEnd_1473897 < baseStart_1473897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473918 : List Nat := [4, 2, 3, 2, 1, 1, 2, 2, 1, 5]
def baseStart_1473918 : Nat := 118140960795 + 1473918 * 2 ^ 59
def prefixEnd_1473918 : Nat := 4983230072969 + 3 ^ 40 * 1473918 * 2
def baseEnd_1473918 : Nat := 252276126437889840915527

theorem tailTrace_1473918 : CollatzResearch.WordTrace tailWord_1473918 prefixEnd_1473918 252276126437889840915527 := by
  unfold tailWord_1473918
  simp only [CollatzResearch.WordTrace]
  refine ⟨6719775734281785749830801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35838803916169523999097605 6719775734281785749830801)
  ·
    refine ⟨5039831800711339312373101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6719775734281785749830801 5039831800711339312373101)
    ·
      refine ⟨1889936925266752242139913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5039831800711339312373101 1889936925266752242139913)
      ·
        refine ⟨1417452693950064181604935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1889936925266752242139913 1417452693950064181604935)
        ·
          refine ⟨2126179040925096272407403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1417452693950064181604935 2126179040925096272407403)
          ·
            refine ⟨3189268561387644408611105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2126179040925096272407403 3189268561387644408611105)
            ·
              refine ⟨2391951421040733306458329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3189268561387644408611105 2391951421040733306458329)
              ·
                refine ⟨1793963565780549979843747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2391951421040733306458329 1793963565780549979843747)
                ·
                  refine ⟨2690945348670824969765621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1793963565780549979843747 2690945348670824969765621)
                  ·
                    refine ⟨252276126437889840915527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2690945348670824969765621 252276126437889840915527)
                    ·
                      rfl

theorem cell23_1473918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_1473918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473918 prefixEnd_1473918 := by exact prefixLift 1473918
  have htrace : WordTrace (prefixWord ++ tailWord_1473918) baseStart_1473918 baseEnd_1473918 := by
    simpa [prefixWord, tailWord_1473918, baseEnd_1473918] using wordTrace_append hprefix tailTrace_1473918
  have hstable : (prefixWord ++ tailWord_1473918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473918).length < 2 ^ (prefixWord ++ tailWord_1473918).sum := by decide
  have hdescent : baseEnd_1473918 < baseStart_1473918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473921 : List Nat := [1, 2, 4, 3, 2, 1, 2, 2, 1, 1, 4]
def baseStart_1473921 : Nat := 118140960795 + 1473921 * 2 ^ 59
def prefixEnd_1473921 : Nat := 4983230072969 + 3 ^ 40 * 1473921 * 2
def baseEnd_1473921 : Nat := 756829919755633011009067

theorem tailTrace_1473921 : CollatzResearch.WordTrace tailWord_1473921 prefixEnd_1473921 756829919755633011009067 := by
  unfold tailWord_1473921
  simp only [CollatzResearch.WordTrace]
  refine ⟨53758315293243417511005617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35838876862162278340670411 53758315293243417511005617)
  ·
    refine ⟨40318736469932563133254213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53758315293243417511005617 40318736469932563133254213)
    ·
      refine ⟨7559763088112355587485165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40318736469932563133254213 7559763088112355587485165)
      ·
        refine ⟨2834911158042133345306937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7559763088112355587485165 2834911158042133345306937)
        ·
          refine ⟨2126183368531600008980203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2834911158042133345306937 2126183368531600008980203)
          ·
            refine ⟨3189275052797400013470305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2126183368531600008980203 3189275052797400013470305)
            ·
              refine ⟨2391956289598050010102729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3189275052797400013470305 2391956289598050010102729)
              ·
                refine ⟨1793967217198537507577047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2391956289598050010102729 1793967217198537507577047)
                ·
                  refine ⟨2690950825797806261365571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1793967217198537507577047 2690950825797806261365571)
                  ·
                    refine ⟨4036426238696709392048357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2690950825797806261365571 4036426238696709392048357)
                    ·
                      refine ⟨756829919755633011009067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4036426238696709392048357 756829919755633011009067)
                      ·
                        rfl

theorem cell23_1473921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_1473921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473921 prefixEnd_1473921 := by exact prefixLift 1473921
  have htrace : WordTrace (prefixWord ++ tailWord_1473921) baseStart_1473921 baseEnd_1473921 := by
    simpa [prefixWord, tailWord_1473921, baseEnd_1473921] using wordTrace_append hprefix tailTrace_1473921
  have hstable : (prefixWord ++ tailWord_1473921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473921).length < 2 ^ (prefixWord ++ tailWord_1473921).sum := by decide
  have hdescent : baseEnd_1473921 < baseStart_1473921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473924 : List Nat := [2, 3, 2, 1, 1, 3, 1, 4, 1, 2, 3]
def baseStart_1473924 : Nat := 118140960795 + 1473924 * 2 ^ 59
def prefixEnd_1473924 : Nat := 4983230072969 + 3 ^ 40 * 1473924 * 2
def baseEnd_1473924 : Nat := 756831460197596499271553

theorem tailTrace_1473924 : CollatzResearch.WordTrace tailWord_1473924 prefixEnd_1473924 756831460197596499271553 := by
  unfold tailWord_1473924
  simp only [CollatzResearch.WordTrace]
  refine ⟨26879212356116274511682413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35838949808155032682243217 26879212356116274511682413)
  ·
    refine ⟨10079704633543602941880905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26879212356116274511682413 10079704633543602941880905)
    ·
      refine ⟨7559778475157702206410679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10079704633543602941880905 7559778475157702206410679)
      ·
        refine ⟨11339667712736553309616019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7559778475157702206410679 11339667712736553309616019)
        ·
          refine ⟨17009501569104829964424029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11339667712736553309616019 17009501569104829964424029)
          ·
            refine ⟨6378563088414311236659011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17009501569104829964424029 6378563088414311236659011)
            ·
              refine ⟨9567844632621466854988517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6378563088414311236659011 9567844632621466854988517)
              ·
                refine ⟨1793970868616525035310347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9567844632621466854988517 1793970868616525035310347)
                ·
                  refine ⟨2690956302924787552965521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1793970868616525035310347 2690956302924787552965521)
                  ·
                    refine ⟨2018217227193590664724141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2690956302924787552965521 2018217227193590664724141)
                    ·
                      refine ⟨756831460197596499271553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2018217227193590664724141 756831460197596499271553)
                      ·
                        rfl

theorem cell23_1473924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_1473924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473924 prefixEnd_1473924 := by exact prefixLift 1473924
  have htrace : WordTrace (prefixWord ++ tailWord_1473924) baseStart_1473924 baseEnd_1473924 := by
    simpa [prefixWord, tailWord_1473924, baseEnd_1473924] using wordTrace_append hprefix tailTrace_1473924
  have hstable : (prefixWord ++ tailWord_1473924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473924).length < 2 ^ (prefixWord ++ tailWord_1473924).sum := by decide
  have hdescent : baseEnd_1473924 < baseStart_1473924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473927 : List Nat := [1, 1, 4, 2, 2, 2, 4, 7]
def baseStart_1473927 : Nat := 118140960795 + 1473927 * 2 ^ 59
def prefixEnd_1473927 : Nat := 4983230072969 + 3 ^ 40 * 1473927 * 2
def baseEnd_1473927 : Nat := 28030851875539258797557

theorem tailTrace_1473927 : CollatzResearch.WordTrace tailWord_1473927 prefixEnd_1473927 28030851875539258797557 := by
  unfold tailWord_1473927
  simp only [CollatzResearch.WordTrace]
  refine ⟨53758534131221680535724035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35839022754147787023816023 53758534131221680535724035)
  ·
    refine ⟨80637801196832520803586053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53758534131221680535724035 80637801196832520803586053)
    ·
      refine ⟨15119587724406097650672385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80637801196832520803586053 15119587724406097650672385)
      ·
        refine ⟨11339690793304573238004289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15119587724406097650672385 11339690793304573238004289)
        ·
          refine ⟨8504768094978429928503217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11339690793304573238004289 8504768094978429928503217)
          ·
            refine ⟨6378576071233822446377413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8504768094978429928503217 6378576071233822446377413)
            ·
              refine ⟨1195983013356341708695765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6378576071233822446377413 1195983013356341708695765)
              ·
                refine ⟨28030851875539258797557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1195983013356341708695765 28030851875539258797557)
                ·
                  rfl

theorem cell23_1473927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 7].length) (baseStart_1473927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473927 prefixEnd_1473927 := by exact prefixLift 1473927
  have htrace : WordTrace (prefixWord ++ tailWord_1473927) baseStart_1473927 baseEnd_1473927 := by
    simpa [prefixWord, tailWord_1473927, baseEnd_1473927] using wordTrace_append hprefix tailTrace_1473927
  have hstable : (prefixWord ++ tailWord_1473927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473927).length < 2 ^ (prefixWord ++ tailWord_1473927).sum := by decide
  have hdescent : baseEnd_1473927 < baseStart_1473927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473944 : List Nat := [2, 1, 2, 5, 3, 1, 9]
def baseStart_1473944 : Nat := 118140960795 + 1473944 * 2 ^ 59
def prefixEnd_1473944 : Nat := 4983230072969 + 3 ^ 40 * 1473944 * 2
def baseEnd_1473944 : Nat := 9343725059391190382981

theorem tailTrace_1473944 : CollatzResearch.WordTrace tailWord_1473944 prefixEnd_1473944 9343725059391190382981 := by
  unfold tailWord_1473944
  simp only [CollatzResearch.WordTrace]
  refine ⟨26879577086080046219546443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35839436114773394959395257 26879577086080046219546443)
  ·
    refine ⟨40319365629120069329319665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26879577086080046219546443 40319365629120069329319665)
    ·
      refine ⟨30239524221840051996989749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40319365629120069329319665 30239524221840051996989749)
      ·
        refine ⟨2834955395797504874717789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30239524221840051996989749 2834955395797504874717789)
        ·
          refine ⟨1063108273424064328019171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2834955395797504874717789 1063108273424064328019171)
          ·
            refine ⟨1594662410136096492028757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063108273424064328019171 1594662410136096492028757)
            ·
              refine ⟨9343725059391190382981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1594662410136096492028757 9343725059391190382981)
              ·
                rfl

theorem cell23_1473944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 9].length) (baseStart_1473944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473944 prefixEnd_1473944 := by exact prefixLift 1473944
  have htrace : WordTrace (prefixWord ++ tailWord_1473944) baseStart_1473944 baseEnd_1473944 := by
    simpa [prefixWord, tailWord_1473944, baseEnd_1473944] using wordTrace_append hprefix tailTrace_1473944
  have hstable : (prefixWord ++ tailWord_1473944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473944).length < 2 ^ (prefixWord ++ tailWord_1473944).sum := by decide
  have hdescent : baseEnd_1473944 < baseStart_1473944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473994 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 3, 4, 2]
def baseStart_1473994 : Nat := 118140960795 + 1473994 * 2 ^ 59
def prefixEnd_1473994 : Nat := 4983230072969 + 3 ^ 40 * 1473994 * 2
def baseEnd_1473994 : Nat := 756867403843411225396231

theorem tailTrace_1473994 : CollatzResearch.WordTrace tailWord_1473994 prefixEnd_1473994 756867403843411225396231 := by
  unfold tailWord_1473994
  simp only [CollatzResearch.WordTrace]
  refine ⟨13440244455494737744603259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35840651881319300652275357 13440244455494737744603259)
  ·
    refine ⟨20160366683242106616904889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13440244455494737744603259 20160366683242106616904889)
    ·
      refine ⟨15120275012431579962678667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20160366683242106616904889 15120275012431579962678667)
      ·
        refine ⟨22680412518647369944018001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15120275012431579962678667 22680412518647369944018001)
        ·
          refine ⟨17010309388985527458013501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22680412518647369944018001 17010309388985527458013501)
          ·
            refine ⟨6378866020869572796755063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17010309388985527458013501 6378866020869572796755063)
            ·
              refine ⟨9568299031304359195132595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6378866020869572796755063 9568299031304359195132595)
              ·
                refine ⟨14352448546956538792698893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9568299031304359195132595 14352448546956538792698893)
                ·
                  refine ⟨5382168205108702047262085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14352448546956538792698893 5382168205108702047262085)
                  ·
                    refine ⟨1009156538457881633861641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5382168205108702047262085 1009156538457881633861641)
                    ·
                      refine ⟨756867403843411225396231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1009156538457881633861641 756867403843411225396231)
                      ·
                        rfl

theorem cell23_1473994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 3, 4, 2].length) (baseStart_1473994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473994 prefixEnd_1473994 := by exact prefixLift 1473994
  have htrace : WordTrace (prefixWord ++ tailWord_1473994) baseStart_1473994 baseEnd_1473994 := by
    simpa [prefixWord, tailWord_1473994, baseEnd_1473994] using wordTrace_append hprefix tailTrace_1473994
  have hstable : (prefixWord ++ tailWord_1473994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473994).length < 2 ^ (prefixWord ++ tailWord_1473994).sum := by decide
  have hdescent : baseEnd_1473994 < baseStart_1473994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474000 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 9]
def baseStart_1474000 : Nat := 118140960795 + 1474000 * 2 ^ 59
def prefixEnd_1474000 : Nat := 4983230072969 + 3 ^ 40 * 1474000 * 2
def baseEnd_1474000 : Nat := 84096720525259800213467

theorem tailTrace_1474000 : CollatzResearch.WordTrace tailWord_1474000 prefixEnd_1474000 84096720525259800213467 := by
  unfold tailWord_1474000
  simp only [CollatzResearch.WordTrace]
  refine ⟨26880598329978607001565727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35840797773304809335420969 26880598329978607001565727)
  ·
    refine ⟨40320897494967910502348591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26880598329978607001565727 40320897494967910502348591)
    ·
      refine ⟨60481346242451865753522887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40320897494967910502348591 60481346242451865753522887)
      ·
        refine ⟨90722019363677798630284331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60481346242451865753522887 90722019363677798630284331)
        ·
          refine ⟨136083029045516697945426497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90722019363677798630284331 136083029045516697945426497)
          ·
            refine ⟨102062271784137523459069873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136083029045516697945426497 102062271784137523459069873)
            ·
              refine ⟨76546703838103142594302405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102062271784137523459069873 76546703838103142594302405)
              ·
                refine ⟨14352506969644339236431701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76546703838103142594302405 14352506969644339236431701)
                ·
                  refine ⟨84096720525259800213467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14352506969644339236431701 84096720525259800213467)
                  ·
                    rfl

theorem cell23_1474000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 9].length) (baseStart_1474000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474000 prefixEnd_1474000 := by exact prefixLift 1474000
  have htrace : WordTrace (prefixWord ++ tailWord_1474000) baseStart_1474000 baseEnd_1474000 := by
    simpa [prefixWord, tailWord_1474000, baseEnd_1474000] using wordTrace_append hprefix tailTrace_1474000
  have hstable : (prefixWord ++ tailWord_1474000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474000).length < 2 ^ (prefixWord ++ tailWord_1474000).sum := by decide
  have hdescent : baseEnd_1474000 < baseStart_1474000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474034 : List Nat := [3, 2, 1, 4, 1, 2, 1, 2, 7]
def baseStart_1474034 : Nat := 118140960795 + 1474034 * 2 ^ 59
def prefixEnd_1474034 : Nat := 4983230072969 + 3 ^ 40 * 1474034 * 2
def baseEnd_1474034 : Nat := 84098660341065674321783

theorem tailTrace_1474034 : CollatzResearch.WordTrace tailWord_1474034 prefixEnd_1474034 84098660341065674321783 := by
  unfold tailWord_1474034
  simp only [CollatzResearch.WordTrace]
  refine ⟨13440609185458509452467289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35841624494556025206579437 13440609185458509452467289)
  ·
    refine ⟨10080456889093882089350467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13440609185458509452467289 10080456889093882089350467)
    ·
      refine ⟨15120685333640823134025701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10080456889093882089350467 15120685333640823134025701)
      ·
        refine ⟨2835128500057654337629819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15120685333640823134025701 2835128500057654337629819)
        ·
          refine ⟨4252692750086481506444729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2835128500057654337629819 4252692750086481506444729)
          ·
            refine ⟨3189519562564861129833547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4252692750086481506444729 3189519562564861129833547)
            ·
              refine ⟨4784279343847291694750321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3189519562564861129833547 4784279343847291694750321)
              ·
                refine ⟨3588209507885468771062741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4784279343847291694750321 3588209507885468771062741)
                ·
                  refine ⟨84098660341065674321783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3588209507885468771062741 84098660341065674321783)
                  ·
                    rfl

theorem cell23_1474034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_1474034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474034 prefixEnd_1474034 := by exact prefixLift 1474034
  have htrace : WordTrace (prefixWord ++ tailWord_1474034) baseStart_1474034 baseEnd_1474034 := by
    simpa [prefixWord, tailWord_1474034, baseEnd_1474034] using wordTrace_append hprefix tailTrace_1474034
  have hstable : (prefixWord ++ tailWord_1474034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474034).length < 2 ^ (prefixWord ++ tailWord_1474034).sum := by decide
  have hdescent : baseEnd_1474034 < baseStart_1474034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474047 : List Nat := [1, 1, 2, 2, 1, 2, 2, 5, 2, 5]
def baseStart_1474047 : Nat := 118140960795 + 1474047 * 2 ^ 59
def prefixEnd_1474047 : Nat := 4983230072969 + 3 ^ 40 * 1474047 * 2
def baseEnd_1474047 : Nat := 252298206106033172677829

theorem tailTrace_1474047 : CollatzResearch.WordTrace tailWord_1474047 prefixEnd_1474047 252298206106033172677829 := by
  unfold tailWord_1474047
  simp only [CollatzResearch.WordTrace]
  refine ⟨53762910890786941030092395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35841940593857960686728263 53762910890786941030092395)
  ·
    refine ⟨80644366336180411545138593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53762910890786941030092395 80644366336180411545138593)
    ·
      refine ⟨60483274752135308658853945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80644366336180411545138593 60483274752135308658853945)
      ·
        refine ⟨45362456064101481494140459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60483274752135308658853945 45362456064101481494140459)
        ·
          refine ⟨68043684096152222241210689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45362456064101481494140459 68043684096152222241210689)
          ·
            refine ⟨51032763072114166680908017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68043684096152222241210689 51032763072114166680908017)
            ·
              refine ⟨38274572304085625010681013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51032763072114166680908017 38274572304085625010681013)
              ·
                refine ⟨3588241153508027344751345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38274572304085625010681013 3588241153508027344751345)
                ·
                  refine ⟨2691180865131020508563509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3588241153508027344751345 2691180865131020508563509)
                  ·
                    refine ⟨252298206106033172677829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2691180865131020508563509 252298206106033172677829)
                    ·
                      rfl

theorem cell23_1474047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 5].length) (baseStart_1474047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474047 prefixEnd_1474047 := by exact prefixLift 1474047
  have htrace : WordTrace (prefixWord ++ tailWord_1474047) baseStart_1474047 baseEnd_1474047 := by
    simpa [prefixWord, tailWord_1474047, baseEnd_1474047] using wordTrace_append hprefix tailTrace_1474047
  have hstable : (prefixWord ++ tailWord_1474047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474047).length < 2 ^ (prefixWord ++ tailWord_1474047).sum := by decide
  have hdescent : baseEnd_1474047 < baseStart_1474047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474062 : List Nat := [4, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2]
def baseStart_1474062 : Nat := 118140960795 + 1474062 * 2 ^ 59
def prefixEnd_1474062 : Nat := 4983230072969 + 3 ^ 40 * 1474062 * 2
def baseEnd_1474062 : Nat := 756902320527916959345919

theorem tailTrace_1474062 : CollatzResearch.WordTrace tailWord_1474062 prefixEnd_1474062 756902320527916959345919 := by
  unfold tailWord_1474062
  simp only [CollatzResearch.WordTrace]
  refine ⟨6720432248216574823986055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35842305323821732394592293 6720432248216574823986055)
  ·
    refine ⟨10080648372324862235979083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6720432248216574823986055 10080648372324862235979083)
    ·
      refine ⟨15120972558487293353968625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10080648372324862235979083 15120972558487293353968625)
      ·
        refine ⟨11340729418865470015476469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15120972558487293353968625 11340729418865470015476469)
        ·
          refine ⟨1063193383018637813950919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11340729418865470015476469 1063193383018637813950919)
          ·
            refine ⟨1594790074527956720926379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063193383018637813950919 1594790074527956720926379)
            ·
              refine ⟨2392185111791935081389569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1594790074527956720926379 2392185111791935081389569)
              ·
                refine ⟨1794138833843951311042177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2392185111791935081389569 1794138833843951311042177)
                ·
                  refine ⟨1345604125382963483281633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1794138833843951311042177 1345604125382963483281633)
                  ·
                    refine ⟨1009203094037222612461225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1345604125382963483281633 1009203094037222612461225)
                    ·
                      refine ⟨756902320527916959345919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1009203094037222612461225 756902320527916959345919)
                      ·
                        rfl

theorem cell23_1474062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_1474062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474062 prefixEnd_1474062 := by exact prefixLift 1474062
  have htrace : WordTrace (prefixWord ++ tailWord_1474062) baseStart_1474062 baseEnd_1474062 := by
    simpa [prefixWord, tailWord_1474062, baseEnd_1474062] using wordTrace_append hprefix tailTrace_1474062
  have hstable : (prefixWord ++ tailWord_1474062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474062).length < 2 ^ (prefixWord ++ tailWord_1474062).sum := by decide
  have hdescent : baseEnd_1474062 < baseStart_1474062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474097 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 1, 6, 4]
def baseStart_1474097 : Nat := 118140960795 + 1474097 * 2 ^ 59
def prefixEnd_1474097 : Nat := 4983230072969 + 3 ^ 40 * 1474097 * 2
def baseEnd_1474097 : Nat := 756920292350824322408257

theorem tailTrace_1474097 : CollatzResearch.WordTrace tailWord_1474097 prefixEnd_1474097 756920292350824322408257 := by
  unfold tailWord_1474097
  simp only [CollatzResearch.WordTrace]
  refine ⟨53764734540605799569412545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35843156360403866379608363 53764734540605799569412545)
  ·
    refine ⟨40323550905454349677059409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53764734540605799569412545 40323550905454349677059409)
    ·
      refine ⟨30242663179090762257794557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40323550905454349677059409 30242663179090762257794557)
      ·
        refine ⟨11340998692159035846672959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30242663179090762257794557 11340998692159035846672959)
        ·
          refine ⟨17011498038238553770009439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11340998692159035846672959 17011498038238553770009439)
          ·
            refine ⟨25517247057357830655014159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17011498038238553770009439 25517247057357830655014159)
            ·
              refine ⟨38275870586036745982521239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25517247057357830655014159 38275870586036745982521239)
              ·
                refine ⟨57413805879055118973781859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38275870586036745982521239 57413805879055118973781859)
                ·
                  refine ⟨86120708818582678460672789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57413805879055118973781859 86120708818582678460672789)
                  ·
                    refine ⟨4036908225871063052844037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86120708818582678460672789 4036908225871063052844037)
                    ·
                      refine ⟨756920292350824322408257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4036908225871063052844037 756920292350824322408257)
                      ·
                        rfl

theorem cell23_1474097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_1474097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474097 prefixEnd_1474097 := by exact prefixLift 1474097
  have htrace : WordTrace (prefixWord ++ tailWord_1474097) baseStart_1474097 baseEnd_1474097 := by
    simpa [prefixWord, tailWord_1474097, baseEnd_1474097] using wordTrace_append hprefix tailTrace_1474097
  have hstable : (prefixWord ++ tailWord_1474097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474097).length < 2 ^ (prefixWord ++ tailWord_1474097).sum := by decide
  have hdescent : baseEnd_1474097 < baseStart_1474097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474104 : List Nat := [2, 1, 2, 1, 4, 2, 2, 1, 1, 4, 3]
def baseStart_1474104 : Nat := 118140960795 + 1474104 * 2 ^ 59
def prefixEnd_1474104 : Nat := 4983230072969 + 3 ^ 40 * 1474104 * 2
def baseEnd_1474104 : Nat := 756923886715405795020725

theorem tailTrace_1474104 : CollatzResearch.WordTrace tailWord_1474104 prefixEnd_1474104 756923886715405795020725 := by
  unfold tailWord_1474104
  simp only [CollatzResearch.WordTrace]
  refine ⟨26882494925790219882458683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35843326567720293176611577 26882494925790219882458683)
  ·
    refine ⟨40323742388685329823688025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26882494925790219882458683 40323742388685329823688025)
    ·
      refine ⟨30242806791513997367766019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40323742388685329823688025 30242806791513997367766019)
      ·
        refine ⟨45364210187270996051649029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30242806791513997367766019 45364210187270996051649029)
        ·
          refine ⟨8505789410113311759684193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45364210187270996051649029 8505789410113311759684193)
          ·
            refine ⟨6379342057584983819763145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8505789410113311759684193 6379342057584983819763145)
            ·
              refine ⟨4784506543188737864822359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6379342057584983819763145 4784506543188737864822359)
              ·
                refine ⟨7176759814783106797233539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4784506543188737864822359 7176759814783106797233539)
                ·
                  refine ⟨10765139722174660195850309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7176759814783106797233539 10765139722174660195850309)
                  ·
                    refine ⟨2018463697907748786721933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10765139722174660195850309 2018463697907748786721933)
                    ·
                      refine ⟨756923886715405795020725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2018463697907748786721933 756923886715405795020725)
                      ·
                        rfl

theorem cell23_1474104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 4, 3].length) (baseStart_1474104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474104 prefixEnd_1474104 := by exact prefixLift 1474104
  have htrace : WordTrace (prefixWord ++ tailWord_1474104) baseStart_1474104 baseEnd_1474104 := by
    simpa [prefixWord, tailWord_1474104, baseEnd_1474104] using wordTrace_append hprefix tailTrace_1474104
  have hstable : (prefixWord ++ tailWord_1474104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474104).length < 2 ^ (prefixWord ++ tailWord_1474104).sum := by decide
  have hdescent : baseEnd_1474104 < baseStart_1474104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474128 : List Nat := [2, 1, 1, 1, 1, 3, 7, 2, 1, 4]
def baseStart_1474128 : Nat := 118140960795 + 1474128 * 2 ^ 59
def prefixEnd_1474128 : Nat := 4983230072969 + 3 ^ 40 * 1474128 * 2
def baseEnd_1474128 : Nat := 252312070083704567040205

theorem tailTrace_1474128 : CollatzResearch.WordTrace tailWord_1474128 prefixEnd_1474128 252312070083704567040205 := by
  unfold tailWord_1474128
  simp only [CollatzResearch.WordTrace]
  refine ⟨26882932601746745931895519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35843910135662327909194025 26882932601746745931895519)
  ·
    refine ⟨40324398902620118897843279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26882932601746745931895519 40324398902620118897843279)
    ·
      refine ⟨60486598353930178346764919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40324398902620118897843279 60486598353930178346764919)
      ·
        refine ⟨90729897530895267520147379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60486598353930178346764919 90729897530895267520147379)
        ·
          refine ⟨136094846296342901280221069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90729897530895267520147379 136094846296342901280221069)
          ·
            refine ⟨51035567361128587980082901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136094846296342901280221069 51035567361128587980082901)
            ·
              refine ⟨1196146110026451280783193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 51035567361128587980082901 1196146110026451280783193)
              ·
                refine ⟨897109582519838460587395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1196146110026451280783193 897109582519838460587395)
                ·
                  refine ⟨1345664373779757690881093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 897109582519838460587395 1345664373779757690881093)
                  ·
                    refine ⟨252312070083704567040205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1345664373779757690881093 252312070083704567040205)
                    ·
                      rfl

theorem cell23_1474128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2, 1, 4].length) (baseStart_1474128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474128 prefixEnd_1474128 := by exact prefixLift 1474128
  have htrace : WordTrace (prefixWord ++ tailWord_1474128) baseStart_1474128 baseEnd_1474128 := by
    simpa [prefixWord, tailWord_1474128, baseEnd_1474128] using wordTrace_append hprefix tailTrace_1474128
  have hstable : (prefixWord ++ tailWord_1474128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474128).length < 2 ^ (prefixWord ++ tailWord_1474128).sum := by decide
  have hdescent : baseEnd_1474128 < baseStart_1474128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474151 : List Nat := [1, 1, 5, 1, 1, 1, 2, 4, 3, 1, 3]
def baseStart_1474151 : Nat := 118140960795 + 1474151 * 2 ^ 59
def prefixEnd_1474151 : Nat := 4983230072969 + 3 ^ 40 * 1474151 * 2
def baseEnd_1474151 : Nat := 756948020306167111133009

theorem tailTrace_1474151 : CollatzResearch.WordTrace tailWord_1474151 prefixEnd_1474151 756948020306167111133009 := by
  unfold tailWord_1474151
  simp only [CollatzResearch.WordTrace]
  refine ⟨53766704082410166791878307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35844469388273444527918871 53766704082410166791878307)
  ·
    refine ⟨80650056123615250187817461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53766704082410166791878307 80650056123615250187817461)
    ·
      refine ⟨7560942761588929705107887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80650056123615250187817461 7560942761588929705107887)
      ·
        refine ⟨11341414142383394557661831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7560942761588929705107887 11341414142383394557661831)
        ·
          refine ⟨17012121213575091836492747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11341414142383394557661831 17012121213575091836492747)
          ·
            refine ⟨25518181820362637754739121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17012121213575091836492747 25518181820362637754739121)
            ·
              refine ⟨19138636365271978316054341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25518181820362637754739121 19138636365271978316054341)
              ·
                refine ⟨3588494318488495934260189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19138636365271978316054341 3588494318488495934260189)
                ·
                  refine ⟨1345685369433185975347571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3588494318488495934260189 1345685369433185975347571)
                  ·
                    refine ⟨2018528054149778963021357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1345685369433185975347571 2018528054149778963021357)
                    ·
                      refine ⟨756948020306167111133009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2018528054149778963021357 756948020306167111133009)
                      ·
                        rfl

theorem cell23_1474151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_1474151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474151 prefixEnd_1474151 := by exact prefixLift 1474151
  have htrace : WordTrace (prefixWord ++ tailWord_1474151) baseStart_1474151 baseEnd_1474151 := by
    simpa [prefixWord, tailWord_1474151, baseEnd_1474151] using wordTrace_append hprefix tailTrace_1474151
  have hstable : (prefixWord ++ tailWord_1474151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474151).length < 2 ^ (prefixWord ++ tailWord_1474151).sum := by decide
  have hdescent : baseEnd_1474151 < baseStart_1474151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474171 : List Nat := [1, 1, 1, 1, 1, 4, 7, 1, 1, 5]
def baseStart_1474171 : Nat := 118140960795 + 1474171 * 2 ^ 59
def prefixEnd_1474171 : Nat := 4983230072969 + 3 ^ 40 * 1474171 * 2
def baseEnd_1474171 : Nat := 252319429973085677627639

theorem tailTrace_1474171 : CollatzResearch.WordTrace tailWord_1474171 prefixEnd_1474171 252319429973085677627639 := by
  unfold tailWord_1474171
  simp only [CollatzResearch.WordTrace]
  refine ⟨53767433542337710207606367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35844955694891806805070911 53767433542337710207606367)
  ·
    refine ⟨80651150313506565311409551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53767433542337710207606367 80651150313506565311409551)
    ·
      refine ⟨120976725470259847967114327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80651150313506565311409551 120976725470259847967114327)
      ·
        refine ⟨181465088205389771950671491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120976725470259847967114327 181465088205389771950671491)
        ·
          refine ⟨272197632308084657926007237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181465088205389771950671491 272197632308084657926007237)
          ·
            refine ⟨51037056057765873361126357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 272197632308084657926007237 51037056057765873361126357)
            ·
              refine ⟨1196181001353887656901399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 51037056057765873361126357 1196181001353887656901399)
              ·
                refine ⟨1794271502030831485352099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1196181001353887656901399 1794271502030831485352099)
                ·
                  refine ⟨2691407253046247228028149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1794271502030831485352099 2691407253046247228028149)
                  ·
                    refine ⟨252319429973085677627639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2691407253046247228028149 252319429973085677627639)
                    ·
                      rfl

theorem cell23_1474171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 1, 5].length) (baseStart_1474171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474171 prefixEnd_1474171 := by exact prefixLift 1474171
  have htrace : WordTrace (prefixWord ++ tailWord_1474171) baseStart_1474171 baseEnd_1474171 := by
    simpa [prefixWord, tailWord_1474171, baseEnd_1474171] using wordTrace_append hprefix tailTrace_1474171
  have hstable : (prefixWord ++ tailWord_1474171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474171).length < 2 ^ (prefixWord ++ tailWord_1474171).sum := by decide
  have hdescent : baseEnd_1474171 < baseStart_1474171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474185 : List Nat := [1, 2, 1, 1, 4, 1, 6, 2, 1, 1, 3]
def baseStart_1474185 : Nat := 118140960795 + 1474185 * 2 ^ 59
def prefixEnd_1474185 : Nat := 4983230072969 + 3 ^ 40 * 1474185 * 2
def baseEnd_1474185 : Nat := 756965478648419978107853

theorem tailTrace_1474185 : CollatzResearch.WordTrace tailWord_1474185 prefixEnd_1474185 756965478648419978107853 := by
  unfold tailWord_1474185
  simp only [CollatzResearch.WordTrace]
  refine ⟨53767944164286990598616009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35845296109524660399077339 53767944164286990598616009)
  ·
    refine ⟨40325958123215242948962007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53767944164286990598616009 40325958123215242948962007)
    ·
      refine ⟨60488937184822864423443011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40325958123215242948962007 60488937184822864423443011)
      ·
        refine ⟨90733405777234296635164517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60488937184822864423443011 90733405777234296635164517)
        ·
          refine ⟨17012513583231430619093347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90733405777234296635164517 17012513583231430619093347)
          ·
            refine ⟨25518770374847145928640021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17012513583231430619093347 25518770374847145928640021)
            ·
              refine ⟨1196192361320959965405001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25518770374847145928640021 1196192361320959965405001)
              ·
                refine ⟨897144270990719974053751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1196192361320959965405001 897144270990719974053751)
                ·
                  refine ⟨1345716406486079961080627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 897144270990719974053751 1345716406486079961080627)
                  ·
                    refine ⟨2018574609729119941620941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1345716406486079961080627 2018574609729119941620941)
                    ·
                      refine ⟨756965478648419978107853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2018574609729119941620941 756965478648419978107853)
                      ·
                        rfl

theorem cell23_1474185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2, 1, 1, 3].length) (baseStart_1474185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474185 prefixEnd_1474185 := by exact prefixLift 1474185
  have htrace : WordTrace (prefixWord ++ tailWord_1474185) baseStart_1474185 baseEnd_1474185 := by
    simpa [prefixWord, tailWord_1474185, baseEnd_1474185] using wordTrace_append hprefix tailTrace_1474185
  have hstable : (prefixWord ++ tailWord_1474185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474185).length < 2 ^ (prefixWord ++ tailWord_1474185).sum := by decide
  have hdescent : baseEnd_1474185 < baseStart_1474185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474208 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 5, 2, 2]
def baseStart_1474208 : Nat := 118140960795 + 1474208 * 2 ^ 59
def prefixEnd_1474208 : Nat := 4983230072969 + 3 ^ 40 * 1474208 * 2
def baseEnd_1474208 : Nat := 756977288703473388120247

theorem tailTrace_1474208 : CollatzResearch.WordTrace tailWord_1474208 prefixEnd_1474208 756977288703473388120247 := by
  unfold tailWord_1474208
  simp only [CollatzResearch.WordTrace]
  refine ⟨26884391521601832763351639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35845855362135777017802185 26884391521601832763351639)
  ·
    refine ⟨40326587282402749145027459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26884391521601832763351639 40326587282402749145027459)
    ·
      refine ⟨60489880923604123717541189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40326587282402749145027459 60489880923604123717541189)
      ·
        refine ⟨11341852673175773197038973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60489880923604123717541189 11341852673175773197038973)
        ·
          refine ⟨4253194752440914948889615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11341852673175773197038973 4253194752440914948889615)
          ·
            refine ⟨6379792128661372423334423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4253194752440914948889615 6379792128661372423334423)
            ·
              refine ⟨9569688192992058635001635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6379792128661372423334423 9569688192992058635001635)
              ·
                refine ⟨14354532289488087952502453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9569688192992058635001635 14354532289488087952502453)
                ·
                  refine ⟨1345737402139508245547105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14354532289488087952502453 1345737402139508245547105)
                  ·
                    refine ⟨1009303051604631184160329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1345737402139508245547105 1009303051604631184160329)
                    ·
                      refine ⟨756977288703473388120247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1009303051604631184160329 756977288703473388120247)
                      ·
                        rfl

theorem cell23_1474208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_1474208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474208 prefixEnd_1474208 := by exact prefixLift 1474208
  have htrace : WordTrace (prefixWord ++ tailWord_1474208) baseStart_1474208 baseEnd_1474208 := by
    simpa [prefixWord, tailWord_1474208, baseEnd_1474208] using wordTrace_append hprefix tailTrace_1474208
  have hstable : (prefixWord ++ tailWord_1474208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474208).length < 2 ^ (prefixWord ++ tailWord_1474208).sum := by decide
  have hdescent : baseEnd_1474208 < baseStart_1474208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474211 : List Nat := [1, 1, 1, 4, 1, 1, 4, 4, 1, 2, 3]
def baseStart_1474211 : Nat := 118140960795 + 1474211 * 2 ^ 59
def prefixEnd_1474211 : Nat := 4983230072969 + 3 ^ 40 * 1474211 * 2
def baseEnd_1474211 : Nat := 756978829145436876382733

theorem tailTrace_1474211 : CollatzResearch.WordTrace tailWord_1474211 prefixEnd_1474211 756978829145436876382733 := by
  unfold tailWord_1474211
  simp only [CollatzResearch.WordTrace]
  refine ⟨53768892462192797039062487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35845928308128531359374991 53768892462192797039062487)
  ·
    refine ⟨80653338693289195558593731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53768892462192797039062487 80653338693289195558593731)
    ·
      refine ⟨120980008039933793337890597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80653338693289195558593731 120980008039933793337890597)
      ·
        refine ⟨22683751507487586250854487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120980008039933793337890597 22683751507487586250854487)
        ·
          refine ⟨34025627261231379376281731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22683751507487586250854487 34025627261231379376281731)
          ·
            refine ⟨51038440891847069064422597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34025627261231379376281731 51038440891847069064422597)
            ·
              refine ⟨9569707667221325449579237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51038440891847069064422597 9569707667221325449579237)
              ·
                refine ⟨1794320187603998521796107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9569707667221325449579237 1794320187603998521796107)
                ·
                  refine ⟨2691480281405997782694161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1794320187603998521796107 2691480281405997782694161)
                  ·
                    refine ⟨2018610211054498337020621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2691480281405997782694161 2018610211054498337020621)
                    ·
                      refine ⟨756978829145436876382733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2018610211054498337020621 756978829145436876382733)
                      ·
                        rfl

theorem cell23_1474211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_1474211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474211 prefixEnd_1474211 := by exact prefixLift 1474211
  have htrace : WordTrace (prefixWord ++ tailWord_1474211) baseStart_1474211 baseEnd_1474211 := by
    simpa [prefixWord, tailWord_1474211, baseEnd_1474211] using wordTrace_append hprefix tailTrace_1474211
  have hstable : (prefixWord ++ tailWord_1474211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474211).length < 2 ^ (prefixWord ++ tailWord_1474211).sum := by decide
  have hdescent : baseEnd_1474211 < baseStart_1474211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474221 : List Nat := [1, 5, 2, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_1474221 : Nat := 118140960795 + 1474221 * 2 ^ 59
def prefixEnd_1474221 : Nat := 4983230072969 + 3 ^ 40 * 1474221 * 2
def baseEnd_1474221 : Nat := 756983963951981837257687

theorem tailTrace_1474221 : CollatzResearch.WordTrace tailWord_1474221 prefixEnd_1474221 756983963951981837257687 := by
  unfold tailWord_1474221
  simp only [CollatzResearch.WordTrace]
  refine ⟨53769257192156568746926517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35846171461437712497951011 53769257192156568746926517)
  ·
    refine ⟨5040867861764678320024361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53769257192156568746926517 5040867861764678320024361)
    ·
      refine ⟨3780650896323508740018271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5040867861764678320024361 3780650896323508740018271)
      ·
        refine ⟨5670976344485263110027407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3780650896323508740018271 5670976344485263110027407)
        ·
          refine ⟨8506464516727894665041111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5670976344485263110027407 8506464516727894665041111)
          ·
            refine ⟨12759696775091841997561667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8506464516727894665041111 12759696775091841997561667)
            ·
              refine ⟨19139545162637762996342501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12759696775091841997561667 19139545162637762996342501)
              ·
                refine ⟨3588664717994580561814219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19139545162637762996342501 3588664717994580561814219)
                ·
                  refine ⟨5382997076991870842721329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3588664717994580561814219 5382997076991870842721329)
                  ·
                    refine ⟨4037247807743903132040997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5382997076991870842721329 4037247807743903132040997)
                    ·
                      refine ⟨756983963951981837257687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4037247807743903132040997 756983963951981837257687)
                      ·
                        rfl

theorem cell23_1474221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_1474221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474221 prefixEnd_1474221 := by exact prefixLift 1474221
  have htrace : WordTrace (prefixWord ++ tailWord_1474221) baseStart_1474221 baseEnd_1474221 := by
    simpa [prefixWord, tailWord_1474221, baseEnd_1474221] using wordTrace_append hprefix tailTrace_1474221
  have hstable : (prefixWord ++ tailWord_1474221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474221).length < 2 ^ (prefixWord ++ tailWord_1474221).sum := by decide
  have hdescent : baseEnd_1474221 < baseStart_1474221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474222 : List Nat := [4, 1, 4, 1, 2, 2, 2, 1, 1, 5]
def baseStart_1474222 : Nat := 118140960795 + 1474222 * 2 ^ 59
def prefixEnd_1474222 : Nat := 4983230072969 + 3 ^ 40 * 1474222 * 2
def baseEnd_1474222 : Nat := 252328159144212111115061

theorem tailTrace_1474222 : CollatzResearch.WordTrace tailWord_1474222 prefixEnd_1474222 252328159144212111115061 := by
  unfold tailWord_1474222
  simp only [CollatzResearch.WordTrace]
  refine ⟨6721161708144118239714115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35846195776768630611808613 6721161708144118239714115)
  ·
    refine ⟨10081742562216177359571173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6721161708144118239714115 10081742562216177359571173)
    ·
      refine ⟨1890326730415533254919595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10081742562216177359571173 1890326730415533254919595)
      ·
        refine ⟨2835490095623299882379393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1890326730415533254919595 2835490095623299882379393)
        ·
          refine ⟨2126617571717474911784545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2835490095623299882379393 2126617571717474911784545)
          ·
            refine ⟨1594963178788106183838409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2126617571717474911784545 1594963178788106183838409)
            ·
              refine ⟨1196222384091079637878807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1594963178788106183838409 1196222384091079637878807)
              ·
                refine ⟨1794333576136619456818211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1196222384091079637878807 1794333576136619456818211)
                ·
                  refine ⟨2691500364204929185227317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1794333576136619456818211 2691500364204929185227317)
                  ·
                    refine ⟨252328159144212111115061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2691500364204929185227317 252328159144212111115061)
                    ·
                      rfl

theorem cell23_1474222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_1474222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474222 prefixEnd_1474222 := by exact prefixLift 1474222
  have htrace : WordTrace (prefixWord ++ tailWord_1474222) baseStart_1474222 baseEnd_1474222 := by
    simpa [prefixWord, tailWord_1474222, baseEnd_1474222] using wordTrace_append hprefix tailTrace_1474222
  have hstable : (prefixWord ++ tailWord_1474222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474222).length < 2 ^ (prefixWord ++ tailWord_1474222).sum := by decide
  have hdescent : baseEnd_1474222 < baseStart_1474222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474251 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 5, 3, 2]
def baseStart_1474251 : Nat := 118140960795 + 1474251 * 2 ^ 59
def prefixEnd_1474251 : Nat := 4983230072969 + 3 ^ 40 * 1474251 * 2
def baseEnd_1474251 : Nat := 756999368371616719882549

theorem tailTrace_1474251 : CollatzResearch.WordTrace tailWord_1474251 prefixEnd_1474251 756999368371616719882549 := by
  unfold tailWord_1474251
  simp only [CollatzResearch.WordTrace]
  refine ⟨53770351382047883870518607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35846900921365255913679071 53770351382047883870518607)
  ·
    refine ⟨80655527073071825805777911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53770351382047883870518607 80655527073071825805777911)
    ·
      refine ⟨120983290609607738708666867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80655527073071825805777911 120983290609607738708666867)
      ·
        refine ⟨181474935914411608063000301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120983290609607738708666867 181474935914411608063000301)
        ·
          refine ⟨68053100967904353023625113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181474935914411608063000301 68053100967904353023625113)
          ·
            refine ⟨51039825725928264767718835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68053100967904353023625113 51039825725928264767718835)
            ·
              refine ⟨76559738588892397151578253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51039825725928264767718835 76559738588892397151578253)
              ·
                refine ⟨28709901970834648931841845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76559738588892397151578253 28709901970834648931841845)
                ·
                  refine ⟨2691553309765748337360173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28709901970834648931841845 2691553309765748337360173)
                  ·
                    refine ⟨1009332491162155626510065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2691553309765748337360173 1009332491162155626510065)
                    ·
                      refine ⟨756999368371616719882549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1009332491162155626510065 756999368371616719882549)
                      ·
                        rfl

theorem cell23_1474251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 3, 2].length) (baseStart_1474251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474251 prefixEnd_1474251 := by exact prefixLift 1474251
  have htrace : WordTrace (prefixWord ++ tailWord_1474251) baseStart_1474251 baseEnd_1474251 := by
    simpa [prefixWord, tailWord_1474251, baseEnd_1474251] using wordTrace_append hprefix tailTrace_1474251
  have hstable : (prefixWord ++ tailWord_1474251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474251).length < 2 ^ (prefixWord ++ tailWord_1474251).sum := by decide
  have hdescent : baseEnd_1474251 < baseStart_1474251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474258 : List Nat := [3, 2, 2, 2, 2, 1, 3, 1, 1, 3, 3]
def baseStart_1474258 : Nat := 118140960795 + 1474258 * 2 ^ 59
def prefixEnd_1474258 : Nat := 4983230072969 + 3 ^ 40 * 1474258 * 2
def baseEnd_1474258 : Nat := 757002962736198192495017

theorem tailTrace_1474258 : CollatzResearch.WordTrace tailWord_1474258 prefixEnd_1474258 757002962736198192495017 := by
  unfold tailWord_1474258
  simp only [CollatzResearch.WordTrace]
  refine ⟨13442651673255631016505857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35847071128681682710682285 13442651673255631016505857)
  ·
    refine ⟨10081988754941723262379393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13442651673255631016505857 10081988754941723262379393)
    ·
      refine ⟨7561491566206292446784545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10081988754941723262379393 7561491566206292446784545)
      ·
        refine ⟨5671118674654719335088409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7561491566206292446784545 5671118674654719335088409)
        ·
          refine ⟨4253339005991039501316307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5671118674654719335088409 4253339005991039501316307)
          ·
            refine ⟨6380008508986559251974461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4253339005991039501316307 6380008508986559251974461)
            ·
              refine ⟨2392503190869959719490423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6380008508986559251974461 2392503190869959719490423)
              ·
                refine ⟨3588754786304939579235635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2392503190869959719490423 3588754786304939579235635)
                ·
                  refine ⟨5383132179457409368853453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3588754786304939579235635 5383132179457409368853453)
                  ·
                    refine ⟨2018674567296528513320045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5383132179457409368853453 2018674567296528513320045)
                    ·
                      refine ⟨757002962736198192495017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2018674567296528513320045 757002962736198192495017)
                      ·
                        rfl

theorem cell23_1474258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_1474258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474258 prefixEnd_1474258 := by exact prefixLift 1474258
  have htrace : WordTrace (prefixWord ++ tailWord_1474258) baseStart_1474258 baseEnd_1474258 := by
    simpa [prefixWord, tailWord_1474258, baseEnd_1474258] using wordTrace_append hprefix tailTrace_1474258
  have hstable : (prefixWord ++ tailWord_1474258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474258).length < 2 ^ (prefixWord ++ tailWord_1474258).sum := by decide
  have hdescent : baseEnd_1474258 < baseStart_1474258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474281 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 3, 4, 2]
def baseStart_1474281 : Nat := 118140960795 + 1474281 * 2 ^ 59
def prefixEnd_1474281 : Nat := 4983230072969 + 3 ^ 40 * 1474281 * 2
def baseEnd_1474281 : Nat := 757014772791251602507411

theorem tailTrace_1474281 : CollatzResearch.WordTrace tailWord_1474281 prefixEnd_1474281 757014772791251602507411 := by
  unfold tailWord_1474281
  simp only [CollatzResearch.WordTrace]
  refine ⟨53771445571939198994110697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35847630381292799329407131 53771445571939198994110697)
  ·
    refine ⟨40328584178954399245583023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53771445571939198994110697 40328584178954399245583023)
    ·
      refine ⟨60492876268431598868374535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40328584178954399245583023 60492876268431598868374535)
      ·
        refine ⟨90739314402647398302561803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60492876268431598868374535 90739314402647398302561803)
        ·
          refine ⟨136108971603971097453842705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90739314402647398302561803 136108971603971097453842705)
          ·
            refine ⟨102081728702978323090382029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136108971603971097453842705 102081728702978323090382029)
            ·
              refine ⟨38280648263616871158893261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102081728702978323090382029 38280648263616871158893261)
              ·
                refine ⟨14355243098856326684584973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38280648263616871158893261 14355243098856326684584973)
                ·
                  refine ⟨5383216162071122506719365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14355243098856326684584973 5383216162071122506719365)
                  ·
                    refine ⟨1009353030388335470009881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5383216162071122506719365 1009353030388335470009881)
                    ·
                      refine ⟨757014772791251602507411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1009353030388335470009881 757014772791251602507411)
                      ·
                        rfl

theorem cell23_1474281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 4, 2].length) (baseStart_1474281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474281 prefixEnd_1474281 := by exact prefixLift 1474281
  have htrace : WordTrace (prefixWord ++ tailWord_1474281) baseStart_1474281 baseEnd_1474281 := by
    simpa [prefixWord, tailWord_1474281, baseEnd_1474281] using wordTrace_append hprefix tailTrace_1474281
  have hstable : (prefixWord ++ tailWord_1474281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474281).length < 2 ^ (prefixWord ++ tailWord_1474281).sum := by decide
  have hdescent : baseEnd_1474281 < baseStart_1474281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474284 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 5]
def baseStart_1474284 : Nat := 118140960795 + 1474284 * 2 ^ 59
def prefixEnd_1474284 : Nat := 4983230072969 + 3 ^ 40 * 1474284 * 2
def baseEnd_1474284 : Nat := 757016313233215090769897

theorem tailTrace_1474284 : CollatzResearch.WordTrace tailWord_1474284 prefixEnd_1474284 757016313233215090769897 := by
  unfold tailWord_1474284
  simp only [CollatzResearch.WordTrace]
  refine ⟨26885777495464165253234953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35847703327285553670979937 26885777495464165253234953)
  ·
    refine ⟨20164333121598123939926215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26885777495464165253234953 20164333121598123939926215)
    ·
      refine ⟨30246499682397185909889323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20164333121598123939926215 30246499682397185909889323)
      ·
        refine ⟨45369749523595778864833985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30246499682397185909889323 45369749523595778864833985)
        ·
          refine ⟨34027312142696834148625489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45369749523595778864833985 34027312142696834148625489)
          ·
            refine ⟨25520484107022625611469117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34027312142696834148625489 25520484107022625611469117)
            ·
              refine ⟨9570181540133484604300919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25520484107022625611469117 9570181540133484604300919)
              ·
                refine ⟨14355272310200226906451379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9570181540133484604300919 14355272310200226906451379)
                ·
                  refine ⟨21532908465300340359677069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14355272310200226906451379 21532908465300340359677069)
                  ·
                    refine ⟨8074840674487627634878901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21532908465300340359677069 8074840674487627634878901)
                    ·
                      refine ⟨757016313233215090769897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8074840674487627634878901 757016313233215090769897)
                      ·
                        rfl

theorem cell23_1474284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_1474284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474284 prefixEnd_1474284 := by exact prefixLift 1474284
  have htrace : WordTrace (prefixWord ++ tailWord_1474284) baseStart_1474284 baseEnd_1474284 := by
    simpa [prefixWord, tailWord_1474284, baseEnd_1474284] using wordTrace_append hprefix tailTrace_1474284
  have hstable : (prefixWord ++ tailWord_1474284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474284).length < 2 ^ (prefixWord ++ tailWord_1474284).sum := by decide
  have hdescent : baseEnd_1474284 < baseStart_1474284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474285 : List Nat := [1, 5, 1, 2, 1, 2, 2, 3, 1, 3, 2]
def baseStart_1474285 : Nat := 118140960795 + 1474285 * 2 ^ 59
def prefixEnd_1474285 : Nat := 4983230072969 + 3 ^ 40 * 1474285 * 2
def baseEnd_1474285 : Nat := 757016826713869586857393

theorem tailTrace_1474285 : CollatzResearch.WordTrace tailWord_1474285 prefixEnd_1474285 757016826713869586857393 := by
  unfold tailWord_1474285
  simp only [CollatzResearch.WordTrace]
  refine ⟨53771591463924707677256309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35847727642616471784837539 53771591463924707677256309)
  ·
    refine ⟨5041086699742941344742779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53771591463924707677256309 5041086699742941344742779)
    ·
      refine ⟨7561630049614412017114169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5041086699742941344742779 7561630049614412017114169)
      ·
        refine ⟨5671222537210809012835627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7561630049614412017114169 5671222537210809012835627)
        ·
          refine ⟨8506833805816213519253441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5671222537210809012835627 8506833805816213519253441)
          ·
            refine ⟨6380125354362160139440081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8506833805816213519253441 6380125354362160139440081)
            ·
              refine ⟨4785094015771620104580061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6380125354362160139440081 4785094015771620104580061)
              ·
                refine ⟨1794410255914357539217523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4785094015771620104580061 1794410255914357539217523)
                ·
                  refine ⟨2691615383871536308826285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1794410255914357539217523 2691615383871536308826285)
                  ·
                    refine ⟨1009355768951826115809857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2691615383871536308826285 1009355768951826115809857)
                    ·
                      refine ⟨757016826713869586857393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1009355768951826115809857 757016826713869586857393)
                      ·
                        rfl

theorem cell23_1474285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_1474285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474285 prefixEnd_1474285 := by exact prefixLift 1474285
  have htrace : WordTrace (prefixWord ++ tailWord_1474285) baseStart_1474285 baseEnd_1474285 := by
    simpa [prefixWord, tailWord_1474285, baseEnd_1474285] using wordTrace_append hprefix tailTrace_1474285
  have hstable : (prefixWord ++ tailWord_1474285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474285).length < 2 ^ (prefixWord ++ tailWord_1474285).sum := by decide
  have hdescent : baseEnd_1474285 < baseStart_1474285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474292 : List Nat := [2, 6, 1, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_1474292 : Nat := 118140960795 + 1474292 * 2 ^ 59
def prefixEnd_1474292 : Nat := 4983230072969 + 3 ^ 40 * 1474292 * 2
def baseEnd_1474292 : Nat := 757020421078451059469861

theorem tailTrace_1474292 : CollatzResearch.WordTrace tailWord_1474292 prefixEnd_1474292 757020421078451059469861 := by
  unfold tailWord_1474292
  simp only [CollatzResearch.WordTrace]
  refine ⟨26885923387449673936380565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35847897849932898581840753 26885923387449673936380565)
  ·
    refine ⟨1260277658786703465767839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26885923387449673936380565 1260277658786703465767839)
    ·
      refine ⟨1890416488180055198651759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1260277658786703465767839 1890416488180055198651759)
      ·
        refine ⟨2835624732270082797977639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1890416488180055198651759 2835624732270082797977639)
        ·
          refine ⟨4253437098405124196966459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2835624732270082797977639 4253437098405124196966459)
          ·
            refine ⟨6380155647607686295449689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4253437098405124196966459 6380155647607686295449689)
            ·
              refine ⟨4785116735705764721587267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6380155647607686295449689 4785116735705764721587267)
              ·
                refine ⟨7177675103558647082380901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4785116735705764721587267 7177675103558647082380901)
                ·
                  refine ⟨1345814081917246327946419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7177675103558647082380901 1345814081917246327946419)
                  ·
                    refine ⟨2018721122875869491919629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1345814081917246327946419 2018721122875869491919629)
                    ·
                      refine ⟨757020421078451059469861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2018721122875869491919629 757020421078451059469861)
                      ·
                        rfl

theorem cell23_1474292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_1474292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474292 prefixEnd_1474292 := by exact prefixLift 1474292
  have htrace : WordTrace (prefixWord ++ tailWord_1474292) baseStart_1474292 baseEnd_1474292 := by
    simpa [prefixWord, tailWord_1474292, baseEnd_1474292] using wordTrace_append hprefix tailTrace_1474292
  have hstable : (prefixWord ++ tailWord_1474292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474292).length < 2 ^ (prefixWord ++ tailWord_1474292).sum := by decide
  have hdescent : baseEnd_1474292 < baseStart_1474292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474338 : List Nat := [3, 3, 1, 1, 2, 1, 2, 5, 5]
def baseStart_1474338 : Nat := 118140960795 + 1474338 * 2 ^ 59
def prefixEnd_1474338 : Nat := 4983230072969 + 3 ^ 40 * 1474338 * 2
def baseEnd_1474338 : Nat := 84116004576506431054961

theorem tailTrace_1474338 : CollatzResearch.WordTrace tailWord_1474338 prefixEnd_1474338 84116004576506431054961 := by
  unfold tailWord_1474338
  simp only [CollatzResearch.WordTrace]
  refine ⟨13443381133183174432233917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35849016355155131819290445 13443381133183174432233917)
  ·
    refine ⟨5041267924943690412087719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13443381133183174432233917 5041267924943690412087719)
    ·
      refine ⟨7561901887415535618131579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5041267924943690412087719 7561901887415535618131579)
      ·
        refine ⟨11342852831123303427197369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7561901887415535618131579 11342852831123303427197369)
        ·
          refine ⟨8507139623342477570398027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11342852831123303427197369 8507139623342477570398027)
          ·
            refine ⟨12760709435013716355597041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8507139623342477570398027 12760709435013716355597041)
            ·
              refine ⟨9570532076260287266697781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12760709435013716355597041 9570532076260287266697781)
              ·
                refine ⟨897237382149401931252917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9570532076260287266697781 897237382149401931252917)
                ·
                  refine ⟨84116004576506431054961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 897237382149401931252917 84116004576506431054961)
                  ·
                    rfl

theorem cell23_1474338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_1474338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474338 prefixEnd_1474338 := by exact prefixLift 1474338
  have htrace : WordTrace (prefixWord ++ tailWord_1474338) baseStart_1474338 baseEnd_1474338 := by
    simpa [prefixWord, tailWord_1474338, baseEnd_1474338] using wordTrace_append hprefix tailTrace_1474338
  have hstable : (prefixWord ++ tailWord_1474338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474338).length < 2 ^ (prefixWord ++ tailWord_1474338).sum := by decide
  have hdescent : baseEnd_1474338 < baseStart_1474338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474388 : List Nat := [2, 4, 1, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_1474388 : Nat := 118140960795 + 1474388 * 2 ^ 59
def prefixEnd_1474388 : Nat := 4983230072969 + 3 ^ 40 * 1474388 * 2
def baseEnd_1474388 : Nat := 757069715221282683869419

theorem tailTrace_1474388 : CollatzResearch.WordTrace tailWord_1474388 prefixEnd_1474388 757069715221282683869419 := by
  unfold tailWord_1474388
  simp only [CollatzResearch.WordTrace]
  refine ⟨26887674091275778134127909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35850232121701037512170545 26887674091275778134127909)
  ·
    refine ⟨5041438892114208400148983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26887674091275778134127909 5041438892114208400148983)
    ·
      refine ⟨7562158338171312600223475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5041438892114208400148983 7562158338171312600223475)
      ·
        refine ⟨11343237507256968900335213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7562158338171312600223475 11343237507256968900335213)
        ·
          refine ⟨4253714065221363337625705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11343237507256968900335213 4253714065221363337625705)
          ·
            refine ⟨3190285548916022503219279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4253714065221363337625705 3190285548916022503219279)
            ·
              refine ⟨4785428323374033754828919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3190285548916022503219279 4785428323374033754828919)
              ·
                refine ⟨7178142485061050632243379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4785428323374033754828919 7178142485061050632243379)
                ·
                  refine ⟨10767213727591575948365069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7178142485061050632243379 10767213727591575948365069)
                  ·
                    refine ⟨4037705147846840980636901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10767213727591575948365069 4037705147846840980636901)
                    ·
                      refine ⟨757069715221282683869419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4037705147846840980636901 757069715221282683869419)
                      ·
                        rfl

theorem cell23_1474388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_1474388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474388 prefixEnd_1474388 := by exact prefixLift 1474388
  have htrace : WordTrace (prefixWord ++ tailWord_1474388) baseStart_1474388 baseEnd_1474388 := by
    simpa [prefixWord, tailWord_1474388, baseEnd_1474388] using wordTrace_append hprefix tailTrace_1474388
  have hstable : (prefixWord ++ tailWord_1474388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474388).length < 2 ^ (prefixWord ++ tailWord_1474388).sum := by decide
  have hdescent : baseEnd_1474388 < baseStart_1474388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474408 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 4, 2, 3]
def baseStart_1474408 : Nat := 118140960795 + 1474408 * 2 ^ 59
def prefixEnd_1474408 : Nat := 4983230072969 + 3 ^ 40 * 1474408 * 2
def baseEnd_1474408 : Nat := 757079984834372605619327

theorem tailTrace_1474408 : CollatzResearch.WordTrace tailWord_1474408 prefixEnd_1474408 757079984834372605619327 := by
  unfold tailWord_1474408
  simp only [CollatzResearch.WordTrace]
  refine ⟨26888038821239549841991939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35850718428319399789322585 26888038821239549841991939)
  ·
    refine ⟨40332058231859324762987909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26888038821239549841991939 40332058231859324762987909)
    ·
      refine ⟨7562260918473623393060233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40332058231859324762987909 7562260918473623393060233)
      ·
        refine ⟨5671695688855217544795175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7562260918473623393060233 5671695688855217544795175)
        ·
          refine ⟨8507543533282826317192763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5671695688855217544795175 8507543533282826317192763)
          ·
            refine ⟨12761315299924239475789145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8507543533282826317192763 12761315299924239475789145)
            ·
              refine ⟨9570986474943179606841859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12761315299924239475789145 9570986474943179606841859)
              ·
                refine ⟨14356479712414769410262789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9570986474943179606841859 14356479712414769410262789)
                ·
                  refine ⟨2691839946077769264424273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14356479712414769410262789 2691839946077769264424273)
                  ·
                    refine ⟨2018879959558326948318205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2691839946077769264424273 2018879959558326948318205)
                    ·
                      refine ⟨757079984834372605619327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2018879959558326948318205 757079984834372605619327)
                      ·
                        rfl

theorem cell23_1474408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_1474408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474408 prefixEnd_1474408 := by exact prefixLift 1474408
  have htrace : WordTrace (prefixWord ++ tailWord_1474408) baseStart_1474408 baseEnd_1474408 := by
    simpa [prefixWord, tailWord_1474408, baseEnd_1474408] using wordTrace_append hprefix tailTrace_1474408
  have hstable : (prefixWord ++ tailWord_1474408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474408).length < 2 ^ (prefixWord ++ tailWord_1474408).sum := by decide
  have hdescent : baseEnd_1474408 < baseStart_1474408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474495 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 5, 2, 2]
def baseStart_1474495 : Nat := 118140960795 + 1474495 * 2 ^ 59
def prefixEnd_1474495 : Nat := 4983230072969 + 3 ^ 40 * 1474495 * 2
def baseEnd_1474495 : Nat := 757124657651313765231427

theorem tailTrace_1474495 : CollatzResearch.WordTrace tailWord_1474495 prefixEnd_1474495 757124657651313765231427 := by
  unfold tailWord_1474495
  simp only [CollatzResearch.WordTrace]
  refine ⟨53779250793163913542400939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35852833862109275694933959 53779250793163913542400939)
  ·
    refine ⟨80668876189745870313601409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53779250793163913542400939 80668876189745870313601409)
    ·
      refine ⟨60501657142309402735201057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80668876189745870313601409 60501657142309402735201057)
      ·
        refine ⟨45376242856732052051400793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60501657142309402735201057 45376242856732052051400793)
        ·
          refine ⟨34032182142549039038550595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45376242856732052051400793 34032182142549039038550595)
          ·
            refine ⟨51048273213823558557825893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34032182142549039038550595 51048273213823558557825893)
            ·
              refine ⟨9571551227591917229592355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51048273213823558557825893 9571551227591917229592355)
              ·
                refine ⟨14357326841387875844388533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9571551227591917229592355 14357326841387875844388533)
                ·
                  refine ⟨1345999391380113360411425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14357326841387875844388533 1345999391380113360411425)
                  ·
                    refine ⟨1009499543535085020308569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1345999391380113360411425 1009499543535085020308569)
                    ·
                      refine ⟨757124657651313765231427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1009499543535085020308569 757124657651313765231427)
                      ·
                        rfl

theorem cell23_1474495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5, 2, 2].length) (baseStart_1474495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474495 prefixEnd_1474495 := by exact prefixLift 1474495
  have htrace : WordTrace (prefixWord ++ tailWord_1474495) baseStart_1474495 baseEnd_1474495 := by
    simpa [prefixWord, tailWord_1474495, baseEnd_1474495] using wordTrace_append hprefix tailTrace_1474495
  have hstable : (prefixWord ++ tailWord_1474495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474495).length < 2 ^ (prefixWord ++ tailWord_1474495).sum := by decide
  have hdescent : baseEnd_1474495 < baseStart_1474495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474508 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 3, 2, 4]
def baseStart_1474508 : Nat := 118140960795 + 1474508 * 2 ^ 59
def prefixEnd_1474508 : Nat := 4983230072969 + 3 ^ 40 * 1474508 * 2
def baseEnd_1474508 : Nat := 757131332899822214368867

theorem tailTrace_1474508 : CollatzResearch.WordTrace tailWord_1474508 prefixEnd_1474508 757131332899822214368867 := by
  unfold tailWord_1474508
  simp only [CollatzResearch.WordTrace]
  refine ⟨26889862471058408381312089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35853149961411211175082785 26889862471058408381312089)
  ·
    refine ⟨20167396853293806285984067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26889862471058408381312089 20167396853293806285984067)
    ·
      refine ⟨30251095279940709428976101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20167396853293806285984067 30251095279940709428976101)
      ·
        refine ⟨5672080364988883017933019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30251095279940709428976101 5672080364988883017933019)
        ·
          refine ⟨8508120547483324526899529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5672080364988883017933019 8508120547483324526899529)
          ·
            refine ⟨6381090410612493395174647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8508120547483324526899529 6381090410612493395174647)
            ·
              refine ⟨9571635615918740092761971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6381090410612493395174647 9571635615918740092761971)
              ·
                refine ⟨14357453423878110139142957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9571635615918740092761971 14357453423878110139142957)
                ·
                  refine ⟨5384045033954291302178609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14357453423878110139142957 5384045033954291302178609)
                  ·
                    refine ⟨4038033775465718476633957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5384045033954291302178609 4038033775465718476633957)
                    ·
                      refine ⟨757131332899822214368867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4038033775465718476633957 757131332899822214368867)
                      ·
                        rfl

theorem cell23_1474508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_1474508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474508 prefixEnd_1474508 := by exact prefixLift 1474508
  have htrace : WordTrace (prefixWord ++ tailWord_1474508) baseStart_1474508 baseEnd_1474508 := by
    simpa [prefixWord, tailWord_1474508, baseEnd_1474508] using wordTrace_append hprefix tailTrace_1474508
  have hstable : (prefixWord ++ tailWord_1474508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474508).length < 2 ^ (prefixWord ++ tailWord_1474508).sum := by decide
  have hdescent : baseEnd_1474508 < baseStart_1474508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474518 : List Nat := [5, 2, 1, 1, 14]
def baseStart_1474518 : Nat := 118140960795 + 1474518 * 2 ^ 59
def prefixEnd_1474518 : Nat := 4983230072969 + 3 ^ 40 * 1474518 * 2
def baseEnd_1474518 : Nat := 1038595977649337688949

theorem tailTrace_1474518 : CollatzResearch.WordTrace tailWord_1474518 prefixEnd_1474518 1038595977649337688949 := by
  unfold tailWord_1474518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3361255604505036779405513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35853393114720392313658805 3361255604505036779405513)
  ·
    refine ⟨2520941703378777584554135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3361255604505036779405513 2520941703378777584554135)
    ·
      refine ⟨3781412555068166376831203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2520941703378777584554135 3781412555068166376831203)
      ·
        refine ⟨5672118832602249565246805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3781412555068166376831203 5672118832602249565246805)
        ·
          refine ⟨1038595977649337688949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 5672118832602249565246805 1038595977649337688949)
          ·
            rfl

theorem cell23_1474518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 14].length) (baseStart_1474518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474518 prefixEnd_1474518 := by exact prefixLift 1474518
  have htrace : WordTrace (prefixWord ++ tailWord_1474518) baseStart_1474518 baseEnd_1474518 := by
    simpa [prefixWord, tailWord_1474518, baseEnd_1474518] using wordTrace_append hprefix tailTrace_1474518
  have hstable : (prefixWord ++ tailWord_1474518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474518).length < 2 ^ (prefixWord ++ tailWord_1474518).sum := by decide
  have hdescent : baseEnd_1474518 < baseStart_1474518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474522 : List Nat := [3, 1, 1, 2, 5, 1, 2, 2, 2, 4]
def baseStart_1474522 : Nat := 118140960795 + 1474522 * 2 ^ 59
def prefixEnd_1474522 : Nat := 4983230072969 + 3 ^ 40 * 1474522 * 2
def baseEnd_1474522 : Nat := 252379507209661719864601

theorem tailTrace_1474522 : CollatzResearch.WordTrace tailWord_1474522 prefixEnd_1474522 252379507209661719864601 := by
  unfold tailWord_1474522
  simp only [CollatzResearch.WordTrace]
  refine ⟨13445058891016524288408455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35853490376044064769089213 13445058891016524288408455)
  ·
    refine ⟨20167588336524786432612683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13445058891016524288408455 20167588336524786432612683)
    ·
      refine ⟨30251382504787179648919025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20167588336524786432612683 30251382504787179648919025)
      ·
        refine ⟨22688536878590384736689269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30251382504787179648919025 22688536878590384736689269)
        ·
          refine ⟨2127050332367848569064619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22688536878590384736689269 2127050332367848569064619)
          ·
            refine ⟨3190575498551772853596929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2127050332367848569064619 3190575498551772853596929)
            ·
              refine ⟨2392931623913829640197697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3190575498551772853596929 2392931623913829640197697)
              ·
                refine ⟨1794698717935372230148273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2392931623913829640197697 1794698717935372230148273)
                ·
                  refine ⟨1346024038451529172611205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1794698717935372230148273 1346024038451529172611205)
                  ·
                    refine ⟨252379507209661719864601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1346024038451529172611205 252379507209661719864601)
                    ·
                      rfl

theorem cell23_1474522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 2, 4].length) (baseStart_1474522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474522 prefixEnd_1474522 := by exact prefixLift 1474522
  have htrace : WordTrace (prefixWord ++ tailWord_1474522) baseStart_1474522 baseEnd_1474522 := by
    simpa [prefixWord, tailWord_1474522, baseEnd_1474522] using wordTrace_append hprefix tailTrace_1474522
  have hstable : (prefixWord ++ tailWord_1474522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474522).length < 2 ^ (prefixWord ++ tailWord_1474522).sum := by decide
  have hdescent : baseEnd_1474522 < baseStart_1474522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474535 : List Nat := [1, 1, 5, 2, 3, 2, 1, 8]
def baseStart_1474535 : Nat := 118140960795 + 1474535 * 2 ^ 59
def prefixEnd_1474535 : Nat := 4983230072969 + 3 ^ 40 * 1474535 * 2
def baseEnd_1474535 : Nat := 28042414699166429953009

theorem tailTrace_1474535 : CollatzResearch.WordTrace tailWord_1474535 prefixEnd_1474535 28042414699166429953009 := by
  unfold tailWord_1474535
  simp only [CollatzResearch.WordTrace]
  refine ⟨53780709713019000373857059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35853806475346000249238039 53780709713019000373857059)
  ·
    refine ⟨80671064569528500560785589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53780709713019000373857059 80671064569528500560785589)
    ·
      refine ⟨7562912303393296927573649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80671064569528500560785589 7562912303393296927573649)
      ·
        refine ⟨5672184227544972695680237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7562912303393296927573649 5672184227544972695680237)
        ·
          refine ⟨2127069085329364760880089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5672184227544972695680237 2127069085329364760880089)
          ·
            refine ⟨1595301813997023570660067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2127069085329364760880089 1595301813997023570660067)
            ·
              refine ⟨2392952720995535355990101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1595301813997023570660067 2392952720995535355990101)
              ·
                refine ⟨28042414699166429953009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2392952720995535355990101 28042414699166429953009)
                ·
                  rfl

theorem cell23_1474535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 8].length) (baseStart_1474535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474535 prefixEnd_1474535 := by exact prefixLift 1474535
  have htrace : WordTrace (prefixWord ++ tailWord_1474535) baseStart_1474535 baseEnd_1474535 := by
    simpa [prefixWord, tailWord_1474535, baseEnd_1474535] using wordTrace_append hprefix tailTrace_1474535
  have hstable : (prefixWord ++ tailWord_1474535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474535).length < 2 ^ (prefixWord ++ tailWord_1474535).sum := by decide
  have hdescent : baseEnd_1474535 < baseStart_1474535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474555 : List Nat := [1, 1, 1, 1, 1, 3, 6, 1, 3, 3, 2]
def baseStart_1474555 : Nat := 118140960795 + 1474555 * 2 ^ 59
def prefixEnd_1474555 : Nat := 4983230072969 + 3 ^ 40 * 1474555 * 2
def baseEnd_1474555 : Nat := 757155466490583530481151

theorem tailTrace_1474555 : CollatzResearch.WordTrace tailWord_1474555 prefixEnd_1474555 757155466490583530481151 := by
  unfold tailWord_1474555
  simp only [CollatzResearch.WordTrace]
  refine ⟨53781439172946543789585119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35854292781964362526390079 53781439172946543789585119)
  ·
    refine ⟨80672158759419815684377679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53781439172946543789585119 80672158759419815684377679)
    ·
      refine ⟨121008238139129723526566519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80672158759419815684377679 121008238139129723526566519)
      ·
        refine ⟨181512357208694585289849779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121008238139129723526566519 181512357208694585289849779)
        ·
          refine ⟨272268535813041877934774669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181512357208694585289849779 272268535813041877934774669)
          ·
            refine ⟨102100700929890704225540501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 272268535813041877934774669 102100700929890704225540501)
            ·
              refine ⟨4785970356088626760572211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102100700929890704225540501 4785970356088626760572211)
              ·
                refine ⟨7178955534132940140858317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4785970356088626760572211 7178955534132940140858317)
                ·
                  refine ⟨2692108325299852552821869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7178955534132940140858317 2692108325299852552821869)
                  ·
                    refine ⟨1009540621987444707308201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2692108325299852552821869 1009540621987444707308201)
                    ·
                      refine ⟨757155466490583530481151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1009540621987444707308201 757155466490583530481151)
                      ·
                        rfl

theorem cell23_1474555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 3, 2].length) (baseStart_1474555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474555 prefixEnd_1474555 := by exact prefixLift 1474555
  have htrace : WordTrace (prefixWord ++ tailWord_1474555) baseStart_1474555 baseEnd_1474555 := by
    simpa [prefixWord, tailWord_1474555, baseEnd_1474555] using wordTrace_append hprefix tailTrace_1474555
  have hstable : (prefixWord ++ tailWord_1474555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474555).length < 2 ^ (prefixWord ++ tailWord_1474555).sum := by decide
  have hdescent : baseEnd_1474555 < baseStart_1474555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474572 : List Nat := [2, 2, 1, 2, 3, 1, 3, 3, 1, 3, 2]
def baseStart_1474572 : Nat := 118140960795 + 1474572 * 2 ^ 59
def prefixEnd_1474572 : Nat := 4983230072969 + 3 ^ 40 * 1474572 * 2
def baseEnd_1474572 : Nat := 757164195661709963968573

theorem tailTrace_1474572 : CollatzResearch.WordTrace tailWord_1474572 prefixEnd_1474572 757164195661709963968573 := by
  unfold tailWord_1474572
  simp only [CollatzResearch.WordTrace]
  refine ⟨26891029606942477846476985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35854706142589970461969313 26891029606942477846476985)
  ·
    refine ⟨20168272205206858384857739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26891029606942477846476985 20168272205206858384857739)
    ·
      refine ⟨30252408307810287577286609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20168272205206858384857739 30252408307810287577286609)
      ·
        refine ⟨22689306230857715682964957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30252408307810287577286609 22689306230857715682964957)
        ·
          refine ⟨8508489836571643381111859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22689306230857715682964957 8508489836571643381111859)
          ·
            refine ⟨12762734754857465071667789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8508489836571643381111859 12762734754857465071667789)
            ·
              refine ⟨4786025533071549401875421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12762734754857465071667789 4786025533071549401875421)
              ·
                refine ⟨1794759574901831025703283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4786025533071549401875421 1794759574901831025703283)
                ·
                  refine ⟨2692139362352746538554925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1794759574901831025703283 2692139362352746538554925)
                  ·
                    refine ⟨1009552260882279951958097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2692139362352746538554925 1009552260882279951958097)
                    ·
                      refine ⟨757164195661709963968573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1009552260882279951958097 757164195661709963968573)
                      ·
                        rfl

theorem cell23_1474572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 1, 3, 2].length) (baseStart_1474572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474572 prefixEnd_1474572 := by exact prefixLift 1474572
  have htrace : WordTrace (prefixWord ++ tailWord_1474572) baseStart_1474572 baseEnd_1474572 := by
    simpa [prefixWord, tailWord_1474572, baseEnd_1474572] using wordTrace_append hprefix tailTrace_1474572
  have hstable : (prefixWord ++ tailWord_1474572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474572).length < 2 ^ (prefixWord ++ tailWord_1474572).sum := by decide
  have hdescent : baseEnd_1474572 < baseStart_1474572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474573 : List Nat := [1, 7, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_1474573 : Nat := 118140960795 + 1474573 * 2 ^ 59
def prefixEnd_1474573 : Nat := 4983230072969 + 3 ^ 40 * 1474573 * 2
def baseEnd_1474573 : Nat := 252388236380788153352023

theorem tailTrace_1474573 : CollatzResearch.WordTrace tailWord_1474573 prefixEnd_1474573 252388236380788153352023 := by
  unfold tailWord_1474573
  simp only [CollatzResearch.WordTrace]
  refine ⟨53782095686881332863740373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35854730457920888575826915 53782095686881332863740373)
  ·
    refine ⟨1260517867661281238993915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 53782095686881332863740373 1260517867661281238993915)
    ·
      refine ⟨1890776801491921858490873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1260517867661281238993915 1890776801491921858490873)
      ·
        refine ⟨1418082601118941393868155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1890776801491921858490873 1418082601118941393868155)
        ·
          refine ⟨2127123901678412090802233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1418082601118941393868155 2127123901678412090802233)
          ·
            refine ⟨1595342926258809068101675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2127123901678412090802233 1595342926258809068101675)
            ·
              refine ⟨2393014389388213602152513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1595342926258809068101675 2393014389388213602152513)
              ·
                refine ⟨1794760792041160201614385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2393014389388213602152513 1794760792041160201614385)
                ·
                  refine ⟨1346070594030870151210789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1794760792041160201614385 1346070594030870151210789)
                  ·
                    refine ⟨252388236380788153352023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1346070594030870151210789 252388236380788153352023)
                    ·
                      rfl

theorem cell23_1474573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_1474573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474573 prefixEnd_1474573 := by exact prefixLift 1474573
  have htrace : WordTrace (prefixWord ++ tailWord_1474573) baseStart_1474573 baseEnd_1474573 := by
    simpa [prefixWord, tailWord_1474573, baseEnd_1474573] using wordTrace_append hprefix tailTrace_1474573
  have hstable : (prefixWord ++ tailWord_1474573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474573).length < 2 ^ (prefixWord ++ tailWord_1474573).sum := by decide
  have hdescent : baseEnd_1474573 < baseStart_1474573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474596 : List Nat := [2, 3, 1, 4, 2, 1, 3, 1, 2, 1, 3]
def baseStart_1474596 : Nat := 118140960795 + 1474596 * 2 ^ 59
def prefixEnd_1474596 : Nat := 4983230072969 + 3 ^ 40 * 1474596 * 2
def baseEnd_1474596 : Nat := 757176519197417870068463

theorem tailTrace_1474596 : CollatzResearch.WordTrace tailWord_1474596 prefixEnd_1474596 757176519197417870068463 := by
  unfold tailWord_1474596
  simp only [CollatzResearch.WordTrace]
  refine ⟨26891467282899003895913821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35855289710532005194551761 26891467282899003895913821)
  ·
    refine ⟨10084300231087126460967683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26891467282899003895913821 10084300231087126460967683)
    ·
      refine ⟨15126450346630689691451525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10084300231087126460967683 15126450346630689691451525)
      ·
        refine ⟨2836209439993254317147161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15126450346630689691451525 2836209439993254317147161)
        ·
          refine ⟨2127157079994940737860371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2836209439993254317147161 2127157079994940737860371)
          ·
            refine ⟨3190735619992411106790557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2127157079994940737860371 3190735619992411106790557)
            ·
              refine ⟨1196525857497154165046459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3190735619992411106790557 1196525857497154165046459)
              ·
                refine ⟨1794788786245731247569689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1196525857497154165046459 1794788786245731247569689)
                ·
                  refine ⟨1346091589684298435677267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1794788786245731247569689 1346091589684298435677267)
                  ·
                    refine ⟨2019137384526447653515901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1346091589684298435677267 2019137384526447653515901)
                    ·
                      refine ⟨757176519197417870068463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2019137384526447653515901 757176519197417870068463)
                      ·
                        rfl

theorem cell23_1474596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_1474596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474596 prefixEnd_1474596 := by exact prefixLift 1474596
  have htrace : WordTrace (prefixWord ++ tailWord_1474596) baseStart_1474596 baseEnd_1474596 := by
    simpa [prefixWord, tailWord_1474596, baseEnd_1474596] using wordTrace_append hprefix tailTrace_1474596
  have hstable : (prefixWord ++ tailWord_1474596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474596).length < 2 ^ (prefixWord ++ tailWord_1474596).sum := by decide
  have hdescent : baseEnd_1474596 < baseStart_1474596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474608 : List Nat := [2, 1, 1, 1, 2, 5, 2, 2, 7]
def baseStart_1474608 : Nat := 118140960795 + 1474608 * 2 ^ 59
def prefixEnd_1474608 : Nat := 4983230072969 + 3 ^ 40 * 1474608 * 2
def baseEnd_1474608 : Nat := 84131408996141313679823

theorem tailTrace_1474608 : CollatzResearch.WordTrace tailWord_1474608 prefixEnd_1474608 84131408996141313679823 := by
  unfold tailWord_1474608
  simp only [CollatzResearch.WordTrace]
  refine ⟨26891686120877266920632239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35855581494503022560842985 26891686120877266920632239)
  ·
    refine ⟨40337529181315900380948359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26891686120877266920632239 40337529181315900380948359)
    ·
      refine ⟨60506293771973850571422539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40337529181315900380948359 60506293771973850571422539)
      ·
        refine ⟨90759440657960775857133809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60506293771973850571422539 90759440657960775857133809)
        ·
          refine ⟨68069580493470581892850357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90759440657960775857133809 68069580493470581892850357)
          ·
            refine ⟨6381523171262867052454721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68069580493470581892850357 6381523171262867052454721)
            ·
              refine ⟨4786142378447150289341041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6381523171262867052454721 4786142378447150289341041)
              ·
                refine ⟨3589606783835362717005781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4786142378447150289341041 3589606783835362717005781)
                ·
                  refine ⟨84131408996141313679823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3589606783835362717005781 84131408996141313679823)
                  ·
                    rfl

theorem cell23_1474608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 7].length) (baseStart_1474608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474608 prefixEnd_1474608 := by exact prefixLift 1474608
  have htrace : WordTrace (prefixWord ++ tailWord_1474608) baseStart_1474608 baseEnd_1474608 := by
    simpa [prefixWord, tailWord_1474608, baseEnd_1474608] using wordTrace_append hprefix tailTrace_1474608
  have hstable : (prefixWord ++ tailWord_1474608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474608).length < 2 ^ (prefixWord ++ tailWord_1474608).sum := by decide
  have hdescent : baseEnd_1474608 < baseStart_1474608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474622 : List Nat := [4, 2, 1, 3, 2, 1, 1, 1, 2, 1, 5]
def baseStart_1474622 : Nat := 118140960795 + 1474622 * 2 ^ 59
def prefixEnd_1474622 : Nat := 4983230072969 + 3 ^ 40 * 1474622 * 2
def baseEnd_1474622 : Nat := 757189869694434768343343

theorem tailTrace_1474622 : CollatzResearch.WordTrace tailWord_1474622 prefixEnd_1474622 757189869694434768343343 := by
  unfold tailWord_1474622
  simp only [CollatzResearch.WordTrace]
  refine ⟨6722985357962976779034265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35855921909135876154849413 6722985357962976779034265)
  ·
    refine ⟨5042239018472232584275699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6722985357962976779034265 5042239018472232584275699)
    ·
      refine ⟨7563358527708348876413549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5042239018472232584275699 7563358527708348876413549)
      ·
        refine ⟨2836259447890630828655081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7563358527708348876413549 2836259447890630828655081)
        ·
          refine ⟨2127194585917973121491311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2836259447890630828655081 2127194585917973121491311)
          ·
            refine ⟨3190791878876959682236967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2127194585917973121491311 3190791878876959682236967)
            ·
              refine ⟨4786187818315439523355451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3190791878876959682236967 4786187818315439523355451)
              ·
                refine ⟨7179281727473159285033177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4786187818315439523355451 7179281727473159285033177)
                ·
                  refine ⟨5384461295604869463774883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7179281727473159285033177 5384461295604869463774883)
                  ·
                    refine ⟨8076691943407304195662325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5384461295604869463774883 8076691943407304195662325)
                    ·
                      refine ⟨757189869694434768343343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8076691943407304195662325 757189869694434768343343)
                      ·
                        rfl

theorem cell23_1474622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_1474622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474622 prefixEnd_1474622 := by exact prefixLift 1474622
  have htrace : WordTrace (prefixWord ++ tailWord_1474622) baseStart_1474622 baseEnd_1474622 := by
    simpa [prefixWord, tailWord_1474622, baseEnd_1474622] using wordTrace_append hprefix tailTrace_1474622
  have hstable : (prefixWord ++ tailWord_1474622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474622).length < 2 ^ (prefixWord ++ tailWord_1474622).sum := by decide
  have hdescent : baseEnd_1474622 < baseStart_1474622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474642 : List Nat := [3, 2, 2, 1, 4, 2, 1, 1, 7]
def baseStart_1474642 : Nat := 118140960795 + 1474642 * 2 ^ 59
def prefixEnd_1474642 : Nat := 4983230072969 + 3 ^ 40 * 1474642 * 2
def baseEnd_1474642 : Nat := 84133348811947187788139

theorem tailTrace_1474642 : CollatzResearch.WordTrace tailWord_1474642 prefixEnd_1474642 84133348811947187788139 := by
  unfold tailWord_1474642
  simp only [CollatzResearch.WordTrace]
  refine ⟨13446153080907839412000545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35856408215754238432001453 13446153080907839412000545)
  ·
    refine ⟨10084614810680879559000409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13446153080907839412000545 10084614810680879559000409)
    ·
      refine ⟨7563461108010659669250307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10084614810680879559000409 7563461108010659669250307)
      ·
        refine ⟨11345191662015989503875461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7563461108010659669250307 11345191662015989503875461)
        ·
          refine ⟨2127223436627998031976649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11345191662015989503875461 2127223436627998031976649)
          ·
            refine ⟨1595417577470998523982487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2127223436627998031976649 1595417577470998523982487)
            ·
              refine ⟨2393126366206497785973731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1595417577470998523982487 2393126366206497785973731)
              ·
                refine ⟨3589689549309746678960597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2393126366206497785973731 3589689549309746678960597)
                ·
                  refine ⟨84133348811947187788139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3589689549309746678960597 84133348811947187788139)
                  ·
                    rfl

theorem cell23_1474642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 7].length) (baseStart_1474642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474642 prefixEnd_1474642 := by exact prefixLift 1474642
  have htrace : WordTrace (prefixWord ++ tailWord_1474642) baseStart_1474642 baseEnd_1474642 := by
    simpa [prefixWord, tailWord_1474642, baseEnd_1474642] using wordTrace_append hprefix tailTrace_1474642
  have hstable : (prefixWord ++ tailWord_1474642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474642).length < 2 ^ (prefixWord ++ tailWord_1474642).sum := by decide
  have hdescent : baseEnd_1474642 < baseStart_1474642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474648 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 1, 1, 7]
def baseStart_1474648 : Nat := 118140960795 + 1474648 * 2 ^ 59
def prefixEnd_1474648 : Nat := 4983230072969 + 3 ^ 40 * 1474648 * 2
def baseEnd_1474648 : Nat := 757203220191451666618223

theorem tailTrace_1474648 : CollatzResearch.WordTrace tailWord_1474648 prefixEnd_1474648 757203220191451666618223 := by
  unfold tailWord_1474648
  simp only [CollatzResearch.WordTrace]
  refine ⟨26892415580804810336360299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35856554107739747115147065 26892415580804810336360299)
  ·
    refine ⟨40338623371207215504540449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26892415580804810336360299 40338623371207215504540449)
    ·
      refine ⟨30253967528405411628405337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40338623371207215504540449 30253967528405411628405337)
      ·
        refine ⟨22690475646304058721304003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30253967528405411628405337 22690475646304058721304003)
        ·
          refine ⟨34035713469456088081956005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22690475646304058721304003 34035713469456088081956005)
          ·
            refine ⟨6381696275523016515366751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34035713469456088081956005 6381696275523016515366751)
            ·
              refine ⟨9572544413284524773050127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6381696275523016515366751 9572544413284524773050127)
              ·
                refine ⟨14358816619926787159575191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9572544413284524773050127 14358816619926787159575191)
                ·
                  refine ⟨21538224929890180739362787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14358816619926787159575191 21538224929890180739362787)
                  ·
                    refine ⟨32307337394835271109044181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21538224929890180739362787 32307337394835271109044181)
                    ·
                      refine ⟨757203220191451666618223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 32307337394835271109044181 757203220191451666618223)
                      ·
                        rfl

theorem cell23_1474648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_1474648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474648 prefixEnd_1474648 := by exact prefixLift 1474648
  have htrace : WordTrace (prefixWord ++ tailWord_1474648) baseStart_1474648 baseEnd_1474648 := by
    simpa [prefixWord, tailWord_1474648, baseEnd_1474648] using wordTrace_append hprefix tailTrace_1474648
  have hstable : (prefixWord ++ tailWord_1474648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474648).length < 2 ^ (prefixWord ++ tailWord_1474648).sum := by decide
  have hdescent : baseEnd_1474648 < baseStart_1474648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474653 : List Nat := [1, 4, 4, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_1474653 : Nat := 118140960795 + 1474653 * 2 ^ 59
def prefixEnd_1474653 : Nat := 4983230072969 + 3 ^ 40 * 1474653 * 2
def baseEnd_1474653 : Nat := 757205787594724147055701

theorem tailTrace_1474653 : CollatzResearch.WordTrace tailWord_1474653 prefixEnd_1474653 757205787594724147055701 := by
  unfold tailWord_1474653
  simp only [CollatzResearch.WordTrace]
  refine ⟨53785013526591506526652613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35856675684394337684435075 53785013526591506526652613)
  ·
    refine ⟨10084690036235907473747365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53785013526591506526652613 10084690036235907473747365)
    ·
      refine ⟨1890879381794232651327631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10084690036235907473747365 1890879381794232651327631)
      ·
        refine ⟨2836319072691348976991447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1890879381794232651327631 2836319072691348976991447)
        ·
          refine ⟨4254478609037023465487171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2836319072691348976991447 4254478609037023465487171)
          ·
            refine ⟨6381717913555535198230757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4254478609037023465487171 6381717913555535198230757)
            ·
              refine ⟨1196572108791662849668267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6381717913555535198230757 1196572108791662849668267)
              ·
                refine ⟨1794858163187494274502401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1196572108791662849668267 1794858163187494274502401)
                ·
                  refine ⟨1346143622390620705876801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1794858163187494274502401 1346143622390620705876801)
                  ·
                    refine ⟨1009607716792965529407601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1346143622390620705876801 1009607716792965529407601)
                    ·
                      refine ⟨757205787594724147055701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1009607716792965529407601 757205787594724147055701)
                      ·
                        rfl

theorem cell23_1474653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_1474653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474653 prefixEnd_1474653 := by exact prefixLift 1474653
  have htrace : WordTrace (prefixWord ++ tailWord_1474653) baseStart_1474653 baseEnd_1474653 := by
    simpa [prefixWord, tailWord_1474653, baseEnd_1474653] using wordTrace_append hprefix tailTrace_1474653
  have hstable : (prefixWord ++ tailWord_1474653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474653).length < 2 ^ (prefixWord ++ tailWord_1474653).sum := by decide
  have hdescent : baseEnd_1474653 < baseStart_1474653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474688 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 6]
def baseStart_1474688 : Nat := 118140960795 + 1474688 * 2 ^ 59
def prefixEnd_1474688 : Nat := 4983230072969 + 3 ^ 40 * 1474688 * 2
def baseEnd_1474688 : Nat := 757223759417631510118039

theorem tailTrace_1474688 : CollatzResearch.WordTrace tailWord_1474688 prefixEnd_1474688 757223759417631510118039 := by
  unfold tailWord_1474688
  simp only [CollatzResearch.WordTrace]
  refine ⟨26893145040732353752088359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35857526720976471669451145 26893145040732353752088359)
  ·
    refine ⟨40339717561098530628132539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26893145040732353752088359 40339717561098530628132539)
    ·
      refine ⟨60509576341647795942198809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40339717561098530628132539 60509576341647795942198809)
      ·
        refine ⟨45382182256235846956649107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60509576341647795942198809 45382182256235846956649107)
        ·
          refine ⟨68073273384353770434973661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45382182256235846956649107 68073273384353770434973661)
          ·
            refine ⟨25527477519132663913115123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68073273384353770434973661 25527477519132663913115123)
            ·
              refine ⟨38291216278698995869672685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25527477519132663913115123 38291216278698995869672685)
              ·
                refine ⟨14359206104512123451127257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38291216278698995869672685 14359206104512123451127257)
                ·
                  refine ⟨10769404578384092588345443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14359206104512123451127257 10769404578384092588345443)
                  ·
                    refine ⟨16154106867576138882518165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10769404578384092588345443 16154106867576138882518165)
                    ·
                      refine ⟨757223759417631510118039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16154106867576138882518165 757223759417631510118039)
                      ·
                        rfl

theorem cell23_1474688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_1474688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474688 prefixEnd_1474688 := by exact prefixLift 1474688
  have htrace : WordTrace (prefixWord ++ tailWord_1474688) baseStart_1474688 baseEnd_1474688 := by
    simpa [prefixWord, tailWord_1474688, baseEnd_1474688] using wordTrace_append hprefix tailTrace_1474688
  have hstable : (prefixWord ++ tailWord_1474688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474688).length < 2 ^ (prefixWord ++ tailWord_1474688).sum := by decide
  have hdescent : baseEnd_1474688 < baseStart_1474688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474692 : List Nat := [2, 3, 2, 1, 2, 1, 2, 2, 2, 4, 2]
def baseStart_1474692 : Nat := 118140960795 + 1474692 * 2 ^ 59
def prefixEnd_1474692 : Nat := 4983230072969 + 3 ^ 40 * 1474692 * 2
def baseEnd_1474692 : Nat := 757225813340249494468021

theorem tailTrace_1474692 : CollatzResearch.WordTrace tailWord_1474692 prefixEnd_1474692 757225813340249494468021 := by
  unfold tailWord_1474692
  simp only [CollatzResearch.WordTrace]
  refine ⟨26893217986725108093661165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35857623982300144124881553 26893217986725108093661165)
  ·
    refine ⟨10084956745021915535122937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26893217986725108093661165 10084956745021915535122937)
    ·
      refine ⟨7563717558766436651342203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10084956745021915535122937 7563717558766436651342203)
      ·
        refine ⟨11345576338149654977013305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7563717558766436651342203 11345576338149654977013305)
        ·
          refine ⟨8509182253612241232759979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11345576338149654977013305 8509182253612241232759979)
          ·
            refine ⟨12763773380418361849139969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8509182253612241232759979 12763773380418361849139969)
            ·
              refine ⟨9572830035313771386854977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12763773380418361849139969 9572830035313771386854977)
              ·
                refine ⟨7179622526485328540141233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9572830035313771386854977 7179622526485328540141233)
                ·
                  refine ⟨5384716894863996405105925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7179622526485328540141233 5384716894863996405105925)
                  ·
                    refine ⟨1009634417786999325957361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5384716894863996405105925 1009634417786999325957361)
                    ·
                      refine ⟨757225813340249494468021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1009634417786999325957361 757225813340249494468021)
                      ·
                        rfl

theorem cell23_1474692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_1474692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474692 prefixEnd_1474692 := by exact prefixLift 1474692
  have htrace : WordTrace (prefixWord ++ tailWord_1474692) baseStart_1474692 baseEnd_1474692 := by
    simpa [prefixWord, tailWord_1474692, baseEnd_1474692] using wordTrace_append hprefix tailTrace_1474692
  have hstable : (prefixWord ++ tailWord_1474692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474692).length < 2 ^ (prefixWord ++ tailWord_1474692).sum := by decide
  have hdescent : baseEnd_1474692 < baseStart_1474692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474785 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 3, 1, 5]
def baseStart_1474785 : Nat := 118140960795 + 1474785 * 2 ^ 59
def prefixEnd_1474785 : Nat := 4983230072969 + 3 ^ 40 * 1474785 * 2
def baseEnd_1474785 : Nat := 757273567041117630605093

theorem tailTrace_1474785 : CollatzResearch.WordTrace tailWord_1474785 prefixEnd_1474785 757273567041117630605093 := by
  unfold tailWord_1474785
  simp only [CollatzResearch.WordTrace]
  refine ⟨53789827962113293070457809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35859885308075528713638539 53789827962113293070457809)
  ·
    refine ⟨40342370971584969802843357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53789827962113293070457809 40342370971584969802843357)
    ·
      refine ⟨15128389114344363676066259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40342370971584969802843357 15128389114344363676066259)
      ·
        refine ⟨22692583671516545514099389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15128389114344363676066259 22692583671516545514099389)
        ·
          refine ⟨8509718876818704567787271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22692583671516545514099389 8509718876818704567787271)
          ·
            refine ⟨12764578315228056851680907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8509718876818704567787271 12764578315228056851680907)
            ·
              refine ⟨19146867472842085277521361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12764578315228056851680907 19146867472842085277521361)
              ·
                refine ⟨14360150604631563958141021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19146867472842085277521361 14360150604631563958141021)
                ·
                  refine ⟨5385056476736836484302883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14360150604631563958141021 5385056476736836484302883)
                  ·
                    refine ⟨8077584715105254726454325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5385056476736836484302883 8077584715105254726454325)
                    ·
                      refine ⟨757273567041117630605093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8077584715105254726454325 757273567041117630605093)
                      ·
                        rfl

theorem cell23_1474785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_1474785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474785 prefixEnd_1474785 := by exact prefixLift 1474785
  have htrace : WordTrace (prefixWord ++ tailWord_1474785) baseStart_1474785 baseEnd_1474785 := by
    simpa [prefixWord, tailWord_1474785, baseEnd_1474785] using wordTrace_append hprefix tailTrace_1474785
  have hstable : (prefixWord ++ tailWord_1474785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474785).length < 2 ^ (prefixWord ++ tailWord_1474785).sum := by decide
  have hdescent : baseEnd_1474785 < baseStart_1474785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474792 : List Nat := [2, 1, 4, 1, 2, 2, 1, 2, 4, 4]
def baseStart_1474792 : Nat := 118140960795 + 1474792 * 2 ^ 59
def prefixEnd_1474792 : Nat := 4983230072969 + 3 ^ 40 * 1474792 * 2
def baseEnd_1474792 : Nat := 252425720468566367739187

theorem tailTrace_1474792 : CollatzResearch.WordTrace tailWord_1474792 prefixEnd_1474792 252425720468566367739187 := by
  unfold tailWord_1474792
  simp only [CollatzResearch.WordTrace]
  refine ⟨26895041636543966632981315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35860055515391955510641753 26895041636543966632981315)
  ·
    refine ⟨40342562454815949949471973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26895041636543966632981315 40342562454815949949471973)
    ·
      refine ⟨7564230460277990615525995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40342562454815949949471973 7564230460277990615525995)
      ·
        refine ⟨11346345690416985923288993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7564230460277990615525995 11346345690416985923288993)
        ·
          refine ⟨8509759267812739442466745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11346345690416985923288993 8509759267812739442466745)
          ·
            refine ⟨6382319450859554581850059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8509759267812739442466745 6382319450859554581850059)
            ·
              refine ⟨9573479176289331872775089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6382319450859554581850059 9573479176289331872775089)
              ·
                refine ⟨7180109382216998904581317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9573479176289331872775089 7180109382216998904581317)
                ·
                  refine ⟨1346270509165687294608997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7180109382216998904581317 1346270509165687294608997)
                  ·
                    refine ⟨252425720468566367739187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1346270509165687294608997 252425720468566367739187)
                    ·
                      rfl

theorem cell23_1474792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_1474792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474792 prefixEnd_1474792 := by exact prefixLift 1474792
  have htrace : WordTrace (prefixWord ++ tailWord_1474792) baseStart_1474792 baseEnd_1474792 := by
    simpa [prefixWord, tailWord_1474792, baseEnd_1474792] using wordTrace_append hprefix tailTrace_1474792
  have hstable : (prefixWord ++ tailWord_1474792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474792).length < 2 ^ (prefixWord ++ tailWord_1474792).sum := by decide
  have hdescent : baseEnd_1474792 < baseStart_1474792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474795 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 4]
def baseStart_1474795 : Nat := 118140960795 + 1474795 * 2 ^ 59
def prefixEnd_1474795 : Nat := 4983230072969 + 3 ^ 40 * 1474795 * 2
def baseEnd_1474795 : Nat := 757278701847662591480047

theorem tailTrace_1474795 : CollatzResearch.WordTrace tailWord_1474795 prefixEnd_1474795 757278701847662591480047 := by
  unfold tailWord_1474795
  simp only [CollatzResearch.WordTrace]
  refine ⟨53790192692077064778321839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35860128461384709852214559 53790192692077064778321839)
  ·
    refine ⟨80685289038115597167482759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53790192692077064778321839 80685289038115597167482759)
    ·
      refine ⟨121027933557173395751224139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80685289038115597167482759 121027933557173395751224139)
      ·
        refine ⟨181541900335760093626836209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121027933557173395751224139 181541900335760093626836209)
        ·
          refine ⟨136156425251820070220127157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181541900335760093626836209 136156425251820070220127157)
          ·
            refine ⟨12764664867358131583136921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136156425251820070220127157 12764664867358131583136921)
            ·
              refine ⟨9573498650518598687352691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12764664867358131583136921 9573498650518598687352691)
              ·
                refine ⟨14360247975777898031029037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9573498650518598687352691 14360247975777898031029037)
                ·
                  refine ⟨5385092990916711761635889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14360247975777898031029037 5385092990916711761635889)
                  ·
                    refine ⟨4038819743187533821226917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5385092990916711761635889 4038819743187533821226917)
                    ·
                      refine ⟨757278701847662591480047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4038819743187533821226917 757278701847662591480047)
                      ·
                        rfl

theorem cell23_1474795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 4].length) (baseStart_1474795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474795 prefixEnd_1474795 := by exact prefixLift 1474795
  have htrace : WordTrace (prefixWord ++ tailWord_1474795) baseStart_1474795 baseEnd_1474795 := by
    simpa [prefixWord, tailWord_1474795, baseEnd_1474795] using wordTrace_append hprefix tailTrace_1474795
  have hstable : (prefixWord ++ tailWord_1474795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474795).length < 2 ^ (prefixWord ++ tailWord_1474795).sum := by decide
  have hdescent : baseEnd_1474795 < baseStart_1474795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474802 : List Nat := [3, 2, 1, 3, 2, 1, 1, 3, 1, 1, 5]
def baseStart_1474802 : Nat := 118140960795 + 1474802 * 2 ^ 59
def prefixEnd_1474802 : Nat := 4983230072969 + 3 ^ 40 * 1474802 * 2
def baseEnd_1474802 : Nat := 757282296212244064092515

theorem tailTrace_1474802 : CollatzResearch.WordTrace tailWord_1474802 prefixEnd_1474802 757282296212244064092515 := by
  unfold tailWord_1474802
  simp only [CollatzResearch.WordTrace]
  refine ⟨13447612000762926243456665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35860298668701136649217773 13447612000762926243456665)
  ·
    refine ⟨10085709000572194682592499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13447612000762926243456665 10085709000572194682592499)
    ·
      refine ⟨15128563500858292023888749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10085709000572194682592499 15128563500858292023888749)
      ·
        refine ⟨5673211312821859508958281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15128563500858292023888749 5673211312821859508958281)
        ·
          refine ⟨4254908484616394631718711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5673211312821859508958281 4254908484616394631718711)
          ·
            refine ⟨6382362726924591947578067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4254908484616394631718711 6382362726924591947578067)
            ·
              refine ⟨9573544090386887921367101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6382362726924591947578067 9573544090386887921367101)
              ·
                refine ⟨3590079033895082970512663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9573544090386887921367101 3590079033895082970512663)
                ·
                  refine ⟨5385118550842624455768995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3590079033895082970512663 5385118550842624455768995)
                  ·
                    refine ⟨8077677826263936683653493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5385118550842624455768995 8077677826263936683653493)
                    ·
                      refine ⟨757282296212244064092515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8077677826263936683653493 757282296212244064092515)
                      ·
                        rfl

theorem cell23_1474802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_1474802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474802 prefixEnd_1474802 := by exact prefixLift 1474802
  have htrace : WordTrace (prefixWord ++ tailWord_1474802) baseStart_1474802 baseEnd_1474802 := by
    simpa [prefixWord, tailWord_1474802, baseEnd_1474802] using wordTrace_append hprefix tailTrace_1474802
  have hstable : (prefixWord ++ tailWord_1474802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474802).length < 2 ^ (prefixWord ++ tailWord_1474802).sum := by decide
  have hdescent : baseEnd_1474802 < baseStart_1474802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474816 : List Nat := [2, 1, 1, 2, 1, 1, 4, 6, 1, 2, 2]
def baseStart_1474816 : Nat := 118140960795 + 1474816 * 2 ^ 59
def prefixEnd_1474816 : Nat := 4983230072969 + 3 ^ 40 * 1474816 * 2
def baseEnd_1474816 : Nat := 757289484941407009317451

theorem tailTrace_1474816 : CollatzResearch.WordTrace tailWord_1474816 prefixEnd_1474816 757289484941407009317451 := by
  unfold tailWord_1474816
  simp only [CollatzResearch.WordTrace]
  refine ⟨26895479312500492682418151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35860639083333990243224201 26895479312500492682418151)
  ·
    refine ⟨40343218968750739023627227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26895479312500492682418151 40343218968750739023627227)
    ·
      refine ⟨60514828453126108535440841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40343218968750739023627227 60514828453126108535440841)
      ·
        refine ⟨45386121339844581401580631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60514828453126108535440841 45386121339844581401580631)
        ·
          refine ⟨68079182009766872102370947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45386121339844581401580631 68079182009766872102370947)
          ·
            refine ⟨102118773014650308153556421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68079182009766872102370947 102118773014650308153556421)
            ·
              refine ⟨19147269940246932778791829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102118773014650308153556421 19147269940246932778791829)
              ·
                refine ⟨897528278449074974005867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19147269940246932778791829 897528278449074974005867)
                ·
                  refine ⟨1346292417673612461008801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 897528278449074974005867 1346292417673612461008801)
                  ·
                    refine ⟨1009719313255209345756601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1346292417673612461008801 1009719313255209345756601)
                    ·
                      refine ⟨757289484941407009317451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1009719313255209345756601 757289484941407009317451)
                      ·
                        rfl

theorem cell23_1474816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6, 1, 2, 2].length) (baseStart_1474816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474816 prefixEnd_1474816 := by exact prefixLift 1474816
  have htrace : WordTrace (prefixWord ++ tailWord_1474816) baseStart_1474816 baseEnd_1474816 := by
    simpa [prefixWord, tailWord_1474816, baseEnd_1474816] using wordTrace_append hprefix tailTrace_1474816
  have hstable : (prefixWord ++ tailWord_1474816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474816).length < 2 ^ (prefixWord ++ tailWord_1474816).sum := by decide
  have hdescent : baseEnd_1474816 < baseStart_1474816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474846 : List Nat := [4, 3, 2, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_1474846 : Nat := 118140960795 + 1474846 * 2 ^ 59
def prefixEnd_1474846 : Nat := 4983230072969 + 3 ^ 40 * 1474846 * 2
def baseEnd_1474846 : Nat := 757304889361041891942313

theorem tailTrace_1474846 : CollatzResearch.WordTrace tailWord_1474846 prefixEnd_1474846 757304889361041891942313 := by
  unfold tailWord_1474846
  simp only [CollatzResearch.WordTrace]
  refine ⟨6724006601861537561053549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35861368543261533658952261 6724006601861537561053549)
  ·
    refine ⟨2521502475698076585395081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6724006601861537561053549 2521502475698076585395081)
    ·
      refine ⟨1891126856773557439046311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2521502475698076585395081 1891126856773557439046311)
      ·
        refine ⟨2836690285160336158569467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1891126856773557439046311 2836690285160336158569467)
        ·
          refine ⟨4255035427740504237854201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2836690285160336158569467 4255035427740504237854201)
          ·
            refine ⟨3191276570805378178390651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4255035427740504237854201 3191276570805378178390651)
            ·
              refine ⟨4786914856208067267585977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3191276570805378178390651 4786914856208067267585977)
              ·
                refine ⟨3590186142156050450689483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4786914856208067267585977 3590186142156050450689483)
                ·
                  refine ⟨5385279213234075676034225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3590186142156050450689483 5385279213234075676034225)
                  ·
                    refine ⟨4038959409925556757025669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5385279213234075676034225 4038959409925556757025669)
                    ·
                      refine ⟨757304889361041891942313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4038959409925556757025669 757304889361041891942313)
                      ·
                        rfl

theorem cell23_1474846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_1474846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474846 prefixEnd_1474846 := by exact prefixLift 1474846
  have htrace : WordTrace (prefixWord ++ tailWord_1474846) baseStart_1474846 baseEnd_1474846 := by
    simpa [prefixWord, tailWord_1474846, baseEnd_1474846] using wordTrace_append hprefix tailTrace_1474846
  have hstable : (prefixWord ++ tailWord_1474846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474846).length < 2 ^ (prefixWord ++ tailWord_1474846).sum := by decide
  have hdescent : baseEnd_1474846 < baseStart_1474846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474889 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 6, 2, 2]
def baseStart_1474889 : Nat := 118140960795 + 1474889 * 2 ^ 59
def prefixEnd_1474889 : Nat := 4983230072969 + 3 ^ 40 * 1474889 * 2
def baseEnd_1474889 : Nat := 757326969029185223704615

theorem tailTrace_1474889 : CollatzResearch.WordTrace tailWord_1474889 prefixEnd_1474889 757326969029185223704615 := by
  unfold tailWord_1474889
  simp only [CollatzResearch.WordTrace]
  refine ⟨53793621153736518832243721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35862414102491012554829147 53793621153736518832243721)
  ·
    refine ⟨40345215865302389124182791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53793621153736518832243721 40345215865302389124182791)
    ·
      refine ⟨60517823797953583686274187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40345215865302389124182791 60517823797953583686274187)
      ·
        refine ⟨90776735696930375529411281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60517823797953583686274187 90776735696930375529411281)
        ·
          refine ⟨68082551772697781647058461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90776735696930375529411281 68082551772697781647058461)
          ·
            refine ⟨25530956914761668117646923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68082551772697781647058461 25530956914761668117646923)
            ·
              refine ⟨38296435372142502176470385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25530956914761668117646923 38296435372142502176470385)
              ·
                refine ⟨28722326529106876632352789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38296435372142502176470385 28722326529106876632352789)
                ·
                  refine ⟨1346359056051884842141537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28722326529106876632352789 1346359056051884842141537)
                  ·
                    refine ⟨1009769292038913631606153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1346359056051884842141537 1009769292038913631606153)
                    ·
                      refine ⟨757326969029185223704615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1009769292038913631606153 757326969029185223704615)
                      ·
                        rfl

theorem cell23_1474889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6, 2, 2].length) (baseStart_1474889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474889 prefixEnd_1474889 := by exact prefixLift 1474889
  have htrace : WordTrace (prefixWord ++ tailWord_1474889) baseStart_1474889 baseEnd_1474889 := by
    simpa [prefixWord, tailWord_1474889, baseEnd_1474889] using wordTrace_append hprefix tailTrace_1474889
  have hstable : (prefixWord ++ tailWord_1474889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474889).length < 2 ^ (prefixWord ++ tailWord_1474889).sum := by decide
  have hdescent : baseEnd_1474889 < baseStart_1474889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474892 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 2, 4, 3]
def baseStart_1474892 : Nat := 118140960795 + 1474892 * 2 ^ 59
def prefixEnd_1474892 : Nat := 4983230072969 + 3 ^ 40 * 1474892 * 2
def baseEnd_1474892 : Nat := 757328509471148711967101

theorem tailTrace_1474892 : CollatzResearch.WordTrace tailWord_1474892 prefixEnd_1474892 757328509471148711967101 := by
  unfold tailWord_1474892
  simp only [CollatzResearch.WordTrace]
  refine ⟨26896865286362825172301465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35862487048483766896401953 26896865286362825172301465)
  ·
    refine ⟨20172648964772118879226099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26896865286362825172301465 20172648964772118879226099)
    ·
      refine ⟨30258973447158178318839149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20172648964772118879226099 30258973447158178318839149)
      ·
        refine ⟨11347115042684316869564681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30258973447158178318839149 11347115042684316869564681)
        ·
          refine ⟨8510336282013237652173511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11347115042684316869564681 8510336282013237652173511)
          ·
            refine ⟨12765504423019856478260267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8510336282013237652173511 12765504423019856478260267)
            ·
              refine ⟨19148256634529784717390401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12765504423019856478260267 19148256634529784717390401)
              ·
                refine ⟨14361192475897338538042801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19148256634529784717390401 14361192475897338538042801)
                ·
                  refine ⟨10770894356923003903532101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14361192475897338538042801 10770894356923003903532101)
                  ·
                    refine ⟨2019542691923063231912269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10770894356923003903532101 2019542691923063231912269)
                    ·
                      refine ⟨757328509471148711967101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2019542691923063231912269 757328509471148711967101)
                      ·
                        rfl

theorem cell23_1474892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_1474892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474892 prefixEnd_1474892 := by exact prefixLift 1474892
  have htrace : WordTrace (prefixWord ++ tailWord_1474892) baseStart_1474892 baseEnd_1474892 := by
    simpa [prefixWord, tailWord_1474892, baseEnd_1474892] using wordTrace_append hprefix tailTrace_1474892
  have hstable : (prefixWord ++ tailWord_1474892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474892).length < 2 ^ (prefixWord ++ tailWord_1474892).sum := by decide
  have hdescent : baseEnd_1474892 < baseStart_1474892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474905 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 7]
def baseStart_1474905 : Nat := 118140960795 + 1474905 * 2 ^ 59
def prefixEnd_1474905 : Nat := 4983230072969 + 3 ^ 40 * 1474905 * 2
def baseEnd_1474905 : Nat := 757335184719657161104541

theorem tailTrace_1474905 : CollatzResearch.WordTrace tailWord_1474905 prefixEnd_1474905 757335184719657161104541 := by
  unfold tailWord_1474905
  simp only [CollatzResearch.WordTrace]
  refine ⟨53794204721678553564826169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35862803147785702376550779 53794204721678553564826169)
  ·
    refine ⟨40345653541258915173619627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53794204721678553564826169 40345653541258915173619627)
    ·
      refine ⟨60518480311888372760429441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40345653541258915173619627 60518480311888372760429441)
      ·
        refine ⟨45388860233916279570322081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60518480311888372760429441 45388860233916279570322081)
        ·
          refine ⟨34041645175437209677741561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45388860233916279570322081 34041645175437209677741561)
          ·
            refine ⟨25531233881577907258306171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34041645175437209677741561 25531233881577907258306171)
            ·
              refine ⟨38296850822366860887459257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25531233881577907258306171 38296850822366860887459257)
              ·
                refine ⟨28722638116775145665594443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38296850822366860887459257 28722638116775145665594443)
                ·
                  refine ⟨43083957175162718498391665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28722638116775145665594443 43083957175162718498391665)
                  ·
                    refine ⟨32312967881372038873793749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43083957175162718498391665 32312967881372038873793749)
                    ·
                      refine ⟨757335184719657161104541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 32312967881372038873793749 757335184719657161104541)
                      ·
                        rfl

theorem cell23_1474905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_1474905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474905 prefixEnd_1474905 := by exact prefixLift 1474905
  have htrace : WordTrace (prefixWord ++ tailWord_1474905) baseStart_1474905 baseEnd_1474905 := by
    simpa [prefixWord, tailWord_1474905, baseEnd_1474905] using wordTrace_append hprefix tailTrace_1474905
  have hstable : (prefixWord ++ tailWord_1474905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474905).length < 2 ^ (prefixWord ++ tailWord_1474905).sum := by decide
  have hdescent : baseEnd_1474905 < baseStart_1474905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1474979 : List Nat := [1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 4]
def baseStart_1474979 : Nat := 118140960795 + 1474979 * 2 ^ 59
def prefixEnd_1474979 : Nat := 4983230072969 + 3 ^ 40 * 1474979 * 2
def baseEnd_1474979 : Nat := 757373182288089871579201

theorem tailTrace_1474979 : CollatzResearch.WordTrace tailWord_1474979 prefixEnd_1474979 757373182288089871579201 := by
  unfold tailWord_1474979
  simp only [CollatzResearch.WordTrace]
  refine ⟨53796903723410464203019991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35864602482273642802013327 53796903723410464203019991)
  ·
    refine ⟨80695355585115696304529987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53796903723410464203019991 80695355585115696304529987)
    ·
      refine ⟨121043033377673544456794981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80695355585115696304529987 121043033377673544456794981)
      ·
        refine ⟨22695568758313789585649059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121043033377673544456794981 22695568758313789585649059)
        ·
          refine ⟨34043353137470684378473589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22695568758313789585649059 34043353137470684378473589)
          ·
            refine ⟨3191564356637876660481899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34043353137470684378473589 3191564356637876660481899)
            ·
              refine ⟨4787346534956814990722849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3191564356637876660481899 4787346534956814990722849)
              ·
                refine ⟨3590509901217611243042137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4787346534956814990722849 3590509901217611243042137)
                ·
                  refine ⟨2692882425913208432281603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3590509901217611243042137 2692882425913208432281603)
                  ·
                    refine ⟨4039323638869812648422405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2692882425913208432281603 4039323638869812648422405)
                    ·
                      refine ⟨757373182288089871579201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4039323638869812648422405 757373182288089871579201)
                      ·
                        rfl

theorem cell23_1474979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_1474979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1474979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1474979 prefixEnd_1474979 := by exact prefixLift 1474979
  have htrace : WordTrace (prefixWord ++ tailWord_1474979) baseStart_1474979 baseEnd_1474979 := by
    simpa [prefixWord, tailWord_1474979, baseEnd_1474979] using wordTrace_append hprefix tailTrace_1474979
  have hstable : (prefixWord ++ tailWord_1474979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1474979).length < 2 ^ (prefixWord ++ tailWord_1474979).sum := by decide
  have hdescent : baseEnd_1474979 < baseStart_1474979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1474979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475016 : List Nat := [2, 1, 3, 1, 3, 3, 2, 1, 2, 2, 3]
def baseStart_1475016 : Nat := 118140960795 + 1475016 * 2 ^ 59
def prefixEnd_1475016 : Nat := 4983230072969 + 3 ^ 40 * 1475016 * 2
def baseEnd_1475016 : Nat := 757392181072306226816531

theorem tailTrace_1475016 : CollatzResearch.WordTrace tailWord_1475016 prefixEnd_1475016 757392181072306226816531 := by
  unfold tailWord_1475016
  simp only [CollatzResearch.WordTrace]
  refine ⟨26899126612138209761058451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35865502149517613014744601 26899126612138209761058451)
  ·
    refine ⟨40348689918207314641587677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26899126612138209761058451 40348689918207314641587677)
    ·
      refine ⟨15130758719327742990595379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40348689918207314641587677 15130758719327742990595379)
      ·
        refine ⟨22696138078991614485893069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15130758719327742990595379 22696138078991614485893069)
        ·
          refine ⟨8511051779621855432209901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22696138078991614485893069 8511051779621855432209901)
          ·
            refine ⟨3191644417358195787078713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8511051779621855432209901 3191644417358195787078713)
            ·
              refine ⟨2393733313018646840309035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3191644417358195787078713 2393733313018646840309035)
              ·
                refine ⟨3590599969527970260463553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2393733313018646840309035 3590599969527970260463553)
                ·
                  refine ⟨2692949977145977695347665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3590599969527970260463553 2692949977145977695347665)
                  ·
                    refine ⟨2019712482859483271510749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2692949977145977695347665 2019712482859483271510749)
                    ·
                      refine ⟨757392181072306226816531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2019712482859483271510749 757392181072306226816531)
                      ·
                        rfl

theorem cell23_1475016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_1475016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475016 prefixEnd_1475016 := by exact prefixLift 1475016
  have htrace : WordTrace (prefixWord ++ tailWord_1475016) baseStart_1475016 baseEnd_1475016 := by
    simpa [prefixWord, tailWord_1475016, baseEnd_1475016] using wordTrace_append hprefix tailTrace_1475016
  have hstable : (prefixWord ++ tailWord_1475016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475016).length < 2 ^ (prefixWord ++ tailWord_1475016).sum := by decide
  have hdescent : baseEnd_1475016 < baseStart_1475016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475022 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8]
def baseStart_1475022 : Nat := 118140960795 + 1475022 * 2 ^ 59
def prefixEnd_1475022 : Nat := 4983230072969 + 3 ^ 40 * 1475022 * 2
def baseEnd_1475022 : Nat := 757395261956233203341503

theorem tailTrace_1475022 : CollatzResearch.WordTrace tailWord_1475022 prefixEnd_1475022 757395261956233203341503 := by
  unfold tailWord_1475022
  simp only [CollatzResearch.WordTrace]
  refine ⟨6724809007781835318354415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35865648041503121697890213 6724809007781835318354415)
  ·
    refine ⟨10087213511672752977531623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6724809007781835318354415 10087213511672752977531623)
    ·
      refine ⟨15130820267509129466297435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10087213511672752977531623 15130820267509129466297435)
      ·
        refine ⟨22696230401263694199446153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15130820267509129466297435 22696230401263694199446153)
        ·
          refine ⟨17022172800947770649584615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22696230401263694199446153 17022172800947770649584615)
          ·
            refine ⟨25533259201421655974376923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17022172800947770649584615 25533259201421655974376923)
            ·
              refine ⟨38299888802132483961565385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25533259201421655974376923 38299888802132483961565385)
              ·
                refine ⟨28724916601599362971174039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38299888802132483961565385 28724916601599362971174039)
                ·
                  refine ⟨43087374902399044456761059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28724916601599362971174039 43087374902399044456761059)
                  ·
                    refine ⟨64631062353598566685141589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43087374902399044456761059 64631062353598566685141589)
                    ·
                      refine ⟨757395261956233203341503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 64631062353598566685141589 757395261956233203341503)
                      ·
                        rfl

theorem cell23_1475022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_1475022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475022 prefixEnd_1475022 := by exact prefixLift 1475022
  have htrace : WordTrace (prefixWord ++ tailWord_1475022) baseStart_1475022 baseEnd_1475022 := by
    simpa [prefixWord, tailWord_1475022, baseEnd_1475022] using wordTrace_append hprefix tailTrace_1475022
  have hstable : (prefixWord ++ tailWord_1475022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475022).length < 2 ^ (prefixWord ++ tailWord_1475022).sum := by decide
  have hdescent : baseEnd_1475022 < baseStart_1475022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475069 : List Nat := [1, 4, 1, 1, 1, 3, 1, 3, 3, 1, 4]
def baseStart_1475069 : Nat := 118140960795 + 1475069 * 2 ^ 59
def prefixEnd_1475069 : Nat := 4983230072969 + 3 ^ 40 * 1475069 * 2
def baseEnd_1475069 : Nat := 757419395546994519453787

theorem tailTrace_1475069 : CollatzResearch.WordTrace tailWord_1475069 prefixEnd_1475069 757419395546994519453787 := by
  unfold tailWord_1475069
  simp only [CollatzResearch.WordTrace]
  refine ⟨53800186293084409573796261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35866790862056273049197507 53800186293084409573796261)
  ·
    refine ⟨10087534929953326795086799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53800186293084409573796261 10087534929953326795086799)
    ·
      refine ⟨15131302394929990192630199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10087534929953326795086799 15131302394929990192630199)
      ·
        refine ⟨22696953592394985288945299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15131302394929990192630199 22696953592394985288945299)
        ·
          refine ⟨34045430388592477933417949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22696953592394985288945299 34045430388592477933417949)
          ·
            refine ⟨12767036395722179225031731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34045430388592477933417949 12767036395722179225031731)
            ·
              refine ⟨19150554593583268837547597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12767036395722179225031731 19150554593583268837547597)
              ·
                refine ⟨7181457972593725814080349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19150554593583268837547597 7181457972593725814080349)
                ·
                  refine ⟨2693046739722647180280131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7181457972593725814080349 2693046739722647180280131)
                  ·
                    refine ⟨4039570109583970770420197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2693046739722647180280131 4039570109583970770420197)
                    ·
                      refine ⟨757419395546994519453787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4039570109583970770420197 757419395546994519453787)
                      ·
                        rfl

theorem cell23_1475069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_1475069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475069 prefixEnd_1475069 := by exact prefixLift 1475069
  have htrace : WordTrace (prefixWord ++ tailWord_1475069) baseStart_1475069 baseEnd_1475069 := by
    simpa [prefixWord, tailWord_1475069, baseEnd_1475069] using wordTrace_append hprefix tailTrace_1475069
  have hstable : (prefixWord ++ tailWord_1475069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475069).length < 2 ^ (prefixWord ++ tailWord_1475069).sum := by decide
  have hdescent : baseEnd_1475069 < baseStart_1475069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475073 : List Nat := [1, 2, 4, 1, 3, 1, 3, 1, 2, 3, 2]
def baseStart_1475073 : Nat := 118140960795 + 1475073 * 2 ^ 59
def prefixEnd_1475073 : Nat := 4983230072969 + 3 ^ 40 * 1475073 * 2
def baseEnd_1475073 : Nat := 757421449469612503803769

theorem tailTrace_1475073 : CollatzResearch.WordTrace tailWord_1475073 prefixEnd_1475073 757421449469612503803769 := by
  unfold tailWord_1475073
  simp only [CollatzResearch.WordTrace]
  refine ⟨53800332185069918256941873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35866888123379945504627915 53800332185069918256941873)
  ·
    refine ⟨40350249138802438692706405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53800332185069918256941873 40350249138802438692706405)
    ·
      refine ⟨7565671713525457254882451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40350249138802438692706405 7565671713525457254882451)
      ·
        refine ⟨11348507570288185882323677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7565671713525457254882451 11348507570288185882323677)
        ·
          refine ⟨4255690338858069705871379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11348507570288185882323677 4255690338858069705871379)
          ·
            refine ⟨6383535508287104558807069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4255690338858069705871379 6383535508287104558807069)
            ·
              refine ⟨2393825815607664209552651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6383535508287104558807069 2393825815607664209552651)
              ·
                refine ⟨3590738723411496314328977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2393825815607664209552651 3590738723411496314328977)
                ·
                  refine ⟨2693054042558622235746733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3590738723411496314328977 2693054042558622235746733)
                  ·
                    refine ⟨1009895265959483338405025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2693054042558622235746733 1009895265959483338405025)
                    ·
                      refine ⟨757421449469612503803769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1009895265959483338405025 757421449469612503803769)
                      ·
                        rfl

theorem cell23_1475073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_1475073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475073 prefixEnd_1475073 := by exact prefixLift 1475073
  have htrace : WordTrace (prefixWord ++ tailWord_1475073) baseStart_1475073 baseEnd_1475073 := by
    simpa [prefixWord, tailWord_1475073, baseEnd_1475073] using wordTrace_append hprefix tailTrace_1475073
  have hstable : (prefixWord ++ tailWord_1475073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475073).length < 2 ^ (prefixWord ++ tailWord_1475073).sum := by decide
  have hdescent : baseEnd_1475073 < baseStart_1475073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475083 : List Nat := [1, 1, 1, 1, 7, 3, 2, 1, 1, 5]
def baseStart_1475083 : Nat := 118140960795 + 1475083 * 2 ^ 59
def prefixEnd_1475083 : Nat := 4983230072969 + 3 ^ 40 * 1475083 * 2
def baseEnd_1475083 : Nat := 252475528092052488226241

theorem tailTrace_1475083 : CollatzResearch.WordTrace tailWord_1475083 prefixEnd_1475083 252475528092052488226241 := by
  unfold tailWord_1475083
  simp only [CollatzResearch.WordTrace]
  refine ⟨53800696915033689964805903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35867131276689126643203935 53800696915033689964805903)
  ·
    refine ⟨80701045372550534947208855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53800696915033689964805903 80701045372550534947208855)
    ·
      refine ⟨121051568058825802420813283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80701045372550534947208855 121051568058825802420813283)
      ·
        refine ⟨181577352088238703631219925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121051568058825802420813283 181577352088238703631219925)
        ·
          refine ⟨4255719189568094616356717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 181577352088238703631219925 4255719189568094616356717)
          ·
            refine ⟨1595894696088035481133769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4255719189568094616356717 1595894696088035481133769)
            ·
              refine ⟨1196921022066026610850327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1595894696088035481133769 1196921022066026610850327)
              ·
                refine ⟨1795381533099039916275491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1196921022066026610850327 1795381533099039916275491)
                ·
                  refine ⟨2693072299648559874413237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1795381533099039916275491 2693072299648559874413237)
                  ·
                    refine ⟨252475528092052488226241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2693072299648559874413237 252475528092052488226241)
                    ·
                      rfl

theorem cell23_1475083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 1, 5].length) (baseStart_1475083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475083 prefixEnd_1475083 := by exact prefixLift 1475083
  have htrace : WordTrace (prefixWord ++ tailWord_1475083) baseStart_1475083 baseEnd_1475083 := by
    simpa [prefixWord, tailWord_1475083, baseEnd_1475083] using wordTrace_append hprefix tailTrace_1475083
  have hstable : (prefixWord ++ tailWord_1475083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475083).length < 2 ^ (prefixWord ++ tailWord_1475083).sum := by decide
  have hdescent : baseEnd_1475083 < baseStart_1475083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475089 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 3]
def baseStart_1475089 : Nat := 118140960795 + 1475089 * 2 ^ 59
def prefixEnd_1475089 : Nat := 4983230072969 + 3 ^ 40 * 1475089 * 2
def baseEnd_1475089 : Nat := 757429665160084441203695

theorem tailTrace_1475089 : CollatzResearch.WordTrace tailWord_1475089 prefixEnd_1475089 757429665160084441203695 := by
  unfold tailWord_1475089
  simp only [CollatzResearch.WordTrace]
  refine ⟨53800915753011952989524321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35867277168674635326349547 53800915753011952989524321)
  ·
    refine ⟨40350686814758964742143241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53800915753011952989524321 40350686814758964742143241)
    ·
      refine ⟨30263015111069223556607431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40350686814758964742143241 30263015111069223556607431)
      ·
        refine ⟨45394522666603835334911147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30263015111069223556607431 45394522666603835334911147)
        ·
          refine ⟨68091783999905753002366721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45394522666603835334911147 68091783999905753002366721)
          ·
            refine ⟨51068837999929314751775041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68091783999905753002366721 51068837999929314751775041)
            ·
              refine ⟨38301628499946986063831281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51068837999929314751775041 38301628499946986063831281)
              ·
                refine ⟨28726221374960239547873461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38301628499946986063831281 28726221374960239547873461)
                ·
                  refine ⟨2693083253902522457613137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28726221374960239547873461 2693083253902522457613137)
                  ·
                    refine ⟨2019812440426891843209853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2693083253902522457613137 2019812440426891843209853)
                    ·
                      refine ⟨757429665160084441203695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2019812440426891843209853 757429665160084441203695)
                      ·
                        rfl

theorem cell23_1475089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 3].length) (baseStart_1475089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475089 prefixEnd_1475089 := by exact prefixLift 1475089
  have htrace : WordTrace (prefixWord ++ tailWord_1475089) baseStart_1475089 baseEnd_1475089 := by
    simpa [prefixWord, tailWord_1475089, baseEnd_1475089] using wordTrace_append hprefix tailTrace_1475089
  have hstable : (prefixWord ++ tailWord_1475089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475089).length < 2 ^ (prefixWord ++ tailWord_1475089).sum := by decide
  have hdescent : baseEnd_1475089 < baseStart_1475089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475096 : List Nat := [2, 1, 2, 3, 3, 2, 1, 1, 4, 4]
def baseStart_1475096 : Nat := 118140960795 + 1475096 * 2 ^ 59
def prefixEnd_1475096 : Nat := 4983230072969 + 3 ^ 40 * 1475096 * 2
def baseEnd_1475096 : Nat := 252477753174888637938721

theorem tailTrace_1475096 : CollatzResearch.WordTrace tailWord_1475096 prefixEnd_1475096 252477753174888637938721 := by
  unfold tailWord_1475096
  simp only [CollatzResearch.WordTrace]
  refine ⟨26900585531993296592514571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35867447375991062123352761 26900585531993296592514571)
  ·
    refine ⟨40350878297989944888771857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26900585531993296592514571 40350878297989944888771857)
    ·
      refine ⟨30263158723492458666578893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40350878297989944888771857 30263158723492458666578893)
      ·
        refine ⟨11348684521309671999967085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30263158723492458666578893 11348684521309671999967085)
        ·
          refine ⟨4255756695491126999987657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11348684521309671999967085 4255756695491126999987657)
          ·
            refine ⟨3191817521618345249990743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4255756695491126999987657 3191817521618345249990743)
            ·
              refine ⟨4787726282427517874986115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3191817521618345249990743 4787726282427517874986115)
              ·
                refine ⟨7181589423641276812479173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4787726282427517874986115 7181589423641276812479173)
                ·
                  refine ⟨1346548016932739402339845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7181589423641276812479173 1346548016932739402339845)
                  ·
                    refine ⟨252477753174888637938721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1346548016932739402339845 252477753174888637938721)
                    ·
                      rfl

theorem cell23_1475096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 4, 4].length) (baseStart_1475096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475096 prefixEnd_1475096 := by exact prefixLift 1475096
  have htrace : WordTrace (prefixWord ++ tailWord_1475096) baseStart_1475096 baseEnd_1475096 := by
    simpa [prefixWord, tailWord_1475096, baseEnd_1475096] using wordTrace_append hprefix tailTrace_1475096
  have hstable : (prefixWord ++ tailWord_1475096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475096).length < 2 ^ (prefixWord ++ tailWord_1475096).sum := by decide
  have hdescent : baseEnd_1475096 < baseStart_1475096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475117 : List Nat := [1, 5, 4, 1, 1, 1, 2, 2, 1, 5]
def baseStart_1475117 : Nat := 118140960795 + 1475117 * 2 ^ 59
def prefixEnd_1475117 : Nat := 4983230072969 + 3 ^ 40 * 1475117 * 2
def baseEnd_1475117 : Nat := 252481347539470110551189

theorem tailTrace_1475117 : CollatzResearch.WordTrace tailWord_1475117 prefixEnd_1475117 252481347539470110551189 := by
  unfold tailWord_1475117
  simp only [CollatzResearch.WordTrace]
  refine ⟨53801936996910513771543605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35867957997940342514362403 53801936996910513771543605)
  ·
    refine ⟨5043931593460360666082213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53801936996910513771543605 5043931593460360666082213)
    ·
      refine ⟨945737173773817624890415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5043931593460360666082213 945737173773817624890415)
      ·
        refine ⟨1418605760660726437335623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 945737173773817624890415 1418605760660726437335623)
        ·
          refine ⟨2127908640991089656003435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1418605760660726437335623 2127908640991089656003435)
          ·
            refine ⟨3191862961486634484005153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2127908640991089656003435 3191862961486634484005153)
            ·
              refine ⟨2393897221114975863003865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3191862961486634484005153 2393897221114975863003865)
              ·
                refine ⟨1795422915836231897252899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2393897221114975863003865 1795422915836231897252899)
                ·
                  refine ⟨2693134373754347845879349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1795422915836231897252899 2693134373754347845879349)
                  ·
                    refine ⟨252481347539470110551189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2693134373754347845879349 252481347539470110551189)
                    ·
                      rfl

theorem cell23_1475117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_1475117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475117 prefixEnd_1475117 := by exact prefixLift 1475117
  have htrace : WordTrace (prefixWord ++ tailWord_1475117) baseStart_1475117 baseEnd_1475117 := by
    simpa [prefixWord, tailWord_1475117, baseEnd_1475117] using wordTrace_append hprefix tailTrace_1475117
  have hstable : (prefixWord ++ tailWord_1475117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475117).length < 2 ^ (prefixWord ++ tailWord_1475117).sum := by decide
  have hdescent : baseEnd_1475117 < baseStart_1475117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475126 : List Nat := [5, 1, 2, 1, 2, 2, 1, 9]
def baseStart_1475126 : Nat := 118140960795 + 1475126 * 2 ^ 59
def prefixEnd_1475126 : Nat := 4983230072969 + 3 ^ 40 * 1475126 * 2
def baseEnd_1475126 : Nat := 28053654220159288757075

theorem tailTrace_1475126 : CollatzResearch.WordTrace tailWord_1475126 prefixEnd_1475126 28053654220159288757075 := by
  unfold tailWord_1475126
  simp only [CollatzResearch.WordTrace]
  refine ⟨3362641578367369269288827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35868176835918605539080821 3362641578367369269288827)
  ·
    refine ⟨5043962367551053903933241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3362641578367369269288827 5043962367551053903933241)
    ·
      refine ⟨3782971775663290427949931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5043962367551053903933241 3782971775663290427949931)
      ·
        refine ⟨5674457663494935641924897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3782971775663290427949931 5674457663494935641924897)
        ·
          refine ⟨4255843247621201731443673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5674457663494935641924897 4255843247621201731443673)
          ·
            refine ⟨3191882435715901298582755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4255843247621201731443673 3191882435715901298582755)
            ·
              refine ⟨4787823653573851947874133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3191882435715901298582755 4787823653573851947874133)
              ·
                refine ⟨28053654220159288757075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4787823653573851947874133 28053654220159288757075)
                ·
                  rfl

theorem cell23_1475126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_1475126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475126 prefixEnd_1475126 := by exact prefixLift 1475126
  have htrace : WordTrace (prefixWord ++ tailWord_1475126) baseStart_1475126 baseEnd_1475126 := by
    simpa [prefixWord, tailWord_1475126, baseEnd_1475126] using wordTrace_append hprefix tailTrace_1475126
  have hstable : (prefixWord ++ tailWord_1475126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475126).length < 2 ^ (prefixWord ++ tailWord_1475126).sum := by decide
  have hdescent : baseEnd_1475126 < baseStart_1475126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475136 : List Nat := [2, 1, 1, 2, 2, 2, 3, 2, 4, 1, 3]
def baseStart_1475136 : Nat := 118140960795 + 1475136 * 2 ^ 59
def prefixEnd_1475136 : Nat := 4983230072969 + 3 ^ 40 * 1475136 * 2
def baseEnd_1475136 : Nat := 757453798750845757315979

theorem tailTrace_1475136 : CollatzResearch.WordTrace tailWord_1475136 prefixEnd_1475136 757453798750845757315979 := by
  unfold tailWord_1475136
  simp only [CollatzResearch.WordTrace]
  refine ⟨26901314991920840008242631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35868419989227786677656841 26901314991920840008242631)
  ·
    refine ⟨40351972487881260012363947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26901314991920840008242631 40351972487881260012363947)
    ·
      refine ⟨60527958731821890018545921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40351972487881260012363947 60527958731821890018545921)
      ·
        refine ⟨45395969048866417513909441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60527958731821890018545921 45395969048866417513909441)
        ·
          refine ⟨34046976786649813135432081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45395969048866417513909441 34046976786649813135432081)
          ·
            refine ⟨25535232589987359851574061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34046976786649813135432081 25535232589987359851574061)
            ·
              refine ⟨9575712221245259944340273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25535232589987359851574061 9575712221245259944340273)
              ·
                refine ⟨7181784165933944958255205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9575712221245259944340273 7181784165933944958255205)
                ·
                  refine ⟨1346584531112614679672851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7181784165933944958255205 1346584531112614679672851)
                  ·
                    refine ⟨2019876796668922019509277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1346584531112614679672851 2019876796668922019509277)
                    ·
                      refine ⟨757453798750845757315979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2019876796668922019509277 757453798750845757315979)
                      ·
                        rfl

theorem cell23_1475136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 4, 1, 3].length) (baseStart_1475136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475136 prefixEnd_1475136 := by exact prefixLift 1475136
  have htrace : WordTrace (prefixWord ++ tailWord_1475136) baseStart_1475136 baseEnd_1475136 := by
    simpa [prefixWord, tailWord_1475136, baseEnd_1475136] using wordTrace_append hprefix tailTrace_1475136
  have hstable : (prefixWord ++ tailWord_1475136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475136).length < 2 ^ (prefixWord ++ tailWord_1475136).sum := by decide
  have hdescent : baseEnd_1475136 < baseStart_1475136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475137 : List Nat := [1, 2, 5, 1, 1, 2, 3, 3, 1, 2, 2]
def baseStart_1475137 : Nat := 118140960795 + 1475137 * 2 ^ 59
def prefixEnd_1475137 : Nat := 4983230072969 + 3 ^ 40 * 1475137 * 2
def baseEnd_1475137 : Nat := 757454312231500253403475

theorem tailTrace_1475137 : CollatzResearch.WordTrace tailWord_1475137 prefixEnd_1475137 757454312231500253403475 := by
  unfold tailWord_1475137
  simp only [CollatzResearch.WordTrace]
  refine ⟨53802666456838057187271665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35868444304558704791514443 53802666456838057187271665)
  ·
    refine ⟨40351999842628542890453749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53802666456838057187271665 40351999842628542890453749)
    ·
      refine ⟨3782999985246425895980039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40351999842628542890453749 3782999985246425895980039)
      ·
        refine ⟨5674499977869638843970059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3782999985246425895980039 5674499977869638843970059)
        ·
          refine ⟨8511749966804458265955089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5674499977869638843970059 8511749966804458265955089)
          ·
            refine ⟨6383812475103343699466317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8511749966804458265955089 6383812475103343699466317)
            ·
              refine ⟨2393929678163753887299869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6383812475103343699466317 2393929678163753887299869)
              ·
                refine ⟨897723629311407707737451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2393929678163753887299869 897723629311407707737451)
                ·
                  refine ⟨1346585443967111561606177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 897723629311407707737451 1346585443967111561606177)
                  ·
                    refine ⟨1009939082975333671204633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1346585443967111561606177 1009939082975333671204633)
                    ·
                      refine ⟨757454312231500253403475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1009939082975333671204633 757454312231500253403475)
                      ·
                        rfl

theorem cell23_1475137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_1475137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475137 prefixEnd_1475137 := by exact prefixLift 1475137
  have htrace : WordTrace (prefixWord ++ tailWord_1475137) baseStart_1475137 baseEnd_1475137 := by
    simpa [prefixWord, tailWord_1475137, baseEnd_1475137] using wordTrace_append hprefix tailTrace_1475137
  have hstable : (prefixWord ++ tailWord_1475137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475137).length < 2 ^ (prefixWord ++ tailWord_1475137).sum := by decide
  have hdescent : baseEnd_1475137 < baseStart_1475137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475159 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 4]
def baseStart_1475159 : Nat := 118140960795 + 1475159 * 2 ^ 59
def prefixEnd_1475159 : Nat := 4983230072969 + 3 ^ 40 * 1475159 * 2
def baseEnd_1475159 : Nat := 757465608805899167328373

theorem tailTrace_1475159 : CollatzResearch.WordTrace tailWord_1475159 prefixEnd_1475159 757465608805899167328373 := by
  unfold tailWord_1475159
  simp only [CollatzResearch.WordTrace]
  refine ⟨53803468862758354944572531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35868979241838903296381687 53803468862758354944572531)
  ·
    refine ⟨80705203294137532416858797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53803468862758354944572531 80705203294137532416858797)
    ·
      refine ⟨30264451235301574656322049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80705203294137532416858797 30264451235301574656322049)
      ·
        refine ⟨22698338426476180992241537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30264451235301574656322049 22698338426476180992241537)
        ·
          refine ⟨17023753819857135744181153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22698338426476180992241537 17023753819857135744181153)
          ·
            refine ⟨12767815364892851808135865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17023753819857135744181153 12767815364892851808135865)
            ·
              refine ⟨9575861523669638856101899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12767815364892851808135865 9575861523669638856101899)
              ·
                refine ⟨14363792285504458284152849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9575861523669638856101899 14363792285504458284152849)
                ·
                  refine ⟨10772844214128343713114637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14363792285504458284152849 10772844214128343713114637)
                  ·
                    refine ⟨4039816580298128892417989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10772844214128343713114637 4039816580298128892417989)
                    ·
                      refine ⟨757465608805899167328373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4039816580298128892417989 757465608805899167328373)
                      ·
                        rfl

theorem cell23_1475159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_1475159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475159 prefixEnd_1475159 := by exact prefixLift 1475159
  have htrace : WordTrace (prefixWord ++ tailWord_1475159) baseStart_1475159 baseEnd_1475159 := by
    simpa [prefixWord, tailWord_1475159, baseEnd_1475159] using wordTrace_append hprefix tailTrace_1475159
  have hstable : (prefixWord ++ tailWord_1475159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475159).length < 2 ^ (prefixWord ++ tailWord_1475159).sum := by decide
  have hdescent : baseEnd_1475159 < baseStart_1475159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475179 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 4, 4, 3]
def baseStart_1475179 : Nat := 118140960795 + 1475179 * 2 ^ 59
def prefixEnd_1475179 : Nat := 4983230072969 + 3 ^ 40 * 1475179 * 2
def baseEnd_1475179 : Nat := 757475878418989089078281

theorem tailTrace_1475179 : CollatzResearch.WordTrace tailWord_1475179 prefixEnd_1475179 757475878418989089078281 := by
  unfold tailWord_1475179
  simp only [CollatzResearch.WordTrace]
  refine ⟨53804198322685898360300591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35869465548457265573533727 53804198322685898360300591)
  ·
    refine ⟨80706297484028847540450887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53804198322685898360300591 80706297484028847540450887)
    ·
      refine ⟨121059446226043271310676331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80706297484028847540450887 121059446226043271310676331)
      ·
        refine ⟨181589169339064906966014497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121059446226043271310676331 181589169339064906966014497)
        ·
          refine ⟨136191877004298680224510873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181589169339064906966014497 136191877004298680224510873)
          ·
            refine ⟨102143907753224010168383155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136191877004298680224510873 102143907753224010168383155)
            ·
              refine ⟨153215861629836015252574733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102143907753224010168383155 153215861629836015252574733)
              ·
                refine ⟨57455948111188505719715525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153215861629836015252574733 57455948111188505719715525)
                ·
                  refine ⟨10772990270847844822446661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57455948111188505719715525 10772990270847844822446661)
                  ·
                    refine ⟨2019935675783970904208749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10772990270847844822446661 2019935675783970904208749)
                    ·
                      refine ⟨757475878418989089078281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2019935675783970904208749 757475878418989089078281)
                      ·
                        rfl

theorem cell23_1475179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4, 3].length) (baseStart_1475179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475179 prefixEnd_1475179 := by exact prefixLift 1475179
  have htrace : WordTrace (prefixWord ++ tailWord_1475179) baseStart_1475179 baseEnd_1475179 := by
    simpa [prefixWord, tailWord_1475179, baseEnd_1475179] using wordTrace_append hprefix tailTrace_1475179
  have hstable : (prefixWord ++ tailWord_1475179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475179).length < 2 ^ (prefixWord ++ tailWord_1475179).sum := by decide
  have hdescent : baseEnd_1475179 < baseStart_1475179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475193 : List Nat := [1, 2, 1, 3, 3, 3, 1, 2, 1, 4, 2]
def baseStart_1475193 : Nat := 118140960795 + 1475193 * 2 ^ 59
def prefixEnd_1475193 : Nat := 4983230072969 + 3 ^ 40 * 1475193 * 2
def baseEnd_1475193 : Nat := 757483067148152034303217

theorem tailTrace_1475193 : CollatzResearch.WordTrace tailWord_1475193 prefixEnd_1475193 757483067148152034303217 := by
  unfold tailWord_1475193
  simp only [CollatzResearch.WordTrace]
  refine ⟨53804708944635178751310233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35869805963090119167540155 53804708944635178751310233)
  ·
    refine ⟨40353531708476384063482675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53804708944635178751310233 40353531708476384063482675)
    ·
      refine ⟨60530297562714576095224013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40353531708476384063482675 60530297562714576095224013)
      ·
        refine ⟨22698861586017966035709005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60530297562714576095224013 22698861586017966035709005)
        ·
          refine ⟨8512073094756737263390877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22698861586017966035709005 8512073094756737263390877)
          ·
            refine ⟨3192027410533776473771579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8512073094756737263390877 3192027410533776473771579)
            ·
              refine ⟨4788041115800664710657369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3192027410533776473771579 4788041115800664710657369)
              ·
                refine ⟨3591030836850498532993027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4788041115800664710657369 3591030836850498532993027)
                ·
                  refine ⟨5386546255275747799489541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3591030836850498532993027 5386546255275747799489541)
                  ·
                    refine ⟨1009977422864202712404289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5386546255275747799489541 1009977422864202712404289)
                    ·
                      refine ⟨757483067148152034303217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1009977422864202712404289 757483067148152034303217)
                      ·
                        rfl

theorem cell23_1475193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 4, 2].length) (baseStart_1475193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475193 prefixEnd_1475193 := by exact prefixLift 1475193
  have htrace : WordTrace (prefixWord ++ tailWord_1475193) baseStart_1475193 baseEnd_1475193 := by
    simpa [prefixWord, tailWord_1475193, baseEnd_1475193] using wordTrace_append hprefix tailTrace_1475193
  have hstable : (prefixWord ++ tailWord_1475193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475193).length < 2 ^ (prefixWord ++ tailWord_1475193).sum := by decide
  have hdescent : baseEnd_1475193 < baseStart_1475193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475197 : List Nat := [1, 4, 1, 1, 5, 1, 3, 1, 1, 3, 2]
def baseStart_1475197 : Nat := 118140960795 + 1475197 * 2 ^ 59
def prefixEnd_1475197 : Nat := 4983230072969 + 3 ^ 40 * 1475197 * 2
def baseEnd_1475197 : Nat := 757485121070770018653199

theorem tailTrace_1475197 : CollatzResearch.WordTrace tailWord_1475197 prefixEnd_1475197 757485121070770018653199 := by
  unfold tailWord_1475197
  simp only [CollatzResearch.WordTrace]
  refine ⟨53804854836620687434455845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35869903224413791622970563 53804854836620687434455845)
  ·
    refine ⟨10088410281866378893960471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53804854836620687434455845 10088410281866378893960471)
    ·
      refine ⟨15132615422799568340940707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10088410281866378893960471 15132615422799568340940707)
      ·
        refine ⟨22698923134199352511411061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15132615422799568340940707 22698923134199352511411061)
        ·
          refine ⟨2128024043831189297944787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22698923134199352511411061 2128024043831189297944787)
          ·
            refine ⟨3192036065746783946917181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2128024043831189297944787 3192036065746783946917181)
            ·
              refine ⟨1197013524655043980093943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3192036065746783946917181 1197013524655043980093943)
              ·
                refine ⟨1795520286982565970140915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1197013524655043980093943 1795520286982565970140915)
                ·
                  refine ⟨2693280430473848955211373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1795520286982565970140915 2693280430473848955211373)
                  ·
                    refine ⟨1009980161427693358204265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2693280430473848955211373 1009980161427693358204265)
                    ·
                      refine ⟨757485121070770018653199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1009980161427693358204265 757485121070770018653199)
                      ·
                        rfl

theorem cell23_1475197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 1, 3, 2].length) (baseStart_1475197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475197 prefixEnd_1475197 := by exact prefixLift 1475197
  have htrace : WordTrace (prefixWord ++ tailWord_1475197) baseStart_1475197 baseEnd_1475197 := by
    simpa [prefixWord, tailWord_1475197, baseEnd_1475197] using wordTrace_append hprefix tailTrace_1475197
  have hstable : (prefixWord ++ tailWord_1475197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475197).length < 2 ^ (prefixWord ++ tailWord_1475197).sum := by decide
  have hdescent : baseEnd_1475197 < baseStart_1475197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475343 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 4, 3, 2]
def baseStart_1475343 : Nat := 118140960795 + 1475343 * 2 ^ 59
def prefixEnd_1475343 : Nat := 4983230072969 + 3 ^ 40 * 1475343 * 2
def baseEnd_1475343 : Nat := 757560089246326447427527

theorem tailTrace_1475343 : CollatzResearch.WordTrace tailWord_1475343 prefixEnd_1475343 757560089246326447427527 := by
  unfold tailWord_1475343
  simp only [CollatzResearch.WordTrace]
  refine ⟨53810179894091754369270683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35873453262727836246180455 53810179894091754369270683)
  ·
    refine ⟨80715269841137631553906025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53810179894091754369270683 80715269841137631553906025)
    ·
      refine ⟨60536452380853223665429519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80715269841137631553906025 60536452380853223665429519)
      ·
        refine ⟨90804678571279835498144279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60536452380853223665429519 90804678571279835498144279)
        ·
          refine ⟨136207017856919753247216419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90804678571279835498144279 136207017856919753247216419)
          ·
            refine ⟨204310526785379629870824629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136207017856919753247216419 204310526785379629870824629)
            ·
              refine ⟨19154111886129340300389809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 204310526785379629870824629 19154111886129340300389809)
              ·
                refine ⟨14365583914597005225292357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19154111886129340300389809 14365583914597005225292357)
                ·
                  refine ⟨2693546983986938479742317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14365583914597005225292357 2693546983986938479742317)
                  ·
                    refine ⟨1010080118995101929903369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2693546983986938479742317 1010080118995101929903369)
                    ·
                      refine ⟨757560089246326447427527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1010080118995101929903369 757560089246326447427527)
                      ·
                        rfl

theorem cell23_1475343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 3, 2].length) (baseStart_1475343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475343 prefixEnd_1475343 := by exact prefixLift 1475343
  have htrace : WordTrace (prefixWord ++ tailWord_1475343) baseStart_1475343 baseEnd_1475343 := by
    simpa [prefixWord, tailWord_1475343, baseEnd_1475343] using wordTrace_append hprefix tailTrace_1475343
  have hstable : (prefixWord ++ tailWord_1475343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475343).length < 2 ^ (prefixWord ++ tailWord_1475343).sum := by decide
  have hdescent : baseEnd_1475343 < baseStart_1475343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475360 : List Nat := [2, 1, 1, 5, 1, 2, 1, 3, 2, 3, 2]
def baseStart_1475360 : Nat := 118140960795 + 1475360 * 2 ^ 59
def prefixEnd_1475360 : Nat := 4983230072969 + 3 ^ 40 * 1475360 * 2
def baseEnd_1475360 : Nat := 757568818417452880914949

theorem tailTrace_1475360 : CollatzResearch.WordTrace tailWord_1475360 prefixEnd_1475360 757568818417452880914949 := by
  unfold tailWord_1475360
  simp only [CollatzResearch.WordTrace]
  refine ⟨26905399967515083136319767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35873866623353444181759689 26905399967515083136319767)
  ·
    refine ⟨40358099951272624704479651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26905399967515083136319767 40358099951272624704479651)
    ·
      refine ⟨60537149926908937056719477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40358099951272624704479651 60537149926908937056719477)
      ·
        refine ⟨5675357805647712849067451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60537149926908937056719477 5675357805647712849067451)
        ·
          refine ⟨8513036708471569273601177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5675357805647712849067451 8513036708471569273601177)
          ·
            refine ⟨6384777531353676955200883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8513036708471569273601177 6384777531353676955200883)
            ·
              refine ⟨9577166297030515432801325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6384777531353676955200883 9577166297030515432801325)
              ·
                refine ⟨3591437361386443287300497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9577166297030515432801325 3591437361386443287300497)
                ·
                  refine ⟨2693578021039832465475373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3591437361386443287300497 2693578021039832465475373)
                  ·
                    refine ⟨1010091757889937174553265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2693578021039832465475373 1010091757889937174553265)
                    ·
                      refine ⟨757568818417452880914949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1010091757889937174553265 757568818417452880914949)
                      ·
                        rfl

theorem cell23_1475360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_1475360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475360 prefixEnd_1475360 := by exact prefixLift 1475360
  have htrace : WordTrace (prefixWord ++ tailWord_1475360) baseStart_1475360 baseEnd_1475360 := by
    simpa [prefixWord, tailWord_1475360, baseEnd_1475360] using wordTrace_append hprefix tailTrace_1475360
  have hstable : (prefixWord ++ tailWord_1475360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475360).length < 2 ^ (prefixWord ++ tailWord_1475360).sum := by decide
  have hdescent : baseEnd_1475360 < baseStart_1475360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475406 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7]
def baseStart_1475406 : Nat := 118140960795 + 1475406 * 2 ^ 59
def prefixEnd_1475406 : Nat := 4983230072969 + 3 ^ 40 * 1475406 * 2
def baseEnd_1475406 : Nat := 757592438527559700939737

theorem tailTrace_1475406 : CollatzResearch.WordTrace tailWord_1475406 prefixEnd_1475406 757592438527559700939737 := by
  unfold tailWord_1475406
  simp only [CollatzResearch.WordTrace]
  refine ⟨6726559711607939516101759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35874985128575677419209381 6726559711607939516101759)
  ·
    refine ⟨10089839567411909274152639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6726559711607939516101759 10089839567411909274152639)
    ·
      refine ⟨15134759351117863911228959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10089839567411909274152639 15134759351117863911228959)
      ·
        refine ⟨22702139026676795866843439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15134759351117863911228959 22702139026676795866843439)
        ·
          refine ⟨34053208540015193800265159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22702139026676795866843439 34053208540015193800265159)
          ·
            refine ⟨51079812810022790700397739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34053208540015193800265159 51079812810022790700397739)
            ·
              refine ⟨76619719215034186050596609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51079812810022790700397739 76619719215034186050596609)
              ·
                refine ⟨57464789411275639537947457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76619719215034186050596609 57464789411275639537947457)
                ·
                  refine ⟨43098592058456729653460593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57464789411275639537947457 43098592058456729653460593)
                  ·
                    refine ⟨32323944043842547240095445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43098592058456729653460593 32323944043842547240095445)
                    ·
                      refine ⟨757592438527559700939737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 32323944043842547240095445 757592438527559700939737)
                      ·
                        rfl

theorem cell23_1475406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_1475406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475406 prefixEnd_1475406 := by exact prefixLift 1475406
  have htrace : WordTrace (prefixWord ++ tailWord_1475406) baseStart_1475406 baseEnd_1475406 := by
    simpa [prefixWord, tailWord_1475406, baseEnd_1475406] using wordTrace_append hprefix tailTrace_1475406
  have hstable : (prefixWord ++ tailWord_1475406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475406).length < 2 ^ (prefixWord ++ tailWord_1475406).sum := by decide
  have hdescent : baseEnd_1475406 < baseStart_1475406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475410 : List Nat := [3, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3]
def baseStart_1475410 : Nat := 118140960795 + 1475410 * 2 ^ 59
def prefixEnd_1475410 : Nat := 4983230072969 + 3 ^ 40 * 1475410 * 2
def baseEnd_1475410 : Nat := 757594492450177685289719

theorem tailTrace_1475410 : CollatzResearch.WordTrace tailWord_1475410 prefixEnd_1475410 757594492450177685289719 := by
  unfold tailWord_1475410
  simp only [CollatzResearch.WordTrace]
  refine ⟨13453155896212256202989921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35875082389899349874639789 13453155896212256202989921)
  ·
    refine ⟨10089866922159192152242441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13453155896212256202989921 10089866922159192152242441)
    ·
      refine ⟨7567400191619394114181831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10089866922159192152242441 7567400191619394114181831)
      ·
        refine ⟨11351100287429091171272747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7567400191619394114181831 11351100287429091171272747)
        ·
          refine ⟨17026650431143636756909121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11351100287429091171272747 17026650431143636756909121)
          ·
            refine ⟨12769987823357727567681841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17026650431143636756909121 12769987823357727567681841)
            ·
              refine ⟨9577490867518295675761381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12769987823357727567681841 9577490867518295675761381)
              ·
                refine ⟨1795779537659680439205259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9577490867518295675761381 1795779537659680439205259)
                ·
                  refine ⟨2693669306489520658807889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1795779537659680439205259 2693669306489520658807889)
                  ·
                    refine ⟨2020251979867140494105917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2693669306489520658807889 2020251979867140494105917)
                    ·
                      refine ⟨757594492450177685289719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2020251979867140494105917 757594492450177685289719)
                      ·
                        rfl

theorem cell23_1475410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_1475410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475410 prefixEnd_1475410 := by exact prefixLift 1475410
  have htrace : WordTrace (prefixWord ++ tailWord_1475410) baseStart_1475410 baseEnd_1475410 := by
    simpa [prefixWord, tailWord_1475410, baseEnd_1475410] using wordTrace_append hprefix tailTrace_1475410
  have hstable : (prefixWord ++ tailWord_1475410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475410).length < 2 ^ (prefixWord ++ tailWord_1475410).sum := by decide
  have hdescent : baseEnd_1475410 < baseStart_1475410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475413 : List Nat := [1, 3, 2, 2, 2, 1, 5, 7]
def baseStart_1475413 : Nat := 118140960795 + 1475413 * 2 ^ 59
def prefixEnd_1475413 : Nat := 4983230072969 + 3 ^ 40 * 1475413 * 2
def baseEnd_1475413 : Nat := 28059112329338561983415

theorem tailTrace_1475413 : CollatzResearch.WordTrace tailWord_1475413 prefixEnd_1475413 28059112329338561983415 := by
  unfold tailWord_1475413
  simp only [CollatzResearch.WordTrace]
  refine ⟨53812733003838156324318893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35875155335892104216212595 53812733003838156324318893)
  ·
    refine ⟨20179774876439308621619585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53812733003838156324318893 20179774876439308621619585)
    ·
      refine ⟨15134831157329481466214689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20179774876439308621619585 15134831157329481466214689)
      ·
        refine ⟨11351123367997111099661017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15134831157329481466214689 11351123367997111099661017)
        ·
          refine ⟨8513342525997833324745763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11351123367997111099661017 8513342525997833324745763)
          ·
            refine ⟨12770013788996749987118645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8513342525997833324745763 12770013788996749987118645)
            ·
              refine ⟨1197188792718445311292373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12770013788996749987118645 1197188792718445311292373)
              ·
                refine ⟨28059112329338561983415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1197188792718445311292373 28059112329338561983415)
                ·
                  rfl

theorem cell23_1475413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 7].length) (baseStart_1475413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475413 prefixEnd_1475413 := by exact prefixLift 1475413
  have htrace : WordTrace (prefixWord ++ tailWord_1475413) baseStart_1475413 baseEnd_1475413 := by
    simpa [prefixWord, tailWord_1475413, baseEnd_1475413] using wordTrace_append hprefix tailTrace_1475413
  have hstable : (prefixWord ++ tailWord_1475413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475413).length < 2 ^ (prefixWord ++ tailWord_1475413).sum := by decide
  have hdescent : baseEnd_1475413 < baseStart_1475413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475420 : List Nat := [2, 2, 4, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_1475420 : Nat := 118140960795 + 1475420 * 2 ^ 59
def prefixEnd_1475420 : Nat := 4983230072969 + 3 ^ 40 * 1475420 * 2
def baseEnd_1475420 : Nat := 757599627256722646164673

theorem tailTrace_1475420 : CollatzResearch.WordTrace tailWord_1475420 prefixEnd_1475420 757599627256722646164673 := by
  unfold tailWord_1475420
  simp only [CollatzResearch.WordTrace]
  refine ⟨26906494157406398259911857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35875325543208531013215809 26906494157406398259911857)
  ·
    refine ⟨20179870618054798694933893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26906494157406398259911857 20179870618054798694933893)
    ·
      refine ⟨3783725740885274755300105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20179870618054798694933893 3783725740885274755300105)
      ·
        refine ⟨2837794305663956066475079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3783725740885274755300105 2837794305663956066475079)
        ·
          refine ⟨4256691458495934099712619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2837794305663956066475079 4256691458495934099712619)
          ·
            refine ⟨6385037187743901149568929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4256691458495934099712619 6385037187743901149568929)
            ·
              refine ⟨4788777890807925862176697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6385037187743901149568929 4788777890807925862176697)
              ·
                refine ⟨3591583418105944396632523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4788777890807925862176697 3591583418105944396632523)
                ·
                  refine ⟨5387375127158916594948785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3591583418105944396632523 5387375127158916594948785)
                  ·
                    refine ⟨4040531345369187446211589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5387375127158916594948785 4040531345369187446211589)
                    ·
                      refine ⟨757599627256722646164673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4040531345369187446211589 757599627256722646164673)
                      ·
                        rfl

theorem cell23_1475420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_1475420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475420 prefixEnd_1475420 := by exact prefixLift 1475420
  have htrace : WordTrace (prefixWord ++ tailWord_1475420) baseStart_1475420 baseEnd_1475420 := by
    simpa [prefixWord, tailWord_1475420, baseEnd_1475420] using wordTrace_append hprefix tailTrace_1475420
  have hstable : (prefixWord ++ tailWord_1475420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475420).length < 2 ^ (prefixWord ++ tailWord_1475420).sum := by decide
  have hdescent : baseEnd_1475420 < baseStart_1475420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475423 : List Nat := [1, 1, 2, 3, 1, 3, 1, 4, 1, 3, 3]
def baseStart_1475423 : Nat := 118140960795 + 1475423 * 2 ^ 59
def prefixEnd_1475423 : Nat := 4983230072969 + 3 ^ 40 * 1475423 * 2
def baseEnd_1475423 : Nat := 757601167698686134427159

theorem tailTrace_1475423 : CollatzResearch.WordTrace tailWord_1475423 prefixEnd_1475423 757601167698686134427159 := by
  unfold tailWord_1475423
  simp only [CollatzResearch.WordTrace]
  refine ⟨53813097733801928032182923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35875398489201285354788615 53813097733801928032182923)
  ·
    refine ⟨80719646600702892048274385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53813097733801928032182923 80719646600702892048274385)
    ·
      refine ⟨60539734950527169036205789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80719646600702892048274385 60539734950527169036205789)
      ·
        refine ⟨22702400606447688388577171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60539734950527169036205789 22702400606447688388577171)
        ·
          refine ⟨34053600909671532582865757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22702400606447688388577171 34053600909671532582865757)
          ·
            refine ⟨12770100341126824718574659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34053600909671532582865757 12770100341126824718574659)
            ·
              refine ⟨19155150511690237077861989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12770100341126824718574659 19155150511690237077861989)
              ·
                refine ⟨3591590720941919452099123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19155150511690237077861989 3591590720941919452099123)
                ·
                  refine ⟨5387386081412879178148685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3591590720941919452099123 5387386081412879178148685)
                  ·
                    refine ⟨2020269780529829691805757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5387386081412879178148685 2020269780529829691805757)
                    ·
                      refine ⟨757601167698686134427159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2020269780529829691805757 757601167698686134427159)
                      ·
                        rfl

theorem cell23_1475423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_1475423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475423 prefixEnd_1475423 := by exact prefixLift 1475423
  have htrace : WordTrace (prefixWord ++ tailWord_1475423) baseStart_1475423 baseEnd_1475423 := by
    simpa [prefixWord, tailWord_1475423, baseEnd_1475423] using wordTrace_append hprefix tailTrace_1475423
  have hstable : (prefixWord ++ tailWord_1475423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475423).length < 2 ^ (prefixWord ++ tailWord_1475423).sum := by decide
  have hdescent : baseEnd_1475423 < baseStart_1475423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475424 : List Nat := [2, 1, 1, 3, 3, 1, 4, 3, 1, 2, 2]
def baseStart_1475424 : Nat := 118140960795 + 1475424 * 2 ^ 59
def prefixEnd_1475424 : Nat := 4983230072969 + 3 ^ 40 * 1475424 * 2
def baseEnd_1475424 : Nat := 757601681179340630514655

theorem tailTrace_1475424 : CollatzResearch.WordTrace tailWord_1475424 prefixEnd_1475424 757601681179340630514655 := by
  unfold tailWord_1475424
  simp only [CollatzResearch.WordTrace]
  refine ⟨26906567103399152601484663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35875422804532203468646217 26906567103399152601484663)
  ·
    refine ⟨40359850655098728902226995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26906567103399152601484663 40359850655098728902226995)
    ·
      refine ⟨60539775982648093353340493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40359850655098728902226995 60539775982648093353340493)
      ·
        refine ⟨22702415993493035007502685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60539775982648093353340493 22702415993493035007502685)
        ·
          refine ⟨8513405997559888127813507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22702415993493035007502685 8513405997559888127813507)
          ·
            refine ⟨12770108996339832191720261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8513405997559888127813507 12770108996339832191720261)
            ·
              refine ⟨2394395436813718535947549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12770108996339832191720261 2394395436813718535947549)
              ·
                refine ⟨897898288805144450980331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2394395436813718535947549 897898288805144450980331)
                ·
                  refine ⟨1346847433207716676470497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 897898288805144450980331 1346847433207716676470497)
                  ·
                    refine ⟨1010135574905787507352873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1346847433207716676470497 1010135574905787507352873)
                    ·
                      refine ⟨757601681179340630514655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1010135574905787507352873 757601681179340630514655)
                      ·
                        rfl

theorem cell23_1475424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3, 1, 2, 2].length) (baseStart_1475424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475424 prefixEnd_1475424 := by exact prefixLift 1475424
  have htrace : WordTrace (prefixWord ++ tailWord_1475424) baseStart_1475424 baseEnd_1475424 := by
    simpa [prefixWord, tailWord_1475424, baseEnd_1475424] using wordTrace_append hprefix tailTrace_1475424
  have hstable : (prefixWord ++ tailWord_1475424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475424).length < 2 ^ (prefixWord ++ tailWord_1475424).sum := by decide
  have hdescent : baseEnd_1475424 < baseStart_1475424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475427 : List Nat := [1, 1, 1, 5, 3, 1, 4, 1, 1, 2, 3]
def baseStart_1475427 : Nat := 118140960795 + 1475427 * 2 ^ 59
def prefixEnd_1475427 : Nat := 4983230072969 + 3 ^ 40 * 1475427 * 2
def baseEnd_1475427 : Nat := 757603221621304118777141

theorem tailTrace_1475427 : CollatzResearch.WordTrace tailWord_1475427 prefixEnd_1475427 757603221621304118777141 := by
  unfold tailWord_1475427
  simp only [CollatzResearch.WordTrace]
  refine ⟨53813243625787436715328535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35875495750524957810219023 53813243625787436715328535)
  ·
    refine ⟨80719865438681155072992803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53813243625787436715328535 80719865438681155072992803)
    ·
      refine ⟨121079798158021732609489205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80719865438681155072992803 121079798158021732609489205)
      ·
        refine ⟨11351231077314537432139613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121079798158021732609489205 11351231077314537432139613)
        ·
          refine ⟨4256711653992951537052355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11351231077314537432139613 4256711653992951537052355)
          ·
            refine ⟨6385067480989427305578533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4256711653992951537052355 6385067480989427305578533)
            ·
              refine ⟨1197200152685517619795975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6385067480989427305578533 1197200152685517619795975)
              ·
                refine ⟨1795800229028276429693963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1197200152685517619795975 1795800229028276429693963)
                ·
                  refine ⟨2693700343542414644540945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1795800229028276429693963 2693700343542414644540945)
                  ·
                    refine ⟨2020275257656810983405709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2693700343542414644540945 2020275257656810983405709)
                    ·
                      refine ⟨757603221621304118777141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2020275257656810983405709 757603221621304118777141)
                      ·
                        rfl

theorem cell23_1475427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_1475427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475427 prefixEnd_1475427 := by exact prefixLift 1475427
  have htrace : WordTrace (prefixWord ++ tailWord_1475427) baseStart_1475427 baseEnd_1475427 := by
    simpa [prefixWord, tailWord_1475427, baseEnd_1475427] using wordTrace_append hprefix tailTrace_1475427
  have hstable : (prefixWord ++ tailWord_1475427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475427).length < 2 ^ (prefixWord ++ tailWord_1475427).sum := by decide
  have hdescent : baseEnd_1475427 < baseStart_1475427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475454 : List Nat := [4, 2, 3, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_1475454 : Nat := 118140960795 + 1475454 * 2 ^ 59
def prefixEnd_1475454 : Nat := 4983230072969 + 3 ^ 40 * 1475454 * 2
def baseEnd_1475454 : Nat := 757617085598975513139517

theorem tailTrace_1475454 : CollatzResearch.WordTrace tailWord_1475454 prefixEnd_1475454 757617085598975513139517 := by
  unfold tailWord_1475454
  simp only [CollatzResearch.WordTrace]
  refine ⟨6726778549586202540820177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35876152264459746884374277 6726778549586202540820177)
  ·
    refine ⟨5045083912189651905615133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6726778549586202540820177 5045083912189651905615133)
    ·
      refine ⟨1891906467071119464605675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5045083912189651905615133 1891906467071119464605675)
      ·
        refine ⟨2837859700606679196908513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1891906467071119464605675 2837859700606679196908513)
        ·
          refine ⟨2128394775455009397681385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2837859700606679196908513 2128394775455009397681385)
          ·
            refine ⟨1596296081591257048261039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2128394775455009397681385 1596296081591257048261039)
            ·
              refine ⟨2394444122386885572391559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1596296081591257048261039 2394444122386885572391559)
              ·
                refine ⟨3591666183580328358587339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2394444122386885572391559 3591666183580328358587339)
                ·
                  refine ⟨5387499275370492537881009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3591666183580328358587339 5387499275370492537881009)
                  ·
                    refine ⟨4040624456527869403410757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5387499275370492537881009 4040624456527869403410757)
                    ·
                      refine ⟨757617085598975513139517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4040624456527869403410757 757617085598975513139517)
                      ·
                        rfl

theorem cell23_1475454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_1475454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475454 prefixEnd_1475454 := by exact prefixLift 1475454
  have htrace : WordTrace (prefixWord ++ tailWord_1475454) baseStart_1475454 baseEnd_1475454 := by
    simpa [prefixWord, tailWord_1475454, baseEnd_1475454] using wordTrace_append hprefix tailTrace_1475454
  have hstable : (prefixWord ++ tailWord_1475454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475454).length < 2 ^ (prefixWord ++ tailWord_1475454).sum := by decide
  have hdescent : baseEnd_1475454 < baseStart_1475454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475456 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 1, 8]
def baseStart_1475456 : Nat := 118140960795 + 1475456 * 2 ^ 59
def prefixEnd_1475456 : Nat := 4983230072969 + 3 ^ 40 * 1475456 * 2
def baseEnd_1475456 : Nat := 252539370853428168438169

theorem tailTrace_1475456 : CollatzResearch.WordTrace tailWord_1475456 prefixEnd_1475456 252539370853428168438169 := by
  unfold tailWord_1475456
  simp only [CollatzResearch.WordTrace]
  refine ⟨26907150671341187334067111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35876200895121583112089481 26907150671341187334067111)
  ·
    refine ⟨40360726007011781001100667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26907150671341187334067111 40360726007011781001100667)
    ·
      refine ⟨60541089010517671501651001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40360726007011781001100667 60541089010517671501651001)
      ·
        refine ⟨45405816757888253626238251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60541089010517671501651001 45405816757888253626238251)
        ·
          refine ⟨68108725136832380439357377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45405816757888253626238251 68108725136832380439357377)
          ·
            refine ⟨51081543852624285329518033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68108725136832380439357377 51081543852624285329518033)
            ·
              refine ⟨38311157889468213997138525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51081543852624285329518033 38311157889468213997138525)
              ·
                refine ⟨14366684208550580248926947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38311157889468213997138525 14366684208550580248926947)
                ·
                  refine ⟨21550026312825870373390421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14366684208550580248926947 21550026312825870373390421)
                  ·
                    refine ⟨252539370853428168438169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21550026312825870373390421 252539370853428168438169)
                    ·
                      rfl

theorem cell23_1475456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 1, 8].length) (baseStart_1475456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475456 prefixEnd_1475456 := by exact prefixLift 1475456
  have htrace : WordTrace (prefixWord ++ tailWord_1475456) baseStart_1475456 baseEnd_1475456 := by
    simpa [prefixWord, tailWord_1475456, baseEnd_1475456] using wordTrace_append hprefix tailTrace_1475456
  have hstable : (prefixWord ++ tailWord_1475456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475456).length < 2 ^ (prefixWord ++ tailWord_1475456).sum := by decide
  have hdescent : baseEnd_1475456 < baseStart_1475456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475497 : List Nat := [1, 2, 1, 1, 1, 1, 6, 4, 2, 2, 2]
def baseStart_1475497 : Nat := 118140960795 + 1475497 * 2 ^ 59
def prefixEnd_1475497 : Nat := 4983230072969 + 3 ^ 40 * 1475497 * 2
def baseEnd_1475497 : Nat := 757639165267118844901819

theorem tailTrace_1475497 : CollatzResearch.WordTrace tailWord_1475497 prefixEnd_1475497 757639165267118844901819 := by
  unfold tailWord_1475497
  simp only [CollatzResearch.WordTrace]
  refine ⟨53815796735533838670376745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35877197823689225780251163 53815796735533838670376745)
  ·
    refine ⟨40361847551650379002782559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53815796735533838670376745 40361847551650379002782559)
    ·
      refine ⟨60542771327475568504173839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40361847551650379002782559 60542771327475568504173839)
      ·
        refine ⟨90814156991213352756260759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60542771327475568504173839 90814156991213352756260759)
        ·
          refine ⟨136221235486820029134391139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90814156991213352756260759 136221235486820029134391139)
          ·
            refine ⟨204331853230230043701586709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136221235486820029134391139 204331853230230043701586709)
            ·
              refine ⟨9578055620167033298511877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 204331853230230043701586709 9578055620167033298511877)
              ·
                refine ⟨1795885428781318743470977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9578055620167033298511877 1795885428781318743470977)
                ·
                  refine ⟨1346914071585989057603233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1795885428781318743470977 1346914071585989057603233)
                  ·
                    refine ⟨1010185553689491793202425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1346914071585989057603233 1010185553689491793202425)
                    ·
                      refine ⟨757639165267118844901819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1010185553689491793202425 757639165267118844901819)
                      ·
                        rfl

theorem cell23_1475497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2, 2, 2].length) (baseStart_1475497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475497 prefixEnd_1475497 := by exact prefixLift 1475497
  have htrace : WordTrace (prefixWord ++ tailWord_1475497) baseStart_1475497 baseEnd_1475497 := by
    simpa [prefixWord, tailWord_1475497, baseEnd_1475497] using wordTrace_append hprefix tailTrace_1475497
  have hstable : (prefixWord ++ tailWord_1475497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475497).length < 2 ^ (prefixWord ++ tailWord_1475497).sum := by decide
  have hdescent : baseEnd_1475497 < baseStart_1475497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475508 : List Nat := [2, 5, 2, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_1475508 : Nat := 118140960795 + 1475508 * 2 ^ 59
def prefixEnd_1475508 : Nat := 4983230072969 + 3 ^ 40 * 1475508 * 2
def baseEnd_1475508 : Nat := 757644813554318301864269

theorem tailTrace_1475508 : CollatzResearch.WordTrace tailWord_1475508 prefixEnd_1475508 757644813554318301864269 := by
  unfold tailWord_1475508
  simp only [CollatzResearch.WordTrace]
  refine ⟨26908098969246993774513589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35877465292329325032684785 26908098969246993774513589)
  ·
    refine ⟨2522634278366905666360649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26908098969246993774513589 2522634278366905666360649)
    ·
      refine ⟨1891975708775179249770487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2522634278366905666360649 1891975708775179249770487)
      ·
        refine ⟨2837963563162768874655731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1891975708775179249770487 2837963563162768874655731)
        ·
          refine ⟨4256945344744153311983597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2837963563162768874655731 4256945344744153311983597)
          ·
            refine ⟨1596354504279057491993849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4256945344744153311983597 1596354504279057491993849)
            ·
              refine ⟨1197265878209293118995387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1596354504279057491993849 1197265878209293118995387)
              ·
                refine ⟨1795898817313939678493081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1197265878209293118995387 1795898817313939678493081)
                ·
                  refine ⟨1346924112985454758869811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1795898817313939678493081 1346924112985454758869811)
                  ·
                    refine ⟨2020386169478182138304717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1346924112985454758869811 2020386169478182138304717)
                    ·
                      refine ⟨757644813554318301864269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2020386169478182138304717 757644813554318301864269)
                      ·
                        rfl

theorem cell23_1475508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_1475508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475508 prefixEnd_1475508 := by exact prefixLift 1475508
  have htrace : WordTrace (prefixWord ++ tailWord_1475508) baseStart_1475508 baseEnd_1475508 := by
    simpa [prefixWord, tailWord_1475508, baseEnd_1475508] using wordTrace_append hprefix tailTrace_1475508
  have hstable : (prefixWord ++ tailWord_1475508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475508).length < 2 ^ (prefixWord ++ tailWord_1475508).sum := by decide
  have hdescent : baseEnd_1475508 < baseStart_1475508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475553 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 3, 3, 4]
def baseStart_1475553 : Nat := 118140960795 + 1475553 * 2 ^ 59
def prefixEnd_1475553 : Nat := 4983230072969 + 3 ^ 40 * 1475553 * 2
def baseEnd_1475553 : Nat := 757667920183770625801561

theorem tailTrace_1475553 : CollatzResearch.WordTrace tailWord_1475553 prefixEnd_1475553 757667920183770625801561 := by
  unfold tailWord_1475553
  simp only [CollatzResearch.WordTrace]
  refine ⟨53817839223330960234415313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35878559482220640156276875 53817839223330960234415313)
  ·
    refine ⟨40363379417498220175811485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53817839223330960234415313 40363379417498220175811485)
    ·
      refine ⟨15136267281561832565929307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40363379417498220175811485 15136267281561832565929307)
      ·
        refine ⟨22704400922342748848893961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15136267281561832565929307 22704400922342748848893961)
        ·
          refine ⟨17028300691757061636670471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22704400922342748848893961 17028300691757061636670471)
          ·
            refine ⟨25542451037635592455005707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17028300691757061636670471 25542451037635592455005707)
            ·
              refine ⟨38313676556453388682508561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25542451037635592455005707 38313676556453388682508561)
              ·
                refine ⟨28735257417340041511881421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38313676556453388682508561 28735257417340041511881421)
                ·
                  refine ⟨10775721531502515566955533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28735257417340041511881421 10775721531502515566955533)
                  ·
                    refine ⟨4040895574313443337608325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10775721531502515566955533 4040895574313443337608325)
                    ·
                      refine ⟨757667920183770625801561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4040895574313443337608325 757667920183770625801561)
                      ·
                        rfl

theorem cell23_1475553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_1475553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475553 prefixEnd_1475553 := by exact prefixLift 1475553
  have htrace : WordTrace (prefixWord ++ tailWord_1475553) baseStart_1475553 baseEnd_1475553 := by
    simpa [prefixWord, tailWord_1475553, baseEnd_1475553] using wordTrace_append hprefix tailTrace_1475553
  have hstable : (prefixWord ++ tailWord_1475553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475553).length < 2 ^ (prefixWord ++ tailWord_1475553).sum := by decide
  have hdescent : baseEnd_1475553 < baseStart_1475553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475554 : List Nat := [3, 3, 3, 1, 1, 2, 1, 4, 5]
def baseStart_1475554 : Nat := 118140960795 + 1475554 * 2 ^ 59
def prefixEnd_1475554 : Nat := 4983230072969 + 3 ^ 40 * 1475554 * 2
def baseEnd_1475554 : Nat := 84185381518269457987673

theorem tailTrace_1475554 : CollatzResearch.WordTrace tailWord_1475554 prefixEnd_1475554 84185381518269457987673 := by
  unfold tailWord_1475554
  simp only [CollatzResearch.WordTrace]
  refine ⟨13454468924081834351300429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35878583797551558270134477 13454468924081834351300429)
  ·
    refine ⟨5045425846530687881737661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13454468924081834351300429 5045425846530687881737661)
    ·
      refine ⟨1892034692449007955651623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5045425846530687881737661 1892034692449007955651623)
      ·
        refine ⟨2838052038673511933477435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1892034692449007955651623 2838052038673511933477435)
        ·
          refine ⟨4257078058010267900216153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2838052038673511933477435 4257078058010267900216153)
          ·
            refine ⟨3192808543507700925162115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4257078058010267900216153 3192808543507700925162115)
            ·
              refine ⟨4789212815261551387743173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3192808543507700925162115 4789212815261551387743173)
              ·
                refine ⟨897977402861540885201845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4789212815261551387743173 897977402861540885201845)
                ·
                  refine ⟨84185381518269457987673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 897977402861540885201845 84185381518269457987673)
                  ·
                    rfl

theorem cell23_1475554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_1475554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475554 prefixEnd_1475554 := by exact prefixLift 1475554
  have htrace : WordTrace (prefixWord ++ tailWord_1475554) baseStart_1475554 baseEnd_1475554 := by
    simpa [prefixWord, tailWord_1475554, baseEnd_1475554] using wordTrace_append hprefix tailTrace_1475554
  have hstable : (prefixWord ++ tailWord_1475554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475554).length < 2 ^ (prefixWord ++ tailWord_1475554).sum := by decide
  have hdescent : baseEnd_1475554 < baseStart_1475554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475580 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 5, 4]
def baseStart_1475580 : Nat := 118140960795 + 1475580 * 2 ^ 59
def prefixEnd_1475580 : Nat := 4983230072969 + 3 ^ 40 * 1475580 * 2
def baseEnd_1475580 : Nat := 252560594720480673387979

theorem tailTrace_1475580 : CollatzResearch.WordTrace tailWord_1475580 prefixEnd_1475580 252560594720480673387979 := by
  unfold tailWord_1475580
  simp only [CollatzResearch.WordTrace]
  refine ⟨26909411997116571922824097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35879215996155429230432129 26909411997116571922824097)
  ·
    refine ⟨20182058997837428942118073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26909411997116571922824097 20182058997837428942118073)
    ·
      refine ⟨15136544248378071706588555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20182058997837428942118073 15136544248378071706588555)
      ·
        refine ⟨22704816372567107559882833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15136544248378071706588555 22704816372567107559882833)
        ·
          refine ⟨17028612279425330669912125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22704816372567107559882833 17028612279425330669912125)
          ·
            refine ⟨6385729604784499001217047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17028612279425330669912125 6385729604784499001217047)
            ·
              refine ⟨9578594407176748501825571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6385729604784499001217047 9578594407176748501825571)
              ·
                refine ⟨14367891610765122752738357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9578594407176748501825571 14367891610765122752738357)
                ·
                  refine ⟨1346989838509230258069221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14367891610765122752738357 1346989838509230258069221)
                  ·
                    refine ⟨252560594720480673387979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1346989838509230258069221 252560594720480673387979)
                    ·
                      rfl

theorem cell23_1475580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_1475580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475580 prefixEnd_1475580 := by exact prefixLift 1475580
  have htrace : WordTrace (prefixWord ++ tailWord_1475580) baseStart_1475580 baseEnd_1475580 := by
    simpa [prefixWord, tailWord_1475580, baseEnd_1475580] using wordTrace_append hprefix tailTrace_1475580
  have hstable : (prefixWord ++ tailWord_1475580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475580).length < 2 ^ (prefixWord ++ tailWord_1475580).sum := by decide
  have hdescent : baseEnd_1475580 < baseStart_1475580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475630 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_1475630 : Nat := 118140960795 + 1475630 * 2 ^ 59
def prefixEnd_1475630 : Nat := 4983230072969 + 3 ^ 40 * 1475630 * 2
def baseEnd_1475630 : Nat := 757707458194166824538707

theorem tailTrace_1475630 : CollatzResearch.WordTrace tailWord_1475630 prefixEnd_1475630 757707458194166824538707 := by
  unfold tailWord_1475630
  simp only [CollatzResearch.WordTrace]
  refine ⟨6727580955506500298121043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35880431762701334923312229 6727580955506500298121043)
  ·
    refine ⟨10091371433259750447181565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6727580955506500298121043 10091371433259750447181565)
    ·
      refine ⟨3784264287472406417693087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10091371433259750447181565 3784264287472406417693087)
      ·
        refine ⟨5676396431208609626539631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3784264287472406417693087 5676396431208609626539631)
        ·
          refine ⟨8514594646812914439809447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5676396431208609626539631 8514594646812914439809447)
          ·
            refine ⟨12771891970219371659714171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8514594646812914439809447 12771891970219371659714171)
            ·
              refine ⟨19157837955329057489571257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12771891970219371659714171 19157837955329057489571257)
              ·
                refine ⟨14368378466496793117178443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19157837955329057489571257 14368378466496793117178443)
                ·
                  refine ⟨21552567699745189675767665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14368378466496793117178443 21552567699745189675767665)
                  ·
                    refine ⟨16164425774808892256825749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21552567699745189675767665 16164425774808892256825749)
                    ·
                      refine ⟨757707458194166824538707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16164425774808892256825749 757707458194166824538707)
                      ·
                        rfl

theorem cell23_1475630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_1475630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475630 prefixEnd_1475630 := by exact prefixLift 1475630
  have htrace : WordTrace (prefixWord ++ tailWord_1475630) baseStart_1475630 baseEnd_1475630 := by
    simpa [prefixWord, tailWord_1475630, baseEnd_1475630] using wordTrace_append hprefix tailTrace_1475630
  have hstable : (prefixWord ++ tailWord_1475630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475630).length < 2 ^ (prefixWord ++ tailWord_1475630).sum := by decide
  have hdescent : baseEnd_1475630 < baseStart_1475630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475647 : List Nat := [1, 1, 2, 2, 3, 1, 1, 5, 2, 3, 2]
def baseStart_1475647 : Nat := 118140960795 + 1475647 * 2 ^ 59
def prefixEnd_1475647 : Nat := 4983230072969 + 3 ^ 40 * 1475647 * 2
def baseEnd_1475647 : Nat := 757716187365293258026129

theorem tailTrace_1475647 : CollatzResearch.WordTrace tailWord_1475647 prefixEnd_1475647 757716187365293258026129 := by
  unfold tailWord_1475647
  simp only [CollatzResearch.WordTrace]
  refine ⟨53821267684990414288337195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35880845123326942858891463 53821267684990414288337195)
  ·
    refine ⟨80731901527485621432505793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53821267684990414288337195 80731901527485621432505793)
    ·
      refine ⟨60548926145614216074379345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80731901527485621432505793 60548926145614216074379345)
      ·
        refine ⟨45411694609210662055784509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60548926145614216074379345 45411694609210662055784509)
        ·
          refine ⟨17029385478453998270919191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45411694609210662055784509 17029385478453998270919191)
          ·
            refine ⟨25544078217680997406378787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17029385478453998270919191 25544078217680997406378787)
            ·
              refine ⟨38316117326521496109568181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25544078217680997406378787 38316117326521496109568181)
              ·
                refine ⟨3592135999361390260272017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38316117326521496109568181 3592135999361390260272017)
                ·
                  refine ⟨2694101999521042695204013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3592135999361390260272017 2694101999521042695204013)
                  ·
                    refine ⟨1010288249820391010701505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2694101999521042695204013 1010288249820391010701505)
                    ·
                      refine ⟨757716187365293258026129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1010288249820391010701505 757716187365293258026129)
                      ·
                        rfl

theorem cell23_1475647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 3, 2].length) (baseStart_1475647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475647 prefixEnd_1475647 := by exact prefixLift 1475647
  have htrace : WordTrace (prefixWord ++ tailWord_1475647) baseStart_1475647 baseEnd_1475647 := by
    simpa [prefixWord, tailWord_1475647, baseEnd_1475647] using wordTrace_append hprefix tailTrace_1475647
  have hstable : (prefixWord ++ tailWord_1475647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475647).length < 2 ^ (prefixWord ++ tailWord_1475647).sum := by decide
  have hdescent : baseEnd_1475647 < baseStart_1475647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475660 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 5, 1, 4]
def baseStart_1475660 : Nat := 118140960795 + 1475660 * 2 ^ 59
def prefixEnd_1475660 : Nat := 4983230072969 + 3 ^ 40 * 1475660 * 2
def baseEnd_1475660 : Nat := 757722862613801707163569

theorem tailTrace_1475660 : CollatzResearch.WordTrace tailWord_1475660 prefixEnd_1475660 757722862613801707163569 := by
  unfold tailWord_1475660
  simp only [CollatzResearch.WordTrace]
  refine ⟨26910870916971658754280217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35881161222628878339040289 26910870916971658754280217)
  ·
    refine ⟨20183153187728744065710163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26910870916971658754280217 20183153187728744065710163)
    ·
      refine ⟨30274729781593116098565245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20183153187728744065710163 30274729781593116098565245)
      ·
        refine ⟨11353023668097418536961967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30274729781593116098565245 11353023668097418536961967)
        ·
          refine ⟨17029535502146127805442951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11353023668097418536961967 17029535502146127805442951)
          ·
            refine ⟨25544303253219191708164427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17029535502146127805442951 25544303253219191708164427)
            ·
              refine ⟨38316454879828787562246641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25544303253219191708164427 38316454879828787562246641)
              ·
                refine ⟨28737341159871590671684981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38316454879828787562246641 28737341159871590671684981)
                ·
                  refine ⟨2694125733737961625470467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28737341159871590671684981 2694125733737961625470467)
                  ·
                    refine ⟨4041188600606942438205701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2694125733737961625470467 4041188600606942438205701)
                    ·
                      refine ⟨757722862613801707163569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4041188600606942438205701 757722862613801707163569)
                      ·
                        rfl

theorem cell23_1475660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_1475660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475660 prefixEnd_1475660 := by exact prefixLift 1475660
  have htrace : WordTrace (prefixWord ++ tailWord_1475660) baseStart_1475660 baseEnd_1475660 := by
    simpa [prefixWord, tailWord_1475660, baseEnd_1475660] using wordTrace_append hprefix tailTrace_1475660
  have hstable : (prefixWord ++ tailWord_1475660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475660).length < 2 ^ (prefixWord ++ tailWord_1475660).sum := by decide
  have hdescent : baseEnd_1475660 < baseStart_1475660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475678 : List Nat := [4, 4, 1, 1, 1, 3, 2, 1, 6]
def baseStart_1475678 : Nat := 118140960795 + 1475678 * 2 ^ 59
def prefixEnd_1475678 : Nat := 4983230072969 + 3 ^ 40 * 1475678 * 2
def baseEnd_1475678 : Nat := 84192456140620292970943

theorem tailTrace_1475678 : CollatzResearch.WordTrace tailWord_1475678 prefixEnd_1475678 84192456140620292970943 := by
  unfold tailWord_1475678
  simp only [CollatzResearch.WordTrace]
  refine ⟨6727799793484763322839461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35881598898585404388477125 6727799793484763322839461)
  ·
    refine ⟨1261462461278393123032399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6727799793484763322839461 1261462461278393123032399)
    ·
      refine ⟨1892193691917589684548599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1261462461278393123032399 1892193691917589684548599)
      ·
        refine ⟨2838290537876384526822899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1892193691917589684548599 2838290537876384526822899)
        ·
          refine ⟨4257435806814576790234349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2838290537876384526822899 4257435806814576790234349)
          ·
            refine ⟨1596538427555466296337881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4257435806814576790234349 1596538427555466296337881)
            ·
              refine ⟨1197403820666599722253411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1596538427555466296337881 1197403820666599722253411)
              ·
                refine ⟨1796105730999899583380117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1197403820666599722253411 1796105730999899583380117)
                ·
                  refine ⟨84192456140620292970943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1796105730999899583380117 84192456140620292970943)
                  ·
                    rfl

theorem cell23_1475678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_1475678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475678 prefixEnd_1475678 := by exact prefixLift 1475678
  have htrace : WordTrace (prefixWord ++ tailWord_1475678) baseStart_1475678 baseEnd_1475678 := by
    simpa [prefixWord, tailWord_1475678, baseEnd_1475678] using wordTrace_append hprefix tailTrace_1475678
  have hstable : (prefixWord ++ tailWord_1475678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475678).length < 2 ^ (prefixWord ++ tailWord_1475678).sum := by decide
  have hdescent : baseEnd_1475678 < baseStart_1475678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475680 : List Nat := [2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 5]
def baseStart_1475680 : Nat := 118140960795 + 1475680 * 2 ^ 59
def prefixEnd_1475680 : Nat := 4983230072969 + 3 ^ 40 * 1475680 * 2
def baseEnd_1475680 : Nat := 757733132226891628913477

theorem tailTrace_1475680 : CollatzResearch.WordTrace tailWord_1475680 prefixEnd_1475680 757733132226891628913477 := by
  unfold tailWord_1475680
  simp only [CollatzResearch.WordTrace]
  refine ⟨26911235646935430462144247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35881647529247240616192329 26911235646935430462144247)
  ·
    refine ⟨40366853470403145693216371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26911235646935430462144247 40366853470403145693216371)
    ·
      refine ⟨60550280205604718539824557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40366853470403145693216371 60550280205604718539824557)
      ·
        refine ⟨22706355077101769452434209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60550280205604718539824557 22706355077101769452434209)
        ·
          refine ⟨17029766307826327089325657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22706355077101769452434209 17029766307826327089325657)
          ·
            refine ⟨12772324730869745316994243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17029766307826327089325657 12772324730869745316994243)
            ·
              refine ⟨19158487096304617975491365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12772324730869745316994243 19158487096304617975491365)
              ·
                refine ⟨3592216330557115870404631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19158487096304617975491365 3592216330557115870404631)
                ·
                  refine ⟨5388324495835673805606947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3592216330557115870404631 5388324495835673805606947)
                  ·
                    refine ⟨8082486743753510708410421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5388324495835673805606947 8082486743753510708410421)
                    ·
                      refine ⟨757733132226891628913477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8082486743753510708410421 757733132226891628913477)
                      ·
                        rfl

theorem cell23_1475680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_1475680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475680 prefixEnd_1475680 := by exact prefixLift 1475680
  have htrace : WordTrace (prefixWord ++ tailWord_1475680) baseStart_1475680 baseEnd_1475680 := by
    simpa [prefixWord, tailWord_1475680, baseEnd_1475680] using wordTrace_append hprefix tailTrace_1475680
  have hstable : (prefixWord ++ tailWord_1475680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475680).length < 2 ^ (prefixWord ++ tailWord_1475680).sum := by decide
  have hdescent : baseEnd_1475680 < baseStart_1475680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475694 : List Nat := [4, 1, 2, 2, 1, 2, 3, 2, 1, 1, 4]
def baseStart_1475694 : Nat := 118140960795 + 1475694 * 2 ^ 59
def prefixEnd_1475694 : Nat := 4983230072969 + 3 ^ 40 * 1475694 * 2
def baseEnd_1475694 : Nat := 757740320956054574138413

theorem tailTrace_1475694 : CollatzResearch.WordTrace tailWord_1475694 prefixEnd_1475694 757740320956054574138413 := by
  unfold tailWord_1475694
  simp only [CollatzResearch.WordTrace]
  refine ⟨6727872739477517664412267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35881987943880094210198757 6727872739477517664412267)
  ·
    refine ⟨10091809109216276496618401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6727872739477517664412267 10091809109216276496618401)
    ·
      refine ⟨7568856831912207372463801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10091809109216276496618401 7568856831912207372463801)
      ·
        refine ⟨5676642623934155529347851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7568856831912207372463801 5676642623934155529347851)
        ·
          refine ⟨8514963935901233294021777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5676642623934155529347851 8514963935901233294021777)
          ·
            refine ⟨6386222951925924970516333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8514963935901233294021777 6386222951925924970516333)
            ·
              refine ⟨2394833606972221863943625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6386222951925924970516333 2394833606972221863943625)
              ·
                refine ⟨1796125205229166397957719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2394833606972221863943625 1796125205229166397957719)
                ·
                  refine ⟨2694187807843749596936579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1796125205229166397957719 2694187807843749596936579)
                  ·
                    refine ⟨4041281711765624395404869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2694187807843749596936579 4041281711765624395404869)
                    ·
                      refine ⟨757740320956054574138413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4041281711765624395404869 757740320956054574138413)
                      ·
                        rfl

theorem cell23_1475694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_1475694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475694 prefixEnd_1475694 := by exact prefixLift 1475694
  have htrace : WordTrace (prefixWord ++ tailWord_1475694) baseStart_1475694 baseEnd_1475694 := by
    simpa [prefixWord, tailWord_1475694, baseEnd_1475694] using wordTrace_append hprefix tailTrace_1475694
  have hstable : (prefixWord ++ tailWord_1475694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475694).length < 2 ^ (prefixWord ++ tailWord_1475694).sum := by decide
  have hdescent : baseEnd_1475694 < baseStart_1475694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475697 : List Nat := [1, 2, 2, 2, 1, 1, 2, 6, 1, 2, 3]
def baseStart_1475697 : Nat := 118140960795 + 1475697 * 2 ^ 59
def prefixEnd_1475697 : Nat := 4983230072969 + 3 ^ 40 * 1475697 * 2
def baseEnd_1475697 : Nat := 757741861398018062400899

theorem tailTrace_1475697 : CollatzResearch.WordTrace tailWord_1475697 prefixEnd_1475697 757741861398018062400899 := by
  unfold tailWord_1475697
  simp only [CollatzResearch.WordTrace]
  refine ⟨53823091334809272827657345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35882060889872848551771563 53823091334809272827657345)
  ·
    refine ⟨40367318501106954620743009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53823091334809272827657345 40367318501106954620743009)
    ·
      refine ⟨30275488875830215965557257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40367318501106954620743009 30275488875830215965557257)
      ·
        refine ⟨22706616656872661974167943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30275488875830215965557257 22706616656872661974167943)
        ·
          refine ⟨34059924985308992961251915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22706616656872661974167943 34059924985308992961251915)
          ·
            refine ⟨51089887477963489441877873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34059924985308992961251915 51089887477963489441877873)
            ·
              refine ⟨38317415608472617081408405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51089887477963489441877873 38317415608472617081408405)
              ·
                refine ⟨1796128856647153925691019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38317415608472617081408405 1796128856647153925691019)
                ·
                  refine ⟨2694193284970730888536529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1796128856647153925691019 2694193284970730888536529)
                  ·
                    refine ⟨2020644963728048166402397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2694193284970730888536529 2020644963728048166402397)
                    ·
                      refine ⟨757741861398018062400899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2020644963728048166402397 757741861398018062400899)
                      ·
                        rfl

theorem cell23_1475697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_1475697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475697 prefixEnd_1475697 := by exact prefixLift 1475697
  have htrace : WordTrace (prefixWord ++ tailWord_1475697) baseStart_1475697 baseEnd_1475697 := by
    simpa [prefixWord, tailWord_1475697, baseEnd_1475697] using wordTrace_append hprefix tailTrace_1475697
  have hstable : (prefixWord ++ tailWord_1475697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475697).length < 2 ^ (prefixWord ++ tailWord_1475697).sum := by decide
  have hdescent : baseEnd_1475697 < baseStart_1475697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475744 : List Nat := [2, 1, 1, 4, 2, 1, 1, 5, 2, 1, 3]
def baseStart_1475744 : Nat := 118140960795 + 1475744 * 2 ^ 59
def prefixEnd_1475744 : Nat := 4983230072969 + 3 ^ 40 * 1475744 * 2
def baseEnd_1475744 : Nat := 757765994988779378513183

theorem tailTrace_1475744 : CollatzResearch.WordTrace tailWord_1475744 prefixEnd_1475744 757765994988779378513183 := by
  unfold tailWord_1475744
  simp only [CollatzResearch.WordTrace]
  refine ⟨26912402782819499927309143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35883203710425999903078857 26912402782819499927309143)
  ·
    refine ⟨40368604174229249890963715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26912402782819499927309143 40368604174229249890963715)
    ·
      refine ⟨60552906261343874836445573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40368604174229249890963715 60552906261343874836445573)
      ·
        refine ⟨11353669924001976531833545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60552906261343874836445573 11353669924001976531833545)
        ·
          refine ⟨8515252443001482398875159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11353669924001976531833545 8515252443001482398875159)
          ·
            refine ⟨12772878664502223598312739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8515252443001482398875159 12772878664502223598312739)
            ·
              refine ⟨19159317996753335397469109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12772878664502223598312739 19159317996753335397469109)
              ·
                refine ⟨1796186062195625193512729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19159317996753335397469109 1796186062195625193512729)
                ·
                  refine ⟨1347139546646718895134547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1796186062195625193512729 1347139546646718895134547)
                  ·
                    refine ⟨2020709319970078342701821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1347139546646718895134547 2020709319970078342701821)
                    ·
                      refine ⟨757765994988779378513183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2020709319970078342701821 757765994988779378513183)
                      ·
                        rfl

theorem cell23_1475744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_1475744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475744 prefixEnd_1475744 := by exact prefixLift 1475744
  have htrace : WordTrace (prefixWord ++ tailWord_1475744) baseStart_1475744 baseEnd_1475744 := by
    simpa [prefixWord, tailWord_1475744, baseEnd_1475744] using wordTrace_append hprefix tailTrace_1475744
  have hstable : (prefixWord ++ tailWord_1475744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475744).length < 2 ^ (prefixWord ++ tailWord_1475744).sum := by decide
  have hdescent : baseEnd_1475744 < baseStart_1475744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475770 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5]
def baseStart_1475770 : Nat := 118140960795 + 1475770 * 2 ^ 59
def prefixEnd_1475770 : Nat := 4983230072969 + 3 ^ 40 * 1475770 * 2
def baseEnd_1475770 : Nat := 757779345485796276788063

theorem tailTrace_1475770 : CollatzResearch.WordTrace tailWord_1475770 prefixEnd_1475770 757779345485796276788063 := by
  unfold tailWord_1475770
  simp only [CollatzResearch.WordTrace]
  refine ⟨13456438465886201573766191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35883835909029870863376509 13456438465886201573766191)
  ·
    refine ⟨20184657698829302360649287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13456438465886201573766191 20184657698829302360649287)
    ·
      refine ⟨30276986548243953540973931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20184657698829302360649287 30276986548243953540973931)
      ·
        refine ⟨45415479822365930311460897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30276986548243953540973931 45415479822365930311460897)
        ·
          refine ⟨34061609866774447733595673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45415479822365930311460897 34061609866774447733595673)
          ·
            refine ⟨25546207400080835800196755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34061609866774447733595673 25546207400080835800196755)
            ·
              refine ⟨38319311100121253700295133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25546207400080835800196755 38319311100121253700295133)
              ·
                refine ⟨14369741662545470137610675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38319311100121253700295133 14369741662545470137610675)
                ·
                  refine ⟨21554612493818205206416013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14369741662545470137610675 21554612493818205206416013)
                  ·
                    refine ⟨8082979685181826952406005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21554612493818205206416013 8082979685181826952406005)
                    ·
                      refine ⟨757779345485796276788063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8082979685181826952406005 757779345485796276788063)
                      ·
                        rfl

theorem cell23_1475770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_1475770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475770 prefixEnd_1475770 := by exact prefixLift 1475770
  have htrace : WordTrace (prefixWord ++ tailWord_1475770) baseStart_1475770 baseEnd_1475770 := by
    simpa [prefixWord, tailWord_1475770, baseEnd_1475770] using wordTrace_append hprefix tailTrace_1475770
  have hstable : (prefixWord ++ tailWord_1475770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475770).length < 2 ^ (prefixWord ++ tailWord_1475770).sum := by decide
  have hdescent : baseEnd_1475770 < baseStart_1475770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475841 : List Nat := [1, 2, 4, 1, 1, 4, 3, 2, 5]
def baseStart_1475841 : Nat := 118140960795 + 1475841 * 2 ^ 59
def prefixEnd_1475841 : Nat := 4983230072969 + 3 ^ 40 * 1475841 * 2
def baseEnd_1475841 : Nat := 84201755845807277666693

theorem tailTrace_1475841 : CollatzResearch.WordTrace tailWord_1475841 prefixEnd_1475841 84201755845807277666693 := by
  unfold tailWord_1475841
  simp only [CollatzResearch.WordTrace]
  refine ⟨53828343446287585420899377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35885562297525056947266251 53828343446287585420899377)
  ·
    refine ⟨40371257584715689065674533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53828343446287585420899377 40371257584715689065674533)
    ·
      refine ⟨7569610797134191699813975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40371257584715689065674533 7569610797134191699813975)
      ·
        refine ⟨11354416195701287549720963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7569610797134191699813975 11354416195701287549720963)
        ·
          refine ⟨17031624293551931324581445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11354416195701287549720963 17031624293551931324581445)
          ·
            refine ⟨3193429555040987123359021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17031624293551931324581445 3193429555040987123359021)
            ·
              refine ⟨1197536083140370171259633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3193429555040987123359021 1197536083140370171259633)
              ·
                refine ⟨898152062355277628444725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1197536083140370171259633 898152062355277628444725)
                ·
                  refine ⟨84201755845807277666693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 898152062355277628444725 84201755845807277666693)
                  ·
                    rfl

theorem cell23_1475841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2, 5].length) (baseStart_1475841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475841 prefixEnd_1475841 := by exact prefixLift 1475841
  have htrace : WordTrace (prefixWord ++ tailWord_1475841) baseStart_1475841 baseEnd_1475841 := by
    simpa [prefixWord, tailWord_1475841, baseEnd_1475841] using wordTrace_append hprefix tailTrace_1475841
  have hstable : (prefixWord ++ tailWord_1475841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475841).length < 2 ^ (prefixWord ++ tailWord_1475841).sum := by decide
  have hdescent : baseEnd_1475841 < baseStart_1475841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475857 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 4]
def baseStart_1475857 : Nat := 118140960795 + 1475857 * 2 ^ 59
def prefixEnd_1475857 : Nat := 4983230072969 + 3 ^ 40 * 1475857 * 2
def baseEnd_1475857 : Nat := 757824018302737436400163

theorem tailTrace_1475857 : CollatzResearch.WordTrace tailWord_1475857 prefixEnd_1475857 757824018302737436400163 := by
  unfold tailWord_1475857
  simp only [CollatzResearch.WordTrace]
  refine ⟨53828927014229620153481825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35885951342819746768987883 53828927014229620153481825)
  ·
    refine ⟨40371695260672215115111369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53828927014229620153481825 40371695260672215115111369)
    ·
      refine ⟨30278771445504161336333527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40371695260672215115111369 30278771445504161336333527)
      ·
        refine ⟨45418157168256242004500291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30278771445504161336333527 45418157168256242004500291)
        ·
          refine ⟨68127235752384363006750437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45418157168256242004500291 68127235752384363006750437)
          ·
            refine ⟨12773856703572068063765707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68127235752384363006750437 12773856703572068063765707)
            ·
              refine ⟨19160785055358102095648561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12773856703572068063765707 19160785055358102095648561)
              ·
                refine ⟨14370588791518576571736421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19160785055358102095648561 14370588791518576571736421)
                ·
                  refine ⟨2694485398409733107200579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14370588791518576571736421 2694485398409733107200579)
                  ·
                    refine ⟨4041728097614599660800869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2694485398409733107200579 4041728097614599660800869)
                    ·
                      refine ⟨757824018302737436400163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4041728097614599660800869 757824018302737436400163)
                      ·
                        rfl

theorem cell23_1475857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_1475857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475857 prefixEnd_1475857 := by exact prefixLift 1475857
  have htrace : WordTrace (prefixWord ++ tailWord_1475857) baseStart_1475857 baseEnd_1475857 := by
    simpa [prefixWord, tailWord_1475857, baseEnd_1475857] using wordTrace_append hprefix tailTrace_1475857
  have hstable : (prefixWord ++ tailWord_1475857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475857).length < 2 ^ (prefixWord ++ tailWord_1475857).sum := by decide
  have hdescent : baseEnd_1475857 < baseStart_1475857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475867 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 5, 4]
def baseStart_1475867 : Nat := 118140960795 + 1475867 * 2 ^ 59
def prefixEnd_1475867 : Nat := 4983230072969 + 3 ^ 40 * 1475867 * 2
def baseEnd_1475867 : Nat := 252609717703094132425039

theorem tailTrace_1475867 : CollatzResearch.WordTrace tailWord_1475867 prefixEnd_1475867 252609717703094132425039 := by
  unfold tailWord_1475867
  simp only [CollatzResearch.WordTrace]
  refine ⟨53829291744193391861345855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35886194496128927907563903 53829291744193391861345855)
  ·
    refine ⟨80743937616290087792018783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53829291744193391861345855 80743937616290087792018783)
    ·
      refine ⟨121115906424435131688028175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80743937616290087792018783 121115906424435131688028175)
      ·
        refine ⟨181673859636652697532042263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121115906424435131688028175 181673859636652697532042263)
        ·
          refine ⟨272510789454979046298063395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181673859636652697532042263 272510789454979046298063395)
          ·
            refine ⟨408766184182468569447095093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272510789454979046298063395 408766184182468569447095093)
            ·
              refine ⟨38321829767106428385665165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 408766184182468569447095093 38321829767106428385665165)
              ·
                refine ⟨14370686162664910644624437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38321829767106428385665165 14370686162664910644624437)
                ·
                  refine ⟨1347251827749835372933541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14370686162664910644624437 1347251827749835372933541)
                  ·
                    refine ⟨252609717703094132425039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1347251827749835372933541 252609717703094132425039)
                    ·
                      rfl

theorem cell23_1475867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5, 4].length) (baseStart_1475867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475867 prefixEnd_1475867 := by exact prefixLift 1475867
  have htrace : WordTrace (prefixWord ++ tailWord_1475867) baseStart_1475867 baseEnd_1475867 := by
    simpa [prefixWord, tailWord_1475867, baseEnd_1475867] using wordTrace_append hprefix tailTrace_1475867
  have hstable : (prefixWord ++ tailWord_1475867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475867).length < 2 ^ (prefixWord ++ tailWord_1475867).sum := by decide
  have hdescent : baseEnd_1475867 < baseStart_1475867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475907 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 2, 5, 3]
def baseStart_1475907 : Nat := 118140960795 + 1475907 * 2 ^ 59
def prefixEnd_1475907 : Nat := 4983230072969 + 3 ^ 40 * 1475907 * 2
def baseEnd_1475907 : Nat := 757849692335462240774933

theorem tailTrace_1475907 : CollatzResearch.WordTrace tailWord_1475907 prefixEnd_1475907 757849692335462240774933 := by
  unfold tailWord_1475907
  simp only [CollatzResearch.WordTrace]
  refine ⟨53830750664048478692801975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35887167109365652461867983 53830750664048478692801975)
  ·
    refine ⟨80746125996072718039202963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53830750664048478692801975 80746125996072718039202963)
    ·
      refine ⟨121119188994109077058804445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80746125996072718039202963 121119188994109077058804445)
      ·
        refine ⟨45419695872790903897051667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121119188994109077058804445 45419695872790903897051667)
        ·
          refine ⟨68129543809186355845577501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45419695872790903897051667 68129543809186355845577501)
          ·
            refine ⟨25548578928444883442091563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68129543809186355845577501 25548578928444883442091563)
            ·
              refine ⟨38322868392667325163137345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25548578928444883442091563 38322868392667325163137345)
              ·
                refine ⟨28742151294500493872353009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38322868392667325163137345 28742151294500493872353009)
                ·
                  refine ⟨21556613470875370404264757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28742151294500493872353009 21556613470875370404264757)
                  ·
                    refine ⟨2020932512894565975399821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21556613470875370404264757 2020932512894565975399821)
                    ·
                      refine ⟨757849692335462240774933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2020932512894565975399821 757849692335462240774933)
                      ·
                        rfl

theorem cell23_1475907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5, 3].length) (baseStart_1475907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475907 prefixEnd_1475907 := by exact prefixLift 1475907
  have htrace : WordTrace (prefixWord ++ tailWord_1475907) baseStart_1475907 baseEnd_1475907 := by
    simpa [prefixWord, tailWord_1475907, baseEnd_1475907] using wordTrace_append hprefix tailTrace_1475907
  have hstable : (prefixWord ++ tailWord_1475907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475907).length < 2 ^ (prefixWord ++ tailWord_1475907).sum := by decide
  have hdescent : baseEnd_1475907 < baseStart_1475907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475908 : List Nat := [2, 3, 4, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_1475908 : Nat := 118140960795 + 1475908 * 2 ^ 59
def prefixEnd_1475908 : Nat := 4983230072969 + 3 ^ 40 * 1475908 * 2
def baseEnd_1475908 : Nat := 757850205816116736862429

theorem tailTrace_1475908 : CollatzResearch.WordTrace tailWord_1475908 prefixEnd_1475908 757850205816116736862429 := by
  unfold tailWord_1475908
  simp only [CollatzResearch.WordTrace]
  refine ⟨26915393568522427931794189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35887191424696570575725585 26915393568522427931794189)
  ·
    refine ⟨10093272588195910474422821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26915393568522427931794189 10093272588195910474422821)
    ·
      refine ⟨1892488610286733213954279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10093272588195910474422821 1892488610286733213954279)
      ·
        refine ⟨2838732915430099820931419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1892488610286733213954279 2838732915430099820931419)
        ·
          refine ⟨4258099373145149731397129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2838732915430099820931419 4258099373145149731397129)
          ·
            refine ⟨3193574529858862298547847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4258099373145149731397129 3193574529858862298547847)
            ·
              refine ⟨4790361794788293447821771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3193574529858862298547847 4790361794788293447821771)
              ·
                refine ⟨7185542692182440171732657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4790361794788293447821771 7185542692182440171732657)
                ·
                  refine ⟨5389157019136830128799493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7185542692182440171732657 5389157019136830128799493)
                  ·
                    refine ⟨1010466941088155649149905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5389157019136830128799493 1010466941088155649149905)
                    ·
                      refine ⟨757850205816116736862429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1010466941088155649149905 757850205816116736862429)
                      ·
                        rfl

theorem cell23_1475908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_1475908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475908 prefixEnd_1475908 := by exact prefixLift 1475908
  have htrace : WordTrace (prefixWord ++ tailWord_1475908) baseStart_1475908 baseEnd_1475908 := by
    simpa [prefixWord, tailWord_1475908, baseEnd_1475908] using wordTrace_append hprefix tailTrace_1475908
  have hstable : (prefixWord ++ tailWord_1475908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475908).length < 2 ^ (prefixWord ++ tailWord_1475908).sum := by decide
  have hdescent : baseEnd_1475908 < baseStart_1475908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475992 : List Nat := [2, 1, 2, 5, 2, 2, 1, 3, 1, 1, 3]
def baseStart_1475992 : Nat := 118140960795 + 1475992 * 2 ^ 59
def prefixEnd_1475992 : Nat := 4983230072969 + 3 ^ 40 * 1475992 * 2
def baseEnd_1475992 : Nat := 757893338191094408212043

theorem tailTrace_1475992 : CollatzResearch.WordTrace tailWord_1475992 prefixEnd_1475992 757893338191094408212043 := by
  unfold tailWord_1475992
  simp only [CollatzResearch.WordTrace]
  refine ⟨26916925434370269104823115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35889233912493692139764153 26916925434370269104823115)
  ·
    refine ⟨40375388151555403657234673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26916925434370269104823115 40375388151555403657234673)
    ·
      refine ⟨30281541113666552742926005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40375388151555403657234673 30281541113666552742926005)
      ·
        refine ⟨2838894479406239319649313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30281541113666552742926005 2838894479406239319649313)
        ·
          refine ⟨2129170859554679489736985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2838894479406239319649313 2129170859554679489736985)
          ·
            refine ⟨1596878144666009617302739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2129170859554679489736985 1596878144666009617302739)
            ·
              refine ⟨2395317216999014425954109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1596878144666009617302739 2395317216999014425954109)
              ·
                refine ⟨898243956374630409732791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2395317216999014425954109 898243956374630409732791)
                ·
                  refine ⟨1347365934561945614599187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 898243956374630409732791 1347365934561945614599187)
                  ·
                    refine ⟨2021048901842918421898781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1347365934561945614599187 2021048901842918421898781)
                    ·
                      refine ⟨757893338191094408212043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2021048901842918421898781 757893338191094408212043)
                      ·
                        rfl

theorem cell23_1475992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_1475992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475992 prefixEnd_1475992 := by exact prefixLift 1475992
  have htrace : WordTrace (prefixWord ++ tailWord_1475992) baseStart_1475992 baseEnd_1475992 := by
    simpa [prefixWord, tailWord_1475992, baseEnd_1475992] using wordTrace_append hprefix tailTrace_1475992
  have hstable : (prefixWord ++ tailWord_1475992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475992).length < 2 ^ (prefixWord ++ tailWord_1475992).sum := by decide
  have hdescent : baseEnd_1475992 < baseStart_1475992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1475994 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4]
def baseStart_1475994 : Nat := 118140960795 + 1475994 * 2 ^ 59
def prefixEnd_1475994 : Nat := 4983230072969 + 3 ^ 40 * 1475994 * 2
def baseEnd_1475994 : Nat := 757894365152403400387033

theorem tailTrace_1475994 : CollatzResearch.WordTrace tailWord_1475994 prefixEnd_1475994 757894365152403400387033 := by
  unfold tailWord_1475994
  simp only [CollatzResearch.WordTrace]
  refine ⟨13458480953683323137804759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35889282543155528367479357 13458480953683323137804759)
  ·
    refine ⟨20187721430524984706707139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13458480953683323137804759 20187721430524984706707139)
    ·
      refine ⟨30281582145787477060060709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20187721430524984706707139 30281582145787477060060709)
      ·
        refine ⟨5677796652335151948761383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30281582145787477060060709 5677796652335151948761383)
        ·
          refine ⟨8516694978502727923142075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5677796652335151948761383 8516694978502727923142075)
          ·
            refine ⟨12775042467754091884713113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8516694978502727923142075 12775042467754091884713113)
            ·
              refine ⟨9581281850815568913534835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12775042467754091884713113 9581281850815568913534835)
              ·
                refine ⟨14371922776223353370302253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9581281850815568913534835 14371922776223353370302253)
                ·
                  refine ⟨5389471041083757513863345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14371922776223353370302253 5389471041083757513863345)
                  ·
                    refine ⟨4042103280812818135397509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5389471041083757513863345 4042103280812818135397509)
                    ·
                      refine ⟨757894365152403400387033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4042103280812818135397509 757894365152403400387033)
                      ·
                        rfl

theorem cell23_1475994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_1475994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1475994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1475994 prefixEnd_1475994 := by exact prefixLift 1475994
  have htrace : WordTrace (prefixWord ++ tailWord_1475994) baseStart_1475994 baseEnd_1475994 := by
    simpa [prefixWord, tailWord_1475994, baseEnd_1475994] using wordTrace_append hprefix tailTrace_1475994
  have hstable : (prefixWord ++ tailWord_1475994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1475994).length < 2 ^ (prefixWord ++ tailWord_1475994).sum := by decide
  have hdescent : baseEnd_1475994 < baseStart_1475994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1475994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476025 : List Nat := [1, 2, 1, 4, 4, 2, 2, 1, 2, 4]
def baseStart_1476025 : Nat := 118140960795 + 1476025 * 2 ^ 59
def prefixEnd_1476025 : Nat := 4983230072969 + 3 ^ 40 * 1476025 * 2
def baseEnd_1476025 : Nat := 252636761017564259699797

theorem tailTrace_1476025 : CollatzResearch.WordTrace tailWord_1476025 prefixEnd_1476025 252636761017564259699797 := by
  unfold tailWord_1476025
  simp only [CollatzResearch.WordTrace]
  refine ⟨53835054477620984845597529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35890036318413989897065019 53835054477620984845597529)
  ·
    refine ⟨40376290858215738634198147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53835054477620984845597529 40376290858215738634198147)
    ·
      refine ⟨60564436287323607951297221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40376290858215738634198147 60564436287323607951297221)
      ·
        refine ⟨11355831803873176490868229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60564436287323607951297221 11355831803873176490868229)
        ·
          refine ⟨2129218463226220592037793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11355831803873176490868229 2129218463226220592037793)
          ·
            refine ⟨1596913847419665444028345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2129218463226220592037793 1596913847419665444028345)
            ·
              refine ⟨1197685385564749083021259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1596913847419665444028345 1197685385564749083021259)
              ·
                refine ⟨1796528078347123624531889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1197685385564749083021259 1796528078347123624531889)
                ·
                  refine ⟨1347396058760342718398917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1796528078347123624531889 1347396058760342718398917)
                  ·
                    refine ⟨252636761017564259699797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1347396058760342718398917 252636761017564259699797)
                    ·
                      rfl

theorem cell23_1476025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 2, 4].length) (baseStart_1476025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476025 prefixEnd_1476025 := by exact prefixLift 1476025
  have htrace : WordTrace (prefixWord ++ tailWord_1476025) baseStart_1476025 baseEnd_1476025 := by
    simpa [prefixWord, tailWord_1476025, baseEnd_1476025] using wordTrace_append hprefix tailTrace_1476025
  have hstable : (prefixWord ++ tailWord_1476025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476025).length < 2 ^ (prefixWord ++ tailWord_1476025).sum := by decide
  have hdescent : baseEnd_1476025 < baseStart_1476025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476088 : List Nat := [2, 1, 2, 1, 1, 6, 2, 1, 1, 4, 2]
def baseStart_1476088 : Nat := 118140960795 + 1476088 * 2 ^ 59
def prefixEnd_1476088 : Nat := 4983230072969 + 3 ^ 40 * 1476088 * 2
def baseEnd_1476088 : Nat := 757942632333926032611601

theorem tailTrace_1476088 : CollatzResearch.WordTrace tailWord_1476088 prefixEnd_1476088 757942632333926032611601 := by
  unfold tailWord_1476088
  simp only [CollatzResearch.WordTrace]
  refine ⟨26918676138196373302570459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35891568184261831070093945 26918676138196373302570459)
  ·
    refine ⟨40378014207294559953855689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26918676138196373302570459 40378014207294559953855689)
    ·
      refine ⟨30283510655470919965391767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40378014207294559953855689 30283510655470919965391767)
      ·
        refine ⟨45425265983206379948087651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30283510655470919965391767 45425265983206379948087651)
        ·
          refine ⟨68137898974809569922131477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45425265983206379948087651 68137898974809569922131477)
          ·
            refine ⟨3193964014444198590099913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68137898974809569922131477 3193964014444198590099913)
            ·
              refine ⟨2395473010833148942574935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3193964014444198590099913 2395473010833148942574935)
              ·
                refine ⟨3593209516249723413862403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2395473010833148942574935 3593209516249723413862403)
                ·
                  refine ⟨5389814274374585120793605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3593209516249723413862403 5389814274374585120793605)
                  ·
                    refine ⟨1010590176445234710148801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5389814274374585120793605 1010590176445234710148801)
                    ·
                      refine ⟨757942632333926032611601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1010590176445234710148801 757942632333926032611601)
                      ·
                        rfl

theorem cell23_1476088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 1, 4, 2].length) (baseStart_1476088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476088 prefixEnd_1476088 := by exact prefixLift 1476088
  have htrace : WordTrace (prefixWord ++ tailWord_1476088) baseStart_1476088 baseEnd_1476088 := by
    simpa [prefixWord, tailWord_1476088, baseEnd_1476088] using wordTrace_append hprefix tailTrace_1476088
  have hstable : (prefixWord ++ tailWord_1476088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476088).length < 2 ^ (prefixWord ++ tailWord_1476088).sum := by decide
  have hdescent : baseEnd_1476088 < baseStart_1476088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476109 : List Nat := [1, 7, 1, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_1476109 : Nat := 118140960795 + 1476109 * 2 ^ 59
def prefixEnd_1476109 : Nat := 4983230072969 + 3 ^ 40 * 1476109 * 2
def baseEnd_1476109 : Nat := 757953415427670450449005

theorem tailTrace_1476109 : CollatzResearch.WordTrace tailWord_1476109 prefixEnd_1476109 757953415427670450449005 := by
  unfold tailWord_1476109
  simp only [CollatzResearch.WordTrace]
  refine ⟨53838118209316667191655381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35892078806211111461103587 53838118209316667191655381)
  ·
    refine ⟨1261830895530859387304423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 53838118209316667191655381 1261830895530859387304423)
    ·
      refine ⟨1892746343296289080956635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1261830895530859387304423 1892746343296289080956635)
      ·
        refine ⟨2839119514944433621434953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1892746343296289080956635 2839119514944433621434953)
        ·
          refine ⟨2129339636208325216076215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2839119514944433621434953 2129339636208325216076215)
          ·
            refine ⟨3194009454312487824114323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2129339636208325216076215 3194009454312487824114323)
            ·
              refine ⟨4791014181468731736171485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3194009454312487824114323 4791014181468731736171485)
              ·
                refine ⟨1796630318050774401064307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4791014181468731736171485 1796630318050774401064307)
                ·
                  refine ⟨2694945477076161601596461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1796630318050774401064307 2694945477076161601596461)
                  ·
                    refine ⟨1010604553903560600598673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2694945477076161601596461 1010604553903560600598673)
                    ·
                      refine ⟨757953415427670450449005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1010604553903560600598673 757953415427670450449005)
                      ·
                        rfl

theorem cell23_1476109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_1476109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476109 prefixEnd_1476109 := by exact prefixLift 1476109
  have htrace : WordTrace (prefixWord ++ tailWord_1476109) baseStart_1476109 baseEnd_1476109 := by
    simpa [prefixWord, tailWord_1476109, baseEnd_1476109] using wordTrace_append hprefix tailTrace_1476109
  have hstable : (prefixWord ++ tailWord_1476109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476109).length < 2 ^ (prefixWord ++ tailWord_1476109).sum := by decide
  have hdescent : baseEnd_1476109 < baseStart_1476109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476128 : List Nat := [2, 1, 1, 6, 1, 1, 2, 4, 5]
def baseStart_1476128 : Nat := 118140960795 + 1476128 * 2 ^ 59
def prefixEnd_1476128 : Nat := 4983230072969 + 3 ^ 40 * 1476128 * 2
def baseEnd_1476128 : Nat := 84218130173345097345713

theorem tailTrace_1476128 : CollatzResearch.WordTrace tailWord_1476128 prefixEnd_1476128 84218130173345097345713 := by
  unfold tailWord_1476128
  simp only [CollatzResearch.WordTrace]
  refine ⟨26919405598123916718298519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35892540797498555624398025 26919405598123916718298519)
  ·
    refine ⟨40379108397185875077447779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26919405598123916718298519 40379108397185875077447779)
    ·
      refine ⟨60568662595778812616171669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40379108397185875077447779 60568662595778812616171669)
      ·
        refine ⟨2839156059177131841383047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60568662595778812616171669 2839156059177131841383047)
        ·
          refine ⟨4258734088765697762074571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2839156059177131841383047 4258734088765697762074571)
          ·
            refine ⟨6388101133148546643111857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4258734088765697762074571 6388101133148546643111857)
            ·
              refine ⟨4791075849861409982333893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6388101133148546643111857 4791075849861409982333893)
              ·
                refine ⟨898326721849014371687605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4791075849861409982333893 898326721849014371687605)
                ·
                  refine ⟨84218130173345097345713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 898326721849014371687605 84218130173345097345713)
                  ·
                    rfl

theorem cell23_1476128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4, 5].length) (baseStart_1476128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476128 prefixEnd_1476128 := by exact prefixLift 1476128
  have htrace : WordTrace (prefixWord ++ tailWord_1476128) baseStart_1476128 baseEnd_1476128 := by
    simpa [prefixWord, tailWord_1476128, baseEnd_1476128] using wordTrace_append hprefix tailTrace_1476128
  have hstable : (prefixWord ++ tailWord_1476128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476128).length < 2 ^ (prefixWord ++ tailWord_1476128).sum := by decide
  have hdescent : baseEnd_1476128 < baseStart_1476128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476154 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 2, 8]
def baseStart_1476154 : Nat := 118140960795 + 1476154 * 2 ^ 59
def prefixEnd_1476154 : Nat := 4983230072969 + 3 ^ 40 * 1476154 * 2
def baseEnd_1476154 : Nat := 252658840685707591462099

theorem tailTrace_1476154 : CollatzResearch.WordTrace tailWord_1476154 prefixEnd_1476154 252658840685707591462099 := by
  unfold tailWord_1476154
  simp only [CollatzResearch.WordTrace]
  refine ⟨13459939873538409969260879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35893172996102426584695677 13459939873538409969260879)
  ·
    refine ⟨20189909810307614953891319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13459939873538409969260879 20189909810307614953891319)
    ·
      refine ⟨30284864715461422430836979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20189909810307614953891319 30284864715461422430836979)
      ·
        refine ⟨45427297073192133646255469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30284864715461422430836979 45427297073192133646255469)
        ·
          refine ⟨17035236402447050117345801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45427297073192133646255469 17035236402447050117345801)
          ·
            refine ⟨12776427301835287588009351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17035236402447050117345801 12776427301835287588009351)
            ·
              refine ⟨19164640952752931382014027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12776427301835287588009351 19164640952752931382014027)
              ·
                refine ⟨28746961429129397073021041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19164640952752931382014027 28746961429129397073021041)
                ·
                  refine ⟨21560221071847047804765781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28746961429129397073021041 21560221071847047804765781)
                  ·
                    refine ⟨252658840685707591462099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21560221071847047804765781 252658840685707591462099)
                    ·
                      rfl

theorem cell23_1476154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_1476154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476154 prefixEnd_1476154 := by exact prefixLift 1476154
  have htrace : WordTrace (prefixWord ++ tailWord_1476154) baseStart_1476154 baseEnd_1476154 := by
    simpa [prefixWord, tailWord_1476154, baseEnd_1476154] using wordTrace_append hprefix tailTrace_1476154
  have hstable : (prefixWord ++ tailWord_1476154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476154).length < 2 ^ (prefixWord ++ tailWord_1476154).sum := by decide
  have hdescent : baseEnd_1476154 < baseStart_1476154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476161 : List Nat := [1, 2, 5, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_1476161 : Nat := 118140960795 + 1476161 * 2 ^ 59
def prefixEnd_1476161 : Nat := 4983230072969 + 3 ^ 40 * 1476161 * 2
def baseEnd_1476161 : Nat := 757980116421704246998765

theorem tailTrace_1476161 : CollatzResearch.WordTrace tailWord_1476161 prefixEnd_1476161 757980116421704246998765 := by
  unfold tailWord_1476161
  simp only [CollatzResearch.WordTrace]
  refine ⟨53840014805128280072548337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35893343203418853381698891 53840014805128280072548337)
  ·
    refine ⟨40380011103846210054411253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53840014805128280072548337 40380011103846210054411253)
    ·
      refine ⟨3785626040985582192601055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40380011103846210054411253 3785626040985582192601055)
      ·
        refine ⟨5678439061478373288901583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3785626040985582192601055 5678439061478373288901583)
        ·
          refine ⟨8517658592217559933352375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5678439061478373288901583 8517658592217559933352375)
          ·
            refine ⟨12776487888326339900028563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8517658592217559933352375 12776487888326339900028563)
            ·
              refine ⟨19164731832489509850042845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12776487888326339900028563 19164731832489509850042845)
              ·
                refine ⟨7186774437183566193766067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19164731832489509850042845 7186774437183566193766067)
                ·
                  refine ⟨10780161655775349290649101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7186774437183566193766067 10780161655775349290649101)
                  ·
                    refine ⟨4042560620915755983993413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10780161655775349290649101 4042560620915755983993413)
                    ·
                      refine ⟨757980116421704246998765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4042560620915755983993413 757980116421704246998765)
                      ·
                        rfl

theorem cell23_1476161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_1476161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476161 prefixEnd_1476161 := by exact prefixLift 1476161
  have htrace : WordTrace (prefixWord ++ tailWord_1476161) baseStart_1476161 baseEnd_1476161 := by
    simpa [prefixWord, tailWord_1476161, baseEnd_1476161] using wordTrace_append hprefix tailTrace_1476161
  have hstable : (prefixWord ++ tailWord_1476161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476161).length < 2 ^ (prefixWord ++ tailWord_1476161).sum := by decide
  have hdescent : baseEnd_1476161 < baseStart_1476161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476178 : List Nat := [3, 2, 2, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_1476178 : Nat := 118140960795 + 1476178 * 2 ^ 59
def prefixEnd_1476178 : Nat := 4983230072969 + 3 ^ 40 * 1476178 * 2
def baseEnd_1476178 : Nat := 757988845592830680486187

theorem tailTrace_1476178 : CollatzResearch.WordTrace tailWord_1476178 prefixEnd_1476178 757988845592830680486187 := by
  unfold tailWord_1476178
  simp only [CollatzResearch.WordTrace]
  refine ⟨13460158711516672993979297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35893756564044461317278125 13460158711516672993979297)
  ·
    refine ⟨10095119033637504745484473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13460158711516672993979297 10095119033637504745484473)
    ·
      refine ⟨7571339275228128559113355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10095119033637504745484473 7571339275228128559113355)
      ·
        refine ⟨11357008912842192838670033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7571339275228128559113355 11357008912842192838670033)
        ·
          refine ⟨8517756684631644629002525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11357008912842192838670033 8517756684631644629002525)
          ·
            refine ⟨3194158756736866735875947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8517756684631644629002525 3194158756736866735875947)
            ·
              refine ⟨4791238135105300103813921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3194158756736866735875947 4791238135105300103813921)
              ·
                refine ⟨3593428601328975077860441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4791238135105300103813921 3593428601328975077860441)
                ·
                  refine ⟨2695071450996731308395331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3593428601328975077860441 2695071450996731308395331)
                  ·
                    refine ⟨4042607176495096962592997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2695071450996731308395331 4042607176495096962592997)
                    ·
                      refine ⟨757988845592830680486187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4042607176495096962592997 757988845592830680486187)
                      ·
                        rfl

theorem cell23_1476178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_1476178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476178 prefixEnd_1476178 := by exact prefixLift 1476178
  have htrace : WordTrace (prefixWord ++ tailWord_1476178) baseStart_1476178 baseEnd_1476178 := by
    simpa [prefixWord, tailWord_1476178, baseEnd_1476178] using wordTrace_append hprefix tailTrace_1476178
  have hstable : (prefixWord ++ tailWord_1476178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476178).length < 2 ^ (prefixWord ++ tailWord_1476178).sum := by decide
  have hdescent : baseEnd_1476178 < baseStart_1476178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476261 : List Nat := [1, 3, 1, 2, 1, 2, 3, 3, 1, 6]
def baseStart_1476261 : Nat := 118140960795 + 1476261 * 2 ^ 59
def prefixEnd_1476261 : Nat := 4983230072969 + 3 ^ 40 * 1476261 * 2
def baseEnd_1476261 : Nat := 252677154829051285249435

theorem tailTrace_1476261 : CollatzResearch.WordTrace tailWord_1476261 prefixEnd_1476261 252677154829051285249435 := by
  unfold tailWord_1476261
  simp only [CollatzResearch.WordTrace]
  refine ⟨53843662104765997151188637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35895774736510664767459091 53843662104765997151188637)
  ·
    refine ⟨20191373289287248931695739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53843662104765997151188637 20191373289287248931695739)
    ·
      refine ⟨30287059933930873397543609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20191373289287248931695739 30287059933930873397543609)
      ·
        refine ⟨22715294950448155048157707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30287059933930873397543609 22715294950448155048157707)
        ·
          refine ⟨34072942425672232572236561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22715294950448155048157707 34072942425672232572236561)
          ·
            refine ⟨25554706819254174429177421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34072942425672232572236561 25554706819254174429177421)
            ·
              refine ⟨9583015057220315410941533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25554706819254174429177421 9583015057220315410941533)
              ·
                refine ⟨3593630646457618279103075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9583015057220315410941533 3593630646457618279103075)
                ·
                  refine ⟨5390445969686427418654613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3593630646457618279103075 5390445969686427418654613)
                  ·
                    refine ⟨252677154829051285249435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5390445969686427418654613 252677154829051285249435)
                    ·
                      rfl

theorem cell23_1476261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 6].length) (baseStart_1476261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476261 prefixEnd_1476261 := by exact prefixLift 1476261
  have htrace : WordTrace (prefixWord ++ tailWord_1476261) baseStart_1476261 baseEnd_1476261 := by
    simpa [prefixWord, tailWord_1476261, baseEnd_1476261] using wordTrace_append hprefix tailTrace_1476261
  have hstable : (prefixWord ++ tailWord_1476261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476261).length < 2 ^ (prefixWord ++ tailWord_1476261).sum := by decide
  have hdescent : baseEnd_1476261 < baseStart_1476261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476285 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 5, 2, 2]
def baseStart_1476285 : Nat := 118140960795 + 1476285 * 2 ^ 59
def prefixEnd_1476285 : Nat := 4983230072969 + 3 ^ 40 * 1476285 * 2
def baseEnd_1476285 : Nat := 758043788022861761848195

theorem tailTrace_1476285 : CollatzResearch.WordTrace tailWord_1476285 prefixEnd_1476285 758043788022861761848195 := by
  unfold tailWord_1476285
  simp only [CollatzResearch.WordTrace]
  refine ⟨53844537456679049250062309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35896358304452699500041539 53844537456679049250062309)
  ·
    refine ⟨10095850773127321734386683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53844537456679049250062309 10095850773127321734386683)
    ·
      refine ⟨15143776159690982601580025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10095850773127321734386683 15143776159690982601580025)
      ·
        refine ⟨11357832119768236951185019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15143776159690982601580025 11357832119768236951185019)
        ·
          refine ⟨17036748179652355426777529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11357832119768236951185019 17036748179652355426777529)
          ·
            refine ⟨12777561134739266570083147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17036748179652355426777529 12777561134739266570083147)
            ·
              refine ⟨19166341702108899855124721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12777561134739266570083147 19166341702108899855124721)
              ·
                refine ⟨14374756276581674891343541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19166341702108899855124721 14374756276581674891343541)
                ·
                  refine ⟨1347633400929532021063457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14374756276581674891343541 1347633400929532021063457)
                  ·
                    refine ⟨1010725050697149015797593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1347633400929532021063457 1010725050697149015797593)
                    ·
                      refine ⟨758043788022861761848195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1010725050697149015797593 758043788022861761848195)
                      ·
                        rfl

theorem cell23_1476285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_1476285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476285 prefixEnd_1476285 := by exact prefixLift 1476285
  have htrace : WordTrace (prefixWord ++ tailWord_1476285) baseStart_1476285 baseEnd_1476285 := by
    simpa [prefixWord, tailWord_1476285, baseEnd_1476285] using wordTrace_append hprefix tailTrace_1476285
  have hstable : (prefixWord ++ tailWord_1476285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476285).length < 2 ^ (prefixWord ++ tailWord_1476285).sum := by decide
  have hdescent : baseEnd_1476285 < baseStart_1476285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476302 : List Nat := [4, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2]
def baseStart_1476302 : Nat := 118140960795 + 1476302 * 2 ^ 59
def prefixEnd_1476302 : Nat := 4983230072969 + 3 ^ 40 * 1476302 * 2
def baseEnd_1476302 : Nat := 758052517193988195335617

theorem tailTrace_1476302 : CollatzResearch.WordTrace tailWord_1476302 prefixEnd_1476302 758052517193988195335617 := by
  unfold tailWord_1476302
  simp only [CollatzResearch.WordTrace]
  refine ⟨6730644687202182644178895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35896771665078307435620773 6730644687202182644178895)
  ·
    refine ⟨10095967030803273966268343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6730644687202182644178895 10095967030803273966268343)
    ·
      refine ⟨15143950546204910949402515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10095967030803273966268343 15143950546204910949402515)
      ·
        refine ⟨22715925819307366424103773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15143950546204910949402515 22715925819307366424103773)
        ·
          refine ⟨8518472182240262409038915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22715925819307366424103773 8518472182240262409038915)
          ·
            refine ⟨12777708273360393613558373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8518472182240262409038915 12777708273360393613558373)
            ·
              refine ⟨2395820301255073802542195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12777708273360393613558373 2395820301255073802542195)
              ·
                refine ⟨3593730451882610703813293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2395820301255073802542195 3593730451882610703813293)
                ·
                  refine ⟨1347648919455979013929985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3593730451882610703813293 1347648919455979013929985)
                  ·
                    refine ⟨1010736689591984260447489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1347648919455979013929985 1010736689591984260447489)
                    ·
                      refine ⟨758052517193988195335617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1010736689591984260447489 758052517193988195335617)
                      ·
                        rfl

theorem cell23_1476302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2].length) (baseStart_1476302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476302 prefixEnd_1476302 := by exact prefixLift 1476302
  have htrace : WordTrace (prefixWord ++ tailWord_1476302) baseStart_1476302 baseEnd_1476302 := by
    simpa [prefixWord, tailWord_1476302, baseEnd_1476302] using wordTrace_append hprefix tailTrace_1476302
  have hstable : (prefixWord ++ tailWord_1476302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476302).length < 2 ^ (prefixWord ++ tailWord_1476302).sum := by decide
  have hdescent : baseEnd_1476302 < baseStart_1476302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476331 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 5]
def baseStart_1476331 : Nat := 118140960795 + 1476331 * 2 ^ 59
def prefixEnd_1476331 : Nat := 4983230072969 + 3 ^ 40 * 1476331 * 2
def baseEnd_1476331 : Nat := 758067408132968581872983

theorem tailTrace_1476331 : CollatzResearch.WordTrace tailWord_1476331 prefixEnd_1476331 758067408132968581872983 := by
  unfold tailWord_1476331
  simp only [CollatzResearch.WordTrace]
  refine ⟨53846215214512399106236847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35897476809674932737491231 53846215214512399106236847)
  ·
    refine ⟨80769322821768598659355271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53846215214512399106236847 80769322821768598659355271)
    ·
      refine ⟨121153984232652897989032907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80769322821768598659355271 121153984232652897989032907)
      ·
        refine ⟨181730976348979346983549361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121153984232652897989032907 181730976348979346983549361)
        ·
          refine ⟨136298232261734510237662021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181730976348979346983549361 136298232261734510237662021)
          ·
            refine ⟨25555918549075220669561629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136298232261734510237662021 25555918549075220669561629)
            ·
              refine ⟨9583469455903207751085611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25555918549075220669561629 9583469455903207751085611)
              ·
                refine ⟨14375204183854811626628417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9583469455903207751085611 14375204183854811626628417)
                ·
                  refine ⟨10781403137891108719971313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14375204183854811626628417 10781403137891108719971313)
                  ·
                    refine ⟨8086052353418331539978485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10781403137891108719971313 8086052353418331539978485)
                    ·
                      refine ⟨758067408132968581872983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8086052353418331539978485 758067408132968581872983)
                      ·
                        rfl

theorem cell23_1476331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 5].length) (baseStart_1476331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476331 prefixEnd_1476331 := by exact prefixLift 1476331
  have htrace : WordTrace (prefixWord ++ tailWord_1476331) baseStart_1476331 baseEnd_1476331 := by
    simpa [prefixWord, tailWord_1476331, baseEnd_1476331] using wordTrace_append hprefix tailTrace_1476331
  have hstable : (prefixWord ++ tailWord_1476331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476331).length < 2 ^ (prefixWord ++ tailWord_1476331).sum := by decide
  have hdescent : baseEnd_1476331 < baseStart_1476331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476351 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 4, 6]
def baseStart_1476351 : Nat := 118140960795 + 1476351 * 2 ^ 59
def prefixEnd_1476351 : Nat := 4983230072969 + 3 ^ 40 * 1476351 * 2
def baseEnd_1476351 : Nat := 252692559248686167874297

theorem tailTrace_1476351 : CollatzResearch.WordTrace tailWord_1476351 prefixEnd_1476351 252692559248686167874297 := by
  unfold tailWord_1476351
  simp only [CollatzResearch.WordTrace]
  refine ⟨53846944674439942521964907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35897963116293295014643271 53846944674439942521964907)
  ·
    refine ⟨80770417011659913782947361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53846944674439942521964907 80770417011659913782947361)
    ·
      refine ⟨60577812758744935337210521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80770417011659913782947361 60577812758744935337210521)
      ·
        refine ⟨45433359569058701502907891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60577812758744935337210521 45433359569058701502907891)
        ·
          refine ⟨68150039353588052254361837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45433359569058701502907891 68150039353588052254361837)
          ·
            refine ⟨25556264757595519595385689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68150039353588052254361837 25556264757595519595385689)
            ·
              refine ⟨19167198568196639696539267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25556264757595519595385689 19167198568196639696539267)
              ·
                refine ⟨28750797852294959544808901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19167198568196639696539267 28750797852294959544808901)
                ·
                  refine ⟨5390774597305304914651669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28750797852294959544808901 5390774597305304914651669)
                  ·
                    refine ⟨252692559248686167874297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5390774597305304914651669 252692559248686167874297)
                    ·
                      rfl

theorem cell23_1476351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 6].length) (baseStart_1476351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476351 prefixEnd_1476351 := by exact prefixLift 1476351
  have htrace : WordTrace (prefixWord ++ tailWord_1476351) baseStart_1476351 baseEnd_1476351 := by
    simpa [prefixWord, tailWord_1476351, baseEnd_1476351] using wordTrace_append hprefix tailTrace_1476351
  have hstable : (prefixWord ++ tailWord_1476351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476351).length < 2 ^ (prefixWord ++ tailWord_1476351).sum := by decide
  have hdescent : baseEnd_1476351 < baseStart_1476351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476361 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 3, 3, 5]
def baseStart_1476361 : Nat := 118140960795 + 1476361 * 2 ^ 59
def prefixEnd_1476361 : Nat := 4983230072969 + 3 ^ 40 * 1476361 * 2
def baseEnd_1476361 : Nat := 758082812552603464497845

theorem tailTrace_1476361 : CollatzResearch.WordTrace tailWord_1476361 prefixEnd_1476361 758082812552603464497845 := by
  unfold tailWord_1476361
  simp only [CollatzResearch.WordTrace]
  refine ⟨53847309404403714229828937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35898206269602476153219291 53847309404403714229828937)
  ·
    refine ⟨40385482053302785672371703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53847309404403714229828937 40385482053302785672371703)
    ·
      refine ⟨60578223079954178508557555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40385482053302785672371703 60578223079954178508557555)
      ·
        refine ⟨90867334619931267762836333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60578223079954178508557555 90867334619931267762836333)
        ·
          refine ⟨34075250482474225411063625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90867334619931267762836333 34075250482474225411063625)
          ·
            refine ⟨25556437861855669058297719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34075250482474225411063625 25556437861855669058297719)
            ·
              refine ⟨38334656792783503587446579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25556437861855669058297719 38334656792783503587446579)
              ·
                refine ⟨57501985189175255381169869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38334656792783503587446579 57501985189175255381169869)
                ·
                  refine ⟨21563244445940720767938701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57501985189175255381169869 21563244445940720767938701)
                  ·
                    refine ⟨8086216667227770287977013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21563244445940720767938701 8086216667227770287977013)
                    ·
                      refine ⟨758082812552603464497845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8086216667227770287977013 758082812552603464497845)
                      ·
                        rfl

theorem cell23_1476361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 3, 5].length) (baseStart_1476361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476361 prefixEnd_1476361 := by exact prefixLift 1476361
  have htrace : WordTrace (prefixWord ++ tailWord_1476361) baseStart_1476361 baseEnd_1476361 := by
    simpa [prefixWord, tailWord_1476361, baseEnd_1476361] using wordTrace_append hprefix tailTrace_1476361
  have hstable : (prefixWord ++ tailWord_1476361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476361).length < 2 ^ (prefixWord ++ tailWord_1476361).sum := by decide
  have hdescent : baseEnd_1476361 < baseStart_1476361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476378 : List Nat := [3, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5]
def baseStart_1476378 : Nat := 118140960795 + 1476378 * 2 ^ 59
def prefixEnd_1476378 : Nat := 4983230072969 + 3 ^ 40 * 1476378 * 2
def baseEnd_1476378 : Nat := 758091541723729897985267

theorem tailTrace_1476378 : CollatzResearch.WordTrace tailWord_1476378 prefixEnd_1476378 758091541723729897985267 := by
  unfold tailWord_1476378
  simp only [CollatzResearch.WordTrace]
  refine ⟨13461982361335531533299447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35898619630228084088798525 13461982361335531533299447)
  ·
    refine ⟨20192973542003297299949171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13461982361335531533299447 20192973542003297299949171)
    ·
      refine ⟨30289460313004945949923757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20192973542003297299949171 30289460313004945949923757)
      ·
        refine ⟨11358547617376854731221409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30289460313004945949923757 11358547617376854731221409)
        ·
          refine ⟨8518910713032641048416057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11358547617376854731221409 8518910713032641048416057)
          ·
            refine ⟨6389183034774480786312043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8518910713032641048416057 6389183034774480786312043)
            ·
              refine ⟨9583774552161721179468065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6389183034774480786312043 9583774552161721179468065)
              ·
                refine ⟨7187830914121290884601049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9583774552161721179468065 7187830914121290884601049)
                ·
                  refine ⟨5390873185590968163450787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7187830914121290884601049 5390873185590968163450787)
                  ·
                    refine ⟨8086309778386452245176181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5390873185590968163450787 8086309778386452245176181)
                    ·
                      refine ⟨758091541723729897985267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8086309778386452245176181 758091541723729897985267)
                      ·
                        rfl

theorem cell23_1476378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_1476378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476378 prefixEnd_1476378 := by exact prefixLift 1476378
  have htrace : WordTrace (prefixWord ++ tailWord_1476378) baseStart_1476378 baseEnd_1476378 := by
    simpa [prefixWord, tailWord_1476378, baseEnd_1476378] using wordTrace_append hprefix tailTrace_1476378
  have hstable : (prefixWord ++ tailWord_1476378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476378).length < 2 ^ (prefixWord ++ tailWord_1476378).sum := by decide
  have hdescent : baseEnd_1476378 < baseStart_1476378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476392 : List Nat := [2, 1, 5, 1, 1, 3, 1, 2, 1, 4, 2]
def baseStart_1476392 : Nat := 118140960795 + 1476392 * 2 ^ 59
def prefixEnd_1476392 : Nat := 4983230072969 + 3 ^ 40 * 1476392 * 2
def baseEnd_1476392 : Nat := 758098730452892843210203

theorem tailTrace_1476392 : CollatzResearch.WordTrace tailWord_1476392 prefixEnd_1476392 758098730452892843210203 := by
  unfold tailWord_1476392
  simp only [CollatzResearch.WordTrace]
  refine ⟨26924220033645703262103715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35898960044860937682804953 26924220033645703262103715)
  ·
    refine ⟨40386330050468554893155573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26924220033645703262103715 40386330050468554893155573)
    ·
      refine ⟨3786218442231427021233335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40386330050468554893155573 3786218442231427021233335)
      ·
        refine ⟨5679327663347140531850003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3786218442231427021233335 5679327663347140531850003)
        ·
          refine ⟨8518991495020710797775005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5679327663347140531850003 8518991495020710797775005)
          ·
            refine ⟨3194621810632766549165627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8518991495020710797775005 3194621810632766549165627)
            ·
              refine ⟨4791932715949149823748441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3194621810632766549165627 4791932715949149823748441)
              ·
                refine ⟨3593949536961862367811331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4791932715949149823748441 3593949536961862367811331)
                ·
                  refine ⟨5390924305442793551716997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3593949536961862367811331 5390924305442793551716997)
                  ·
                    refine ⟨1010798307270523790946937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5390924305442793551716997 1010798307270523790946937)
                    ·
                      refine ⟨758098730452892843210203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1010798307270523790946937 758098730452892843210203)
                      ·
                        rfl

theorem cell23_1476392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_1476392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476392 prefixEnd_1476392 := by exact prefixLift 1476392
  have htrace : WordTrace (prefixWord ++ tailWord_1476392) baseStart_1476392 baseEnd_1476392 := by
    simpa [prefixWord, tailWord_1476392, baseEnd_1476392] using wordTrace_append hprefix tailTrace_1476392
  have hstable : (prefixWord ++ tailWord_1476392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476392).length < 2 ^ (prefixWord ++ tailWord_1476392).sum := by decide
  have hdescent : baseEnd_1476392 < baseStart_1476392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476422 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_1476422 : Nat := 118140960795 + 1476422 * 2 ^ 59
def prefixEnd_1476422 : Nat := 4983230072969 + 3 ^ 40 * 1476422 * 2
def baseEnd_1476422 : Nat := 758114134872527725835065

theorem tailTrace_1476422 : CollatzResearch.WordTrace tailWord_1476422 prefixEnd_1476422 758114134872527725835065 := by
  unfold tailWord_1476422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1682797945536960051493735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35899689504788481098533013 1682797945536960051493735)
  ·
    refine ⟨2524196918305440077240603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1682797945536960051493735 2524196918305440077240603)
    ·
      refine ⟨3786295377458160115860905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2524196918305440077240603 3786295377458160115860905)
      ·
        refine ⟨2839721533093620086895679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3786295377458160115860905 2839721533093620086895679)
        ·
          refine ⟨4259582299640430130343519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2839721533093620086895679 4259582299640430130343519)
          ·
            refine ⟨6389373449460645195515279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4259582299640430130343519 6389373449460645195515279)
            ·
              refine ⟨9584060174190967793272919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6389373449460645195515279 9584060174190967793272919)
              ·
                refine ⟨14376090261286451689909379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9584060174190967793272919 14376090261286451689909379)
                ·
                  refine ⟨21564135391929677534864069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14376090261286451689909379 21564135391929677534864069)
                  ·
                    refine ⟨4043275385986814537787013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21564135391929677534864069 4043275385986814537787013)
                    ·
                      refine ⟨758114134872527725835065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4043275385986814537787013 758114134872527725835065)
                      ·
                        rfl

theorem cell23_1476422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_1476422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476422 prefixEnd_1476422 := by exact prefixLift 1476422
  have htrace : WordTrace (prefixWord ++ tailWord_1476422) baseStart_1476422 baseEnd_1476422 := by
    simpa [prefixWord, tailWord_1476422, baseEnd_1476422] using wordTrace_append hprefix tailTrace_1476422
  have hstable : (prefixWord ++ tailWord_1476422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476422).length < 2 ^ (prefixWord ++ tailWord_1476422).sum := by decide
  have hdescent : baseEnd_1476422 < baseStart_1476422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476465 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 4, 4, 2]
def baseStart_1476465 : Nat := 118140960795 + 1476465 * 2 ^ 59
def prefixEnd_1476465 : Nat := 4983230072969 + 3 ^ 40 * 1476465 * 2
def baseEnd_1476465 : Nat := 758136214540671057597367

theorem tailTrace_1476465 : CollatzResearch.WordTrace tailWord_1476465 prefixEnd_1476465 758136214540671057597367 := by
  unfold tailWord_1476465
  simp only [CollatzResearch.WordTrace]
  refine ⟨53851102596026939991614849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35900735064017959994409899 53851102596026939991614849)
  ·
    refine ⟨40388326947020204993711137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53851102596026939991614849 40388326947020204993711137)
    ·
      refine ⟨30291245210265153745283353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40388326947020204993711137 30291245210265153745283353)
      ·
        refine ⟨22718433907698865308962515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30291245210265153745283353 22718433907698865308962515)
        ·
          refine ⟨34077650861548297963443773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22718433907698865308962515 34077650861548297963443773)
          ·
            refine ⟨12779119073080611736291415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34077650861548297963443773 12779119073080611736291415)
            ·
              refine ⟨19168678609620917604437123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12779119073080611736291415 19168678609620917604437123)
              ·
                refine ⟨28753017914431376406655685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19168678609620917604437123 28753017914431376406655685)
                ·
                  refine ⟨5391190858955883076247941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28753017914431376406655685 5391190858955883076247941)
                  ·
                    refine ⟨1010848286054228076796489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5391190858955883076247941 1010848286054228076796489)
                    ·
                      refine ⟨758136214540671057597367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1010848286054228076796489 758136214540671057597367)
                      ·
                        rfl

theorem cell23_1476465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 4, 2].length) (baseStart_1476465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476465 prefixEnd_1476465 := by exact prefixLift 1476465
  have htrace : WordTrace (prefixWord ++ tailWord_1476465) baseStart_1476465 baseEnd_1476465 := by
    simpa [prefixWord, tailWord_1476465, baseEnd_1476465] using wordTrace_append hprefix tailTrace_1476465
  have hstable : (prefixWord ++ tailWord_1476465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476465).length < 2 ^ (prefixWord ++ tailWord_1476465).sum := by decide
  have hdescent : baseEnd_1476465 < baseStart_1476465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476509 : List Nat := [1, 4, 2, 1, 2, 2, 3, 3, 1, 4]
def baseStart_1476509 : Nat := 118140960795 + 1476509 * 2 ^ 59
def prefixEnd_1476509 : Nat := 4983230072969 + 3 ^ 40 * 1476509 * 2
def baseEnd_1476509 : Nat := 252719602563156295149055

theorem tailTrace_1476509 : CollatzResearch.WordTrace tailWord_1476509 prefixEnd_1476509 252719602563156295149055 := by
  unfold tailWord_1476509
  simp only [CollatzResearch.WordTrace]
  refine ⟨53852707407867535506216581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35901804938578357004144387 53852707407867535506216581)
  ·
    refine ⟨10097382638975162907415609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53852707407867535506216581 10097382638975162907415609)
    ·
      refine ⟨7573036979231372180561707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10097382638975162907415609 7573036979231372180561707)
      ·
        refine ⟨11359555468847058270842561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7573036979231372180561707 11359555468847058270842561)
        ·
          refine ⟨8519666601635293703131921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11359555468847058270842561 8519666601635293703131921)
          ·
            refine ⟨6389749951226470277348941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8519666601635293703131921 6389749951226470277348941)
            ·
              refine ⟨2396156231709926354005853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6389749951226470277348941 2396156231709926354005853)
              ·
                refine ⟨898558586891222382752195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2396156231709926354005853 898558586891222382752195)
                ·
                  refine ⟨1347837880336833574128293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 898558586891222382752195 1347837880336833574128293)
                  ·
                    refine ⟨252719602563156295149055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1347837880336833574128293 252719602563156295149055)
                    ·
                      rfl

theorem cell23_1476509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_1476509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476509 prefixEnd_1476509 := by exact prefixLift 1476509
  have htrace : WordTrace (prefixWord ++ tailWord_1476509) baseStart_1476509 baseEnd_1476509 := by
    simpa [prefixWord, tailWord_1476509, baseEnd_1476509] using wordTrace_append hprefix tailTrace_1476509
  have hstable : (prefixWord ++ tailWord_1476509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476509).length < 2 ^ (prefixWord ++ tailWord_1476509).sum := by decide
  have hdescent : baseEnd_1476509 < baseStart_1476509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476552 : List Nat := [2, 1, 3, 1, 4, 1, 3, 2, 1, 5]
def baseStart_1476552 : Nat := 118140960795 + 1476552 * 2 ^ 59
def prefixEnd_1476552 : Nat := 4983230072969 + 3 ^ 40 * 1476552 * 2
def baseEnd_1476552 : Nat := 252726962452537405736489

theorem tailTrace_1476552 : CollatzResearch.WordTrace tailWord_1476552 prefixEnd_1476552 252726962452537405736489 := by
  unfold tailWord_1476552
  simp only [CollatzResearch.WordTrace]
  refine ⟨26927137873355876925015955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35902850497807835900021273 26927137873355876925015955)
  ·
    refine ⟨40390706810033815387523933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26927137873355876925015955 40390706810033815387523933)
    ·
      refine ⟨15146515053762680770321475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40390706810033815387523933 15146515053762680770321475)
      ·
        refine ⟨22719772580644021155482213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15146515053762680770321475 22719772580644021155482213)
        ·
          refine ⟨4259957358870753966652915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22719772580644021155482213 4259957358870753966652915)
          ·
            refine ⟨6389936038306130949979373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4259957358870753966652915 6389936038306130949979373)
            ·
              refine ⟨2396226014364799106242265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6389936038306130949979373 2396226014364799106242265)
              ·
                refine ⟨1797169510773599329681699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2396226014364799106242265 1797169510773599329681699)
                ·
                  refine ⟨2695754266160398994522549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1797169510773599329681699 2695754266160398994522549)
                  ·
                    refine ⟨252726962452537405736489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2695754266160398994522549 252726962452537405736489)
                    ·
                      rfl

theorem cell23_1476552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_1476552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476552 prefixEnd_1476552 := by exact prefixLift 1476552
  have htrace : WordTrace (prefixWord ++ tailWord_1476552) baseStart_1476552 baseEnd_1476552 := by
    simpa [prefixWord, tailWord_1476552, baseEnd_1476552] using wordTrace_append hprefix tailTrace_1476552
  have hstable : (prefixWord ++ tailWord_1476552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476552).length < 2 ^ (prefixWord ++ tailWord_1476552).sum := by decide
  have hdescent : baseEnd_1476552 < baseStart_1476552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476555 : List Nat := [1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 4]
def baseStart_1476555 : Nat := 118140960795 + 1476555 * 2 ^ 59
def prefixEnd_1476555 : Nat := 4983230072969 + 3 ^ 40 * 1476555 * 2
def baseEnd_1476555 : Nat := 758182427799575705471953

theorem tailTrace_1476555 : CollatzResearch.WordTrace tailWord_1476555 prefixEnd_1476555 758182427799575705471953 := by
  unfold tailWord_1476555
  simp only [CollatzResearch.WordTrace]
  refine ⟨53854385165700885362391119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35902923443800590241594079 53854385165700885362391119)
  ·
    refine ⟨80781577748551328043586679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53854385165700885362391119 80781577748551328043586679)
    ·
      refine ⟨121172366622826992065380019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80781577748551328043586679 121172366622826992065380019)
      ·
        refine ⟨181758549934240488098070029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121172366622826992065380019 181758549934240488098070029)
        ·
          refine ⟨68159456225340183036776261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181758549934240488098070029 68159456225340183036776261)
          ·
            refine ⟨12779898042251284319395549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68159456225340183036776261 12779898042251284319395549)
            ·
              refine ⟨4792461765844231619773331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12779898042251284319395549 4792461765844231619773331)
              ·
                refine ⟨7188692648766347429659997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4792461765844231619773331 7188692648766347429659997)
                ·
                  refine ⟨2695759743287380286122499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7188692648766347429659997 2695759743287380286122499)
                  ·
                    refine ⟨4043639614931070429183749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2695759743287380286122499 4043639614931070429183749)
                    ·
                      refine ⟨758182427799575705471953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4043639614931070429183749 758182427799575705471953)
                      ·
                        rfl

theorem cell23_1476555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 4].length) (baseStart_1476555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476555 prefixEnd_1476555 := by exact prefixLift 1476555
  have htrace : WordTrace (prefixWord ++ tailWord_1476555) baseStart_1476555 baseEnd_1476555 := by
    simpa [prefixWord, tailWord_1476555, baseEnd_1476555] using wordTrace_append hprefix tailTrace_1476555
  have hstable : (prefixWord ++ tailWord_1476555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476555).length < 2 ^ (prefixWord ++ tailWord_1476555).sum := by decide
  have hdescent : baseEnd_1476555 < baseStart_1476555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476565 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 3, 6]
def baseStart_1476565 : Nat := 118140960795 + 1476565 * 2 ^ 59
def prefixEnd_1476565 : Nat := 4983230072969 + 3 ^ 40 * 1476565 * 2
def baseEnd_1476565 : Nat := 252729187535373555448969

theorem tailTrace_1476565 : CollatzResearch.WordTrace tailWord_1476565 prefixEnd_1476565 252729187535373555448969 := by
  unfold tailWord_1476565
  simp only [CollatzResearch.WordTrace]
  refine ⟨53854749895664657070255149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35903166597109771380170099 53854749895664657070255149)
  ·
    refine ⟨20195531210874246401345681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53854749895664657070255149 20195531210874246401345681)
    ·
      refine ⟨15146648408155684801009261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20195531210874246401345681 15146648408155684801009261)
      ·
        refine ⟨5679993153058381800378473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15146648408155684801009261 5679993153058381800378473)
        ·
          refine ⟨4259994864793786350283855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5679993153058381800378473 4259994864793786350283855)
          ·
            refine ⟨6389992297190679525425783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4259994864793786350283855 6389992297190679525425783)
            ·
              refine ⟨9584988445786019288138675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6389992297190679525425783 9584988445786019288138675)
              ·
                refine ⟨14377482668679028932208013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9584988445786019288138675 14377482668679028932208013)
                ·
                  refine ⟨5391556000754635849578005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14377482668679028932208013 5391556000754635849578005)
                  ·
                    refine ⟨252729187535373555448969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5391556000754635849578005 252729187535373555448969)
                    ·
                      rfl

theorem cell23_1476565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_1476565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476565 prefixEnd_1476565 := by exact prefixLift 1476565
  have htrace : WordTrace (prefixWord ++ tailWord_1476565) baseStart_1476565 baseEnd_1476565 := by
    simpa [prefixWord, tailWord_1476565, baseEnd_1476565] using wordTrace_append hprefix tailTrace_1476565
  have hstable : (prefixWord ++ tailWord_1476565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476565).length < 2 ^ (prefixWord ++ tailWord_1476565).sum := by decide
  have hdescent : baseEnd_1476565 < baseStart_1476565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476569 : List Nat := [1, 2, 1, 2, 6, 1, 3, 1, 1, 5]
def baseStart_1476569 : Nat := 118140960795 + 1476569 * 2 ^ 59
def prefixEnd_1476569 : Nat := 4983230072969 + 3 ^ 40 * 1476569 * 2
def baseEnd_1476569 : Nat := 252729872176246216898963

theorem tailTrace_1476569 : CollatzResearch.WordTrace tailWord_1476569 prefixEnd_1476569 252729872176246216898963 := by
  unfold tailWord_1476569
  simp only [CollatzResearch.WordTrace]
  refine ⟨53854895787650165753400761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35903263858433443835600507 53854895787650165753400761)
  ·
    refine ⟨40391171840737624315050571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53854895787650165753400761 40391171840737624315050571)
    ·
      refine ⟨60586757761106436472575857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40391171840737624315050571 60586757761106436472575857)
      ·
        refine ⟨45440068320829827354431893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60586757761106436472575857 45440068320829827354431893)
        ·
          refine ⟨2130003202538898157238995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45440068320829827354431893 2130003202538898157238995)
          ·
            refine ⟨3195004803808347235858493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2130003202538898157238995 3195004803808347235858493)
            ·
              refine ⟨1198126801428130213446935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3195004803808347235858493 1198126801428130213446935)
              ·
                refine ⟨1797190202142195320170403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1198126801428130213446935 1797190202142195320170403)
                ·
                  refine ⟨2695785303213292980255605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1797190202142195320170403 2695785303213292980255605)
                  ·
                    refine ⟨252729872176246216898963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2695785303213292980255605 252729872176246216898963)
                    ·
                      rfl

theorem cell23_1476569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 1, 5].length) (baseStart_1476569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476569 prefixEnd_1476569 := by exact prefixLift 1476569
  have htrace : WordTrace (prefixWord ++ tailWord_1476569) baseStart_1476569 baseEnd_1476569 := by
    simpa [prefixWord, tailWord_1476569, baseEnd_1476569] using wordTrace_append hprefix tailTrace_1476569
  have hstable : (prefixWord ++ tailWord_1476569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476569).length < 2 ^ (prefixWord ++ tailWord_1476569).sum := by decide
  have hdescent : baseEnd_1476569 < baseStart_1476569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476606 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 5, 2, 2]
def baseStart_1476606 : Nat := 118140960795 + 1476606 * 2 ^ 59
def prefixEnd_1476606 : Nat := 4983230072969 + 3 ^ 40 * 1476606 * 2
def baseEnd_1476606 : Nat := 758208615312955005934219

theorem tailTrace_1476606 : CollatzResearch.WordTrace tailWord_1476606 prefixEnd_1476606 758208615312955005934219 := by
  unfold tailWord_1476606
  simp only [CollatzResearch.WordTrace]
  refine ⟨6732030661064515134062209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35904163525677414048331781 6732030661064515134062209)
  ·
    refine ⟨5049022995798386350546657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6732030661064515134062209 5049022995798386350546657)
    ·
      refine ⟨3786767246848789762909993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5049022995798386350546657 3786767246848789762909993)
      ·
        refine ⟨2840075435136592322182495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3786767246848789762909993 2840075435136592322182495)
        ·
          refine ⟨4260113152704888483273743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2840075435136592322182495 4260113152704888483273743)
          ·
            refine ⟨6390169729057332724910615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4260113152704888483273743 6390169729057332724910615)
            ·
              refine ⟨9585254593585999087365923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6390169729057332724910615 9585254593585999087365923)
              ·
                refine ⟨14377881890378998631048885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9585254593585999087365923 14377881890378998631048885)
                ·
                  refine ⟨1347926427223031121660833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14377881890378998631048885 1347926427223031121660833)
                  ·
                    refine ⟨1010944820417273341245625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1347926427223031121660833 1010944820417273341245625)
                    ·
                      refine ⟨758208615312955005934219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1010944820417273341245625 758208615312955005934219)
                      ·
                        rfl

theorem cell23_1476606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_1476606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476606 prefixEnd_1476606 := by exact prefixLift 1476606
  have htrace : WordTrace (prefixWord ++ tailWord_1476606) baseStart_1476606 baseEnd_1476606 := by
    simpa [prefixWord, tailWord_1476606, baseEnd_1476606] using wordTrace_append hprefix tailTrace_1476606
  have hstable : (prefixWord ++ tailWord_1476606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476606).length < 2 ^ (prefixWord ++ tailWord_1476606).sum := by decide
  have hdescent : baseEnd_1476606 < baseStart_1476606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476622 : List Nat := [4, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3]
def baseStart_1476622 : Nat := 118140960795 + 1476622 * 2 ^ 59
def prefixEnd_1476622 : Nat := 4983230072969 + 3 ^ 40 * 1476622 * 2
def baseEnd_1476622 : Nat := 758216831003426943334145

theorem tailTrace_1476622 : CollatzResearch.WordTrace tailWord_1476622 prefixEnd_1476622 758216831003426943334145 := by
  unfold tailWord_1476622
  simp only [CollatzResearch.WordTrace]
  refine ⟨6732103607057269475635015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35904552570972103870053413 6732103607057269475635015)
  ·
    refine ⟨10098155410585904213452523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6732103607057269475635015 10098155410585904213452523)
    ·
      refine ⟨15147233115878856320178785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10098155410585904213452523 15147233115878856320178785)
      ·
        refine ⟨11360424836909142240134089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15147233115878856320178785 11360424836909142240134089)
        ·
          refine ⟨8520318627681856680100567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11360424836909142240134089 8520318627681856680100567)
          ·
            refine ⟨12780477941522785020150851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8520318627681856680100567 12780477941522785020150851)
            ·
              refine ⟨19170716912284177530226277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12780477941522785020150851 19170716912284177530226277)
              ·
                refine ⟨3594509421053283286917427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19170716912284177530226277 3594509421053283286917427)
                ·
                  refine ⟨5391764131579924930376141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3594509421053283286917427 5391764131579924930376141)
                  ·
                    refine ⟨2021911549342471848891053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5391764131579924930376141 2021911549342471848891053)
                    ·
                      refine ⟨758216831003426943334145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2021911549342471848891053 758216831003426943334145)
                      ·
                        rfl

theorem cell23_1476622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_1476622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476622 prefixEnd_1476622 := by exact prefixLift 1476622
  have htrace : WordTrace (prefixWord ++ tailWord_1476622) baseStart_1476622 baseEnd_1476622 := by
    simpa [prefixWord, tailWord_1476622, baseEnd_1476622] using wordTrace_append hprefix tailTrace_1476622
  have hstable : (prefixWord ++ tailWord_1476622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476622).length < 2 ^ (prefixWord ++ tailWord_1476622).sum := by decide
  have hdescent : baseEnd_1476622 < baseStart_1476622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476656 : List Nat := [2, 1, 1, 1, 2, 6, 3, 1, 2, 1, 3]
def baseStart_1476656 : Nat := 118140960795 + 1476656 * 2 ^ 59
def prefixEnd_1476656 : Nat := 4983230072969 + 3 ^ 40 * 1476656 * 2
def baseEnd_1476656 : Nat := 758234289345679810308989

theorem tailTrace_1476656 : CollatzResearch.WordTrace tailWord_1476656 prefixEnd_1476656 758234289345679810308989 := by
  unfold tailWord_1476656
  simp only [CollatzResearch.WordTrace]
  refine ⟨26929034469167489805908911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35905379292223319741211881 26929034469167489805908911)
  ·
    refine ⟨40393551703751234708863367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26929034469167489805908911 40393551703751234708863367)
    ·
      refine ⟨60590327555626852063295051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40393551703751234708863367 60590327555626852063295051)
      ·
        refine ⟨90885491333440278094942577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60590327555626852063295051 90885491333440278094942577)
        ·
          refine ⟨68164118500080208571206933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90885491333440278094942577 68164118500080208571206933)
          ·
            refine ⟨3195193054691259776775325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68164118500080208571206933 3195193054691259776775325)
            ·
              refine ⟨1198197395509222416290747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3195193054691259776775325 1198197395509222416290747)
              ·
                refine ⟨1797296093263833624436121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1198197395509222416290747 1797296093263833624436121)
                ·
                  refine ⟨1347972069947875218327091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1797296093263833624436121 1347972069947875218327091)
                  ·
                    refine ⟨2021958104921812827490637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1347972069947875218327091 2021958104921812827490637)
                    ·
                      refine ⟨758234289345679810308989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2021958104921812827490637 758234289345679810308989)
                      ·
                        rfl

theorem cell23_1476656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 2, 1, 3].length) (baseStart_1476656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476656 prefixEnd_1476656 := by exact prefixLift 1476656
  have htrace : WordTrace (prefixWord ++ tailWord_1476656) baseStart_1476656 baseEnd_1476656 := by
    simpa [prefixWord, tailWord_1476656, baseEnd_1476656] using wordTrace_append hprefix tailTrace_1476656
  have hstable : (prefixWord ++ tailWord_1476656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476656).length < 2 ^ (prefixWord ++ tailWord_1476656).sum := by decide
  have hdescent : baseEnd_1476656 < baseStart_1476656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476675 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 4]
def baseStart_1476675 : Nat := 118140960795 + 1476675 * 2 ^ 59
def prefixEnd_1476675 : Nat := 4983230072969 + 3 ^ 40 * 1476675 * 2
def baseEnd_1476675 : Nat := 758244045478115235971401

theorem tailTrace_1476675 : CollatzResearch.WordTrace tailWord_1476675 prefixEnd_1476675 758244045478115235971401 := by
  unfold tailWord_1476675
  simp only [CollatzResearch.WordTrace]
  refine ⟨53858761925266145856759479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35905841283510763904506319 53858761925266145856759479)
  ·
    refine ⟨80788142887899218785139219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53858761925266145856759479 80788142887899218785139219)
    ·
      refine ⟨121182214331848828177708829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80788142887899218785139219 121182214331848828177708829)
      ·
        refine ⟨45443330374443310566640811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121182214331848828177708829 45443330374443310566640811)
        ·
          refine ⟨68164995561664965849961217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45443330374443310566640811 68164995561664965849961217)
          ·
            refine ⟨51123746671248724387470913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68164995561664965849961217 51123746671248724387470913)
            ·
              refine ⟨38342810003436543290603185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51123746671248724387470913 38342810003436543290603185)
              ·
                refine ⟨28757107502577407467952389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38342810003436543290603185 28757107502577407467952389)
                ·
                  refine ⟨5391957656733263900241073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28757107502577407467952389 5391957656733263900241073)
                  ·
                    refine ⟨4043968242549947925180805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5391957656733263900241073 4043968242549947925180805)
                    ·
                      refine ⟨758244045478115235971401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4043968242549947925180805 758244045478115235971401)
                      ·
                        rfl

theorem cell23_1476675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_1476675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476675 prefixEnd_1476675 := by exact prefixLift 1476675
  have htrace : WordTrace (prefixWord ++ tailWord_1476675) baseStart_1476675 baseEnd_1476675 := by
    simpa [prefixWord, tailWord_1476675, baseEnd_1476675] using wordTrace_append hprefix tailTrace_1476675
  have hstable : (prefixWord ++ tailWord_1476675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476675).length < 2 ^ (prefixWord ++ tailWord_1476675).sum := by decide
  have hdescent : baseEnd_1476675 < baseStart_1476675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476679 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 6, 2, 2]
def baseStart_1476679 : Nat := 118140960795 + 1476679 * 2 ^ 59
def prefixEnd_1476679 : Nat := 4983230072969 + 3 ^ 40 * 1476679 * 2
def baseEnd_1476679 : Nat := 758246099400733220321383

theorem tailTrace_1476679 : CollatzResearch.WordTrace tailWord_1476679 prefixEnd_1476679 758246099400733220321383 := by
  unfold tailWord_1476679
  simp only [CollatzResearch.WordTrace]
  refine ⟨53858907817251654539905091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35905938544834436359936727 53858907817251654539905091)
  ·
    refine ⟨80788361725877481809857637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53858907817251654539905091 80788361725877481809857637)
    ·
      refine ⟨15147817823602027839348307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80788361725877481809857637 15147817823602027839348307)
      ·
        refine ⟨22721726735403041759022461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15147817823602027839348307 22721726735403041759022461)
        ·
          refine ⟨8520647525776140659633423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22721726735403041759022461 8520647525776140659633423)
          ·
            refine ⟨12780971288664210989450135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8520647525776140659633423 12780971288664210989450135)
            ·
              refine ⟨19171456932996316484175203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12780971288664210989450135 19171456932996316484175203)
              ·
                refine ⟨28757185399494474726262805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19171456932996316484175203 28757185399494474726262805)
                ·
                  refine ⟨1347993065601303502793569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28757185399494474726262805 1347993065601303502793569)
                  ·
                    refine ⟨1010994799200977627095177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1347993065601303502793569 1010994799200977627095177)
                    ·
                      refine ⟨758246099400733220321383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1010994799200977627095177 758246099400733220321383)
                      ·
                        rfl

theorem cell23_1476679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6, 2, 2].length) (baseStart_1476679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476679 prefixEnd_1476679 := by exact prefixLift 1476679
  have htrace : WordTrace (prefixWord ++ tailWord_1476679) baseStart_1476679 baseEnd_1476679 := by
    simpa [prefixWord, tailWord_1476679, baseEnd_1476679] using wordTrace_append hprefix tailTrace_1476679
  have hstable : (prefixWord ++ tailWord_1476679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476679).length < 2 ^ (prefixWord ++ tailWord_1476679).sum := by decide
  have hdescent : baseEnd_1476679 < baseStart_1476679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476732 : List Nat := [2, 2, 2, 1, 1, 4, 1, 3, 2, 5]
def baseStart_1476732 : Nat := 118140960795 + 1476732 * 2 ^ 59
def prefixEnd_1476732 : Nat := 4983230072969 + 3 ^ 40 * 1476732 * 2
def baseEnd_1476732 : Nat := 252757771291807170986213

theorem tailTrace_1476732 : CollatzResearch.WordTrace tailWord_1476732 prefixEnd_1476732 252757771291807170986213 := by
  unfold tailWord_1476732
  simp only [CollatzResearch.WordTrace]
  refine ⟨26930420443029822295792225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35907227257373096394389633 26930420443029822295792225)
  ·
    refine ⟨20197815332272366721844169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26930420443029822295792225 20197815332272366721844169)
    ·
      refine ⟨15148361499204275041383127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20197815332272366721844169 15148361499204275041383127)
      ·
        refine ⟨22722542248806412562074691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15148361499204275041383127 22722542248806412562074691)
        ·
          refine ⟨34083813373209618843112037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22722542248806412562074691 34083813373209618843112037)
          ·
            refine ⟨6390715007476803533083507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34083813373209618843112037 6390715007476803533083507)
            ·
              refine ⟨9586072511215205299625261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6390715007476803533083507 9586072511215205299625261)
              ·
                refine ⟨3594777191705701987359473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9586072511215205299625261 3594777191705701987359473)
                ·
                  refine ⟨2696082893779276490519605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3594777191705701987359473 2696082893779276490519605)
                  ·
                    refine ⟨252757771291807170986213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2696082893779276490519605 252757771291807170986213)
                    ·
                      rfl

theorem cell23_1476732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_1476732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476732 prefixEnd_1476732 := by exact prefixLift 1476732
  have htrace : WordTrace (prefixWord ++ tailWord_1476732) baseStart_1476732 baseEnd_1476732 := by
    simpa [prefixWord, tailWord_1476732, baseEnd_1476732] using wordTrace_append hprefix tailTrace_1476732
  have hstable : (prefixWord ++ tailWord_1476732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476732).length < 2 ^ (prefixWord ++ tailWord_1476732).sum := by decide
  have hdescent : baseEnd_1476732 < baseStart_1476732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476752 : List Nat := [2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 4]
def baseStart_1476752 : Nat := 118140960795 + 1476752 * 2 ^ 59
def prefixEnd_1476752 : Nat := 4983230072969 + 3 ^ 40 * 1476752 * 2
def baseEnd_1476752 : Nat := 758283583488511434708547

theorem tailTrace_1476752 : CollatzResearch.WordTrace tailWord_1476752 prefixEnd_1476752 758283583488511434708547 := by
  unfold tailWord_1476752
  simp only [CollatzResearch.WordTrace]
  refine ⟨26930785172993594003656255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35907713563991458671541673 26930785172993594003656255)
  ·
    refine ⟨40396177759490391005484383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26930785172993594003656255 40396177759490391005484383)
    ·
      refine ⟨60594266639235586508226575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40396177759490391005484383 60594266639235586508226575)
      ·
        refine ⟨90891399958853379762339863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60594266639235586508226575 90891399958853379762339863)
        ·
          refine ⟨136337099938280069643509795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90891399958853379762339863 136337099938280069643509795)
          ·
            refine ⟨204505649907420104465264693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136337099938280069643509795 204505649907420104465264693)
            ·
              refine ⟨19172404678820634793618565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 204505649907420104465264693 19172404678820634793618565)
              ·
                refine ⟨3594825877278869023803481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19172404678820634793618565 3594825877278869023803481)
                ·
                  refine ⟨2696119407959151767852611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3594825877278869023803481 2696119407959151767852611)
                  ·
                    refine ⟨4044179111938727651778917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2696119407959151767852611 4044179111938727651778917)
                    ·
                      refine ⟨758283583488511434708547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4044179111938727651778917 758283583488511434708547)
                      ·
                        rfl

theorem cell23_1476752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 4].length) (baseStart_1476752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476752 prefixEnd_1476752 := by exact prefixLift 1476752
  have htrace : WordTrace (prefixWord ++ tailWord_1476752) baseStart_1476752 baseEnd_1476752 := by
    simpa [prefixWord, tailWord_1476752, baseEnd_1476752] using wordTrace_append hprefix tailTrace_1476752
  have hstable : (prefixWord ++ tailWord_1476752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476752).length < 2 ^ (prefixWord ++ tailWord_1476752).sum := by decide
  have hdescent : baseEnd_1476752 < baseStart_1476752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476755 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 5]
def baseStart_1476755 : Nat := 118140960795 + 1476755 * 2 ^ 59
def prefixEnd_1476755 : Nat := 4983230072969 + 3 ^ 40 * 1476755 * 2
def baseEnd_1476755 : Nat := 758285123930474922971033

theorem tailTrace_1476755 : CollatzResearch.WordTrace tailWord_1476755 prefixEnd_1476755 758285123930474922971033 := by
  unfold tailWord_1476755
  simp only [CollatzResearch.WordTrace]
  refine ⟨53861679764976319519671719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35907786509984213013114479 53861679764976319519671719)
  ·
    refine ⟨80792519647464479279507579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53861679764976319519671719 80792519647464479279507579)
    ·
      refine ⟨121188779471196718919261369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80792519647464479279507579 121188779471196718919261369)
      ·
        refine ⟨90891584603397539189446027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121188779471196718919261369 90891584603397539189446027)
        ·
          refine ⟨136337376905096308784169041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90891584603397539189446027 136337376905096308784169041)
          ·
            refine ⟨102253032678822231588126781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136337376905096308784169041 102253032678822231588126781)
            ·
              refine ⟨38344887254558336845547543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102253032678822231588126781 38344887254558336845547543)
              ·
                refine ⟨57517330881837505268321315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38344887254558336845547543 57517330881837505268321315)
                ·
                  refine ⟨86275996322756257902481973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57517330881837505268321315 86275996322756257902481973)
                  ·
                    refine ⟨8088374655258399178357685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86275996322756257902481973 8088374655258399178357685)
                    ·
                      refine ⟨758285123930474922971033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8088374655258399178357685 758285123930474922971033)
                      ·
                        rfl

theorem cell23_1476755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 5].length) (baseStart_1476755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476755 prefixEnd_1476755 := by exact prefixLift 1476755
  have htrace : WordTrace (prefixWord ++ tailWord_1476755) baseStart_1476755 baseEnd_1476755 := by
    simpa [prefixWord, tailWord_1476755, baseEnd_1476755] using wordTrace_append hprefix tailTrace_1476755
  have hstable : (prefixWord ++ tailWord_1476755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476755).length < 2 ^ (prefixWord ++ tailWord_1476755).sum := by decide
  have hdescent : baseEnd_1476755 < baseStart_1476755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476769 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 1, 6, 2]
def baseStart_1476769 : Nat := 118140960795 + 1476769 * 2 ^ 59
def prefixEnd_1476769 : Nat := 4983230072969 + 3 ^ 40 * 1476769 * 2
def baseEnd_1476769 : Nat := 758292312659637868195969

theorem tailTrace_1476769 : CollatzResearch.WordTrace tailWord_1476769 prefixEnd_1476769 758292312659637868195969 := by
  unfold tailWord_1476769
  simp only [CollatzResearch.WordTrace]
  refine ⟨53862190386925599910681361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35908126924617066607120907 53862190386925599910681361)
  ·
    refine ⟨40396642790194199933011021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53862190386925599910681361 40396642790194199933011021)
    ·
      refine ⟨15148741046322824974879133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40396642790194199933011021 15148741046322824974879133)
      ·
        refine ⟨5680777892371059365579675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15148741046322824974879133 5680777892371059365579675)
        ·
          refine ⟨8521166838556589048369513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5680777892371059365579675 8521166838556589048369513)
          ·
            refine ⟨6390875128917441786277135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8521166838556589048369513 6390875128917441786277135)
            ·
              refine ⟨9586312693376162679415703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6390875128917441786277135 9586312693376162679415703)
              ·
                refine ⟨14379469040064244019123555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9586312693376162679415703 14379469040064244019123555)
                ·
                  refine ⟨21569203560096366028685333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14379469040064244019123555 21569203560096366028685333)
                  ·
                    refine ⟨1011056416879517157594625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21569203560096366028685333 1011056416879517157594625)
                    ·
                      refine ⟨758292312659637868195969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1011056416879517157594625 758292312659637868195969)
                      ·
                        rfl

theorem cell23_1476769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_1476769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476769 prefixEnd_1476769 := by exact prefixLift 1476769
  have htrace : WordTrace (prefixWord ++ tailWord_1476769) baseStart_1476769 baseEnd_1476769 := by
    simpa [prefixWord, tailWord_1476769, baseEnd_1476769] using wordTrace_append hprefix tailTrace_1476769
  have hstable : (prefixWord ++ tailWord_1476769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476769).length < 2 ^ (prefixWord ++ tailWord_1476769).sum := by decide
  have hdescent : baseEnd_1476769 < baseStart_1476769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476846 : List Nat := [4, 1, 2, 1, 1, 1, 1, 5, 2, 3, 2]
def baseStart_1476846 : Nat := 118140960795 + 1476846 * 2 ^ 59
def prefixEnd_1476846 : Nat := 4983230072969 + 3 ^ 40 * 1476846 * 2
def baseEnd_1476846 : Nat := 758331850670034066933115

theorem tailTrace_1476846 : CollatzResearch.WordTrace tailWord_1476846 prefixEnd_1476846 758331850670034066933115 := by
  unfold tailWord_1476846
  simp only [CollatzResearch.WordTrace]
  refine ⟨6733124850955830257654299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35909999205097761374156261 6733124850955830257654299)
  ·
    refine ⟨10099687276433745386481449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6733124850955830257654299 10099687276433745386481449)
    ·
      refine ⟨7574765457325309039861087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10099687276433745386481449 7574765457325309039861087)
      ·
        refine ⟨11362148185987963559791631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7574765457325309039861087 11362148185987963559791631)
        ·
          refine ⟨17043222278981945339687447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11362148185987963559791631 17043222278981945339687447)
          ·
            refine ⟨25564833418472918009531171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17043222278981945339687447 25564833418472918009531171)
            ·
              refine ⟨38347250127709377014296757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25564833418472918009531171 38347250127709377014296757)
              ·
                refine ⟨3595054699472754095090321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38347250127709377014296757 3595054699472754095090321)
                ·
                  refine ⟨2696291024604565571317741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3595054699472754095090321 2696291024604565571317741)
                  ·
                    refine ⟨1011109134226712089244153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2696291024604565571317741 1011109134226712089244153)
                    ·
                      refine ⟨758331850670034066933115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1011109134226712089244153 758331850670034066933115)
                      ·
                        rfl

theorem cell23_1476846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_1476846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476846 prefixEnd_1476846 := by exact prefixLift 1476846
  have htrace : WordTrace (prefixWord ++ tailWord_1476846) baseStart_1476846 baseEnd_1476846 := by
    simpa [prefixWord, tailWord_1476846, baseEnd_1476846] using wordTrace_append hprefix tailTrace_1476846
  have hstable : (prefixWord ++ tailWord_1476846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476846).length < 2 ^ (prefixWord ++ tailWord_1476846).sum := by decide
  have hdescent : baseEnd_1476846 < baseStart_1476846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476896 : List Nat := [2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 3]
def baseStart_1476896 : Nat := 118140960795 + 1476896 * 2 ^ 59
def prefixEnd_1476896 : Nat := 4983230072969 + 3 ^ 40 * 1476896 * 2
def baseEnd_1476896 : Nat := 758357524702758871307885

theorem tailTrace_1476896 : CollatzResearch.WordTrace tailWord_1476896 prefixEnd_1476896 758357524702758871307885 := by
  unfold tailWord_1476896
  simp only [CollatzResearch.WordTrace]
  refine ⟨26933411228732750300277271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35911214971643667067036361 26933411228732750300277271)
  ·
    refine ⟨40400116843099125450415907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26933411228732750300277271 40400116843099125450415907)
    ·
      refine ⟨60600175264648688175623861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40400116843099125450415907 60600175264648688175623861)
      ·
        refine ⟨5681266431060814516464737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60600175264648688175623861 5681266431060814516464737)
        ·
          refine ⟨4260949823295610887348553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5681266431060814516464737 4260949823295610887348553)
          ·
            refine ⟨3195712367471708165511415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4260949823295610887348553 3195712367471708165511415)
            ·
              refine ⟨4793568551207562248267123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3195712367471708165511415 4793568551207562248267123)
              ·
                refine ⟨7190352826811343372400685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4793568551207562248267123 7190352826811343372400685)
                ·
                  refine ⟨2696382310054253764650257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7190352826811343372400685 2696382310054253764650257)
                  ·
                    refine ⟨2022286732540690323487693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2696382310054253764650257 2022286732540690323487693)
                    ·
                      refine ⟨758357524702758871307885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2022286732540690323487693 758357524702758871307885)
                      ·
                        rfl

theorem cell23_1476896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_1476896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476896 prefixEnd_1476896 := by exact prefixLift 1476896
  have htrace : WordTrace (prefixWord ++ tailWord_1476896) baseStart_1476896 baseEnd_1476896 := by
    simpa [prefixWord, tailWord_1476896, baseEnd_1476896] using wordTrace_append hprefix tailTrace_1476896
  have hstable : (prefixWord ++ tailWord_1476896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476896).length < 2 ^ (prefixWord ++ tailWord_1476896).sum := by decide
  have hdescent : baseEnd_1476896 < baseStart_1476896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476913 : List Nat := [1, 2, 2, 3, 5, 1, 1, 1, 1, 1, 5]
def baseStart_1476913 : Nat := 118140960795 + 1476913 * 2 ^ 59
def prefixEnd_1476913 : Nat := 4983230072969 + 3 ^ 40 * 1476913 * 2
def baseEnd_1476913 : Nat := 758366253873885304795307

theorem tailTrace_1476913 : CollatzResearch.WordTrace tailWord_1476913 prefixEnd_1476913 758366253873885304795307 := by
  unfold tailWord_1476913
  simp only [CollatzResearch.WordTrace]
  refine ⟨53867442498403912503923393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35911628332269275002615595 53867442498403912503923393)
  ·
    refine ⟨40400581873802934377942545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53867442498403912503923393 40400581873802934377942545)
    ·
      refine ⟨30300436405352200783456909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40400581873802934377942545 30300436405352200783456909)
      ·
        refine ⟨11362663652007075293796341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30300436405352200783456909 11362663652007075293796341)
        ·
          refine ⟨1065249717375663308793407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11362663652007075293796341 1065249717375663308793407)
          ·
            refine ⟨1597874576063494963190111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1065249717375663308793407 1597874576063494963190111)
            ·
              refine ⟨2396811864095242444785167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1597874576063494963190111 2396811864095242444785167)
              ·
                refine ⟨3595217796142863667177751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2396811864095242444785167 3595217796142863667177751)
                ·
                  refine ⟨5392826694214295500766627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3595217796142863667177751 5392826694214295500766627)
                  ·
                    refine ⟨8089240041321443251149941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5392826694214295500766627 8089240041321443251149941)
                    ·
                      refine ⟨758366253873885304795307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8089240041321443251149941 758366253873885304795307)
                      ·
                        rfl

theorem cell23_1476913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_1476913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476913 prefixEnd_1476913 := by exact prefixLift 1476913
  have htrace : WordTrace (prefixWord ++ tailWord_1476913) baseStart_1476913 baseEnd_1476913 := by
    simpa [prefixWord, tailWord_1476913, baseEnd_1476913] using wordTrace_append hprefix tailTrace_1476913
  have hstable : (prefixWord ++ tailWord_1476913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476913).length < 2 ^ (prefixWord ++ tailWord_1476913).sum := by decide
  have hdescent : baseEnd_1476913 < baseStart_1476913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476936 : List Nat := [2, 1, 3, 1, 1, 2, 3, 2, 3, 3, 2]
def baseStart_1476936 : Nat := 118140960795 + 1476936 * 2 ^ 59
def prefixEnd_1476936 : Nat := 4983230072969 + 3 ^ 40 * 1476936 * 2
def baseEnd_1476936 : Nat := 758378063928938714807701

theorem tailTrace_1476936 : CollatzResearch.WordTrace tailWord_1476936 prefixEnd_1476936 758378063928938714807701 := by
  unfold tailWord_1476936
  simp only [CollatzResearch.WordTrace]
  refine ⟨26934140688660293716005331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35912187584880391621340441 26934140688660293716005331)
  ·
    refine ⟨40401211032990440574007997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26934140688660293716005331 40401211032990440574007997)
    ·
      refine ⟨15150454137371415215252999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40401211032990440574007997 15150454137371415215252999)
      ·
        refine ⟨22725681206057122822879499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15150454137371415215252999 22725681206057122822879499)
        ·
          refine ⟨34088521809085684234319249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22725681206057122822879499 34088521809085684234319249)
          ·
            refine ⟨25566391356814263175739437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34088521809085684234319249 25566391356814263175739437)
            ·
              refine ⟨9587396758805348690902289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25566391356814263175739437 9587396758805348690902289)
              ·
                refine ⟨7190547569104011518176717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9587396758805348690902289 7190547569104011518176717)
                ·
                  refine ⟨2696455338414004319316269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7190547569104011518176717 2696455338414004319316269)
                  ·
                    refine ⟨1011170751905251619743601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2696455338414004319316269 1011170751905251619743601)
                    ·
                      refine ⟨758378063928938714807701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1011170751905251619743601 758378063928938714807701)
                      ·
                        rfl

theorem cell23_1476936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 3, 3, 2].length) (baseStart_1476936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476936 prefixEnd_1476936 := by exact prefixLift 1476936
  have htrace : WordTrace (prefixWord ++ tailWord_1476936) baseStart_1476936 baseEnd_1476936 := by
    simpa [prefixWord, tailWord_1476936, baseEnd_1476936] using wordTrace_append hprefix tailTrace_1476936
  have hstable : (prefixWord ++ tailWord_1476936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476936).length < 2 ^ (prefixWord ++ tailWord_1476936).sum := by decide
  have hdescent : baseEnd_1476936 < baseStart_1476936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476970 : List Nat := [3, 1, 3, 3, 1, 2, 1, 3, 1, 3, 2]
def baseStart_1476970 : Nat := 118140960795 + 1476970 * 2 ^ 59
def prefixEnd_1476970 : Nat := 4983230072969 + 3 ^ 40 * 1476970 * 2
def baseEnd_1476970 : Nat := 758395522271191581782545

theorem tailTrace_1476970 : CollatzResearch.WordTrace tailWord_1476970 prefixEnd_1476970 758395522271191581782545 := by
  unfold tailWord_1476970
  simp only [CollatzResearch.WordTrace]
  refine ⟨13467380364799352809687091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35913014306131607492498909 13467380364799352809687091)
  ·
    refine ⟨20201070547199029214530637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13467380364799352809687091 20201070547199029214530637)
    ·
      refine ⟨7575401455199635955448989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20201070547199029214530637 7575401455199635955448989)
      ·
        refine ⟨2840775545699863483293371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7575401455199635955448989 2840775545699863483293371)
        ·
          refine ⟨4261163318549795224940057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2840775545699863483293371 4261163318549795224940057)
          ·
            refine ⟨3195872488912346418705043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4261163318549795224940057 3195872488912346418705043)
            ·
              refine ⟨4793808733368519628057565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3195872488912346418705043 4793808733368519628057565)
              ·
                refine ⟨1797678275013194860521587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4793808733368519628057565 1797678275013194860521587)
                ·
                  refine ⟨2696517412519792290782381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1797678275013194860521587 2696517412519792290782381)
                  ·
                    refine ⟨1011194029694922109043393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2696517412519792290782381 1011194029694922109043393)
                    ·
                      refine ⟨758395522271191581782545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1011194029694922109043393 758395522271191581782545)
                      ·
                        rfl

theorem cell23_1476970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_1476970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476970 prefixEnd_1476970 := by exact prefixLift 1476970
  have htrace : WordTrace (prefixWord ++ tailWord_1476970) baseStart_1476970 baseEnd_1476970 := by
    simpa [prefixWord, tailWord_1476970, baseEnd_1476970] using wordTrace_append hprefix tailTrace_1476970
  have hstable : (prefixWord ++ tailWord_1476970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476970).length < 2 ^ (prefixWord ++ tailWord_1476970).sum := by decide
  have hdescent : baseEnd_1476970 < baseStart_1476970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476983 : List Nat := [1, 1, 3, 1, 1, 2, 2, 6, 2, 2, 2]
def baseStart_1476983 : Nat := 118140960795 + 1476983 * 2 ^ 59
def prefixEnd_1476983 : Nat := 4983230072969 + 3 ^ 40 * 1476983 * 2
def baseEnd_1476983 : Nat := 758402197519700030919985

theorem tailTrace_1476983 : CollatzResearch.WordTrace tailWord_1476983 prefixEnd_1476983 758402197519700030919985 := by
  unfold tailWord_1476983
  simp only [CollatzResearch.WordTrace]
  refine ⟨53869995608150314458971603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35913330405433542972647735 53869995608150314458971603)
  ·
    refine ⟨80804993412225471688457405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53869995608150314458971603 80804993412225471688457405)
    ·
      refine ⟨30301872529584551883171527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80804993412225471688457405 30301872529584551883171527)
      ·
        refine ⟨45452808794376827824757291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30301872529584551883171527 45452808794376827824757291)
        ·
          refine ⟨68179213191565241737135937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45452808794376827824757291 68179213191565241737135937)
          ·
            refine ⟨51134409893673931302851953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68179213191565241737135937 51134409893673931302851953)
            ·
              refine ⟨38350807420255448477138965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51134409893673931302851953 38350807420255448477138965)
              ·
                refine ⟨1797694097824474147365889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38350807420255448477138965 1797694097824474147365889)
                ·
                  refine ⟨1348270573368355610524417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1797694097824474147365889 1348270573368355610524417)
                  ·
                    refine ⟨1011202930026266707893313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1348270573368355610524417 1011202930026266707893313)
                    ·
                      refine ⟨758402197519700030919985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1011202930026266707893313 758402197519700030919985)
                      ·
                        rfl

theorem cell23_1476983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2, 2, 2].length) (baseStart_1476983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476983 prefixEnd_1476983 := by exact prefixLift 1476983
  have htrace : WordTrace (prefixWord ++ tailWord_1476983) baseStart_1476983 baseEnd_1476983 := by
    simpa [prefixWord, tailWord_1476983, baseEnd_1476983] using wordTrace_append hprefix tailTrace_1476983
  have hstable : (prefixWord ++ tailWord_1476983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476983).length < 2 ^ (prefixWord ++ tailWord_1476983).sum := by decide
  have hdescent : baseEnd_1476983 < baseStart_1476983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476989 : List Nat := [1, 4, 1, 1, 2, 3, 1, 3, 7]
def baseStart_1476989 : Nat := 118140960795 + 1476989 * 2 ^ 59
def prefixEnd_1476989 : Nat := 4983230072969 + 3 ^ 40 * 1476989 * 2
def baseEnd_1476989 : Nat := 84267253155958556382773

theorem tailTrace_1476989 : CollatzResearch.WordTrace tailWord_1476989 prefixEnd_1476989 84267253155958556382773 := by
  unfold tailWord_1476989
  simp only [CollatzResearch.WordTrace]
  refine ⟨53870214446128577483690021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35913476297419051655793347 53870214446128577483690021)
  ·
    refine ⟨10100665208649108278191879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53870214446128577483690021 10100665208649108278191879)
    ·
      refine ⟨15150997812973662417287819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10100665208649108278191879 15150997812973662417287819)
      ·
        refine ⟨22726496719460493625931729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15150997812973662417287819 22726496719460493625931729)
        ·
          refine ⟨17044872539595370219448797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22726496719460493625931729 17044872539595370219448797)
          ·
            refine ⟨6391827202348263832293299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17044872539595370219448797 6391827202348263832293299)
            ·
              refine ⟨9587740803522395748439949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6391827202348263832293299 9587740803522395748439949)
              ·
                refine ⟨3595402801320898405664981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9587740803522395748439949 3595402801320898405664981)
                ·
                  refine ⟨84267253155958556382773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3595402801320898405664981 84267253155958556382773)
                  ·
                    rfl

theorem cell23_1476989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_1476989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476989 prefixEnd_1476989 := by exact prefixLift 1476989
  have htrace : WordTrace (prefixWord ++ tailWord_1476989) baseStart_1476989 baseEnd_1476989 := by
    simpa [prefixWord, tailWord_1476989, baseEnd_1476989] using wordTrace_append hprefix tailTrace_1476989
  have hstable : (prefixWord ++ tailWord_1476989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476989).length < 2 ^ (prefixWord ++ tailWord_1476989).sum := by decide
  have hdescent : baseEnd_1476989 < baseStart_1476989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1476994 : List Nat := [3, 4, 2, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_1476994 : Nat := 118140960795 + 1476994 * 2 ^ 59
def prefixEnd_1476994 : Nat := 4983230072969 + 3 ^ 40 * 1476994 * 2
def baseEnd_1476994 : Nat := 758407845806899487882435

theorem tailTrace_1476994 : CollatzResearch.WordTrace tailWord_1476994 prefixEnd_1476994 758407845806899487882435 := by
  unfold tailWord_1476994
  simp only [CollatzResearch.WordTrace]
  refine ⟨13467599202777615834405509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35913597874073642225081357 13467599202777615834405509)
  ·
    refine ⟨2525174850520802968951033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13467599202777615834405509 2525174850520802968951033)
    ·
      refine ⟨1893881137890602226713275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2525174850520802968951033 1893881137890602226713275)
      ·
        refine ⟨2840821706835903340069913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1893881137890602226713275 2840821706835903340069913)
        ·
          refine ⟨2130616280126927505052435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2840821706835903340069913 2130616280126927505052435)
          ·
            refine ⟨3195924420190391257578653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2130616280126927505052435 3195924420190391257578653)
            ·
              refine ⟨1198471657571396721591995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3195924420190391257578653 1198471657571396721591995)
              ·
                refine ⟨1797707486357095082387993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1198471657571396721591995 1797707486357095082387993)
                ·
                  refine ⟨1348280614767821311790995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1797707486357095082387993 1348280614767821311790995)
                  ·
                    refine ⟨2022420922151731967686493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1348280614767821311790995 2022420922151731967686493)
                    ·
                      refine ⟨758407845806899487882435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2022420922151731967686493 758407845806899487882435)
                      ·
                        rfl

theorem cell23_1476994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_1476994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1476994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1476994 prefixEnd_1476994 := by exact prefixLift 1476994
  have htrace : WordTrace (prefixWord ++ tailWord_1476994) baseStart_1476994 baseEnd_1476994 := by
    simpa [prefixWord, tailWord_1476994, baseEnd_1476994] using wordTrace_append hprefix tailTrace_1476994
  have hstable : (prefixWord ++ tailWord_1476994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1476994).length < 2 ^ (prefixWord ++ tailWord_1476994).sum := by decide
  have hdescent : baseEnd_1476994 < baseStart_1476994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1476994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477006 : List Nat := [4, 1, 1, 4, 1, 1, 2, 2, 7]
def baseStart_1477006 : Nat := 118140960795 + 1477006 * 2 ^ 59
def prefixEnd_1477006 : Nat := 4983230072969 + 3 ^ 40 * 1477006 * 2
def baseEnd_1477006 : Nat := 84268223063861493436931

theorem tailTrace_1477006 : CollatzResearch.WordTrace tailWord_1477006 prefixEnd_1477006 84268223063861493436931 := by
  unfold tailWord_1477006
  simp only [CollatzResearch.WordTrace]
  refine ⟨6733854310883373673382359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35913889658044659591372581 6733854310883373673382359)
  ·
    refine ⟨10100781466325060510073539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6733854310883373673382359 10100781466325060510073539)
    ·
      refine ⟨15151172199487590765110309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10100781466325060510073539 15151172199487590765110309)
      ·
        refine ⟨2840844787403923268458183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15151172199487590765110309 2840844787403923268458183)
        ·
          refine ⟨4261267181105884902687275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2840844787403923268458183 4261267181105884902687275)
          ·
            refine ⟨6391900771658827354030913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4261267181105884902687275 6391900771658827354030913)
            ·
              refine ⟨4793925578744120515523185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6391900771658827354030913 4793925578744120515523185)
              ·
                refine ⟨3595444184058090386642389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4793925578744120515523185 3595444184058090386642389)
                ·
                  refine ⟨84268223063861493436931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3595444184058090386642389 84268223063861493436931)
                  ·
                    rfl

theorem cell23_1477006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_1477006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477006 prefixEnd_1477006 := by exact prefixLift 1477006
  have htrace : WordTrace (prefixWord ++ tailWord_1477006) baseStart_1477006 baseEnd_1477006 := by
    simpa [prefixWord, tailWord_1477006, baseEnd_1477006] using wordTrace_append hprefix tailTrace_1477006
  have hstable : (prefixWord ++ tailWord_1477006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477006).length < 2 ^ (prefixWord ++ tailWord_1477006).sum := by decide
  have hdescent : baseEnd_1477006 < baseStart_1477006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477029 : List Nat := [1, 3, 1, 2, 1, 1, 4, 2, 1, 2, 5]
def baseStart_1477029 : Nat := 118140960795 + 1477029 * 2 ^ 59
def prefixEnd_1477029 : Nat := 4983230072969 + 3 ^ 40 * 1477029 * 2
def baseEnd_1477029 : Nat := 758425817629806850944773

theorem tailTrace_1477029 : CollatzResearch.WordTrace tailWord_1477029 prefixEnd_1477029 758425817629806850944773 := by
  unfold tailWord_1477029
  simp only [CollatzResearch.WordTrace]
  refine ⟨53871673365983664315146141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35914448910655776210097427 53871673365983664315146141)
  ·
    refine ⟨20201877512243874118179803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53871673365983664315146141 20201877512243874118179803)
    ·
      refine ⟨30302816268365811177269705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20201877512243874118179803 30302816268365811177269705)
      ·
        refine ⟨22727112201274358382952279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30302816268365811177269705 22727112201274358382952279)
        ·
          refine ⟨34090668301911537574428419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22727112201274358382952279 34090668301911537574428419)
          ·
            refine ⟨51136002452867306361642629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34090668301911537574428419 51136002452867306361642629)
            ·
              refine ⟨9588000459912619942807993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51136002452867306361642629 9588000459912619942807993)
              ·
                refine ⟨7191000344934464957105995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9588000459912619942807993 7191000344934464957105995)
                ·
                  refine ⟨10786500517401697435658993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7191000344934464957105995 10786500517401697435658993)
                  ·
                    refine ⟨8089875388051273076744245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10786500517401697435658993 8089875388051273076744245)
                    ·
                      refine ⟨758425817629806850944773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8089875388051273076744245 758425817629806850944773)
                      ·
                        rfl

theorem cell23_1477029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_1477029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477029 prefixEnd_1477029 := by exact prefixLift 1477029
  have htrace : WordTrace (prefixWord ++ tailWord_1477029) baseStart_1477029 baseEnd_1477029 := by
    simpa [prefixWord, tailWord_1477029, baseEnd_1477029] using wordTrace_append hprefix tailTrace_1477029
  have hstable : (prefixWord ++ tailWord_1477029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477029).length < 2 ^ (prefixWord ++ tailWord_1477029).sum := by decide
  have hdescent : baseEnd_1477029 < baseStart_1477029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477056 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 1, 6, 2]
def baseStart_1477056 : Nat := 118140960795 + 1477056 * 2 ^ 59
def prefixEnd_1477056 : Nat := 4983230072969 + 3 ^ 40 * 1477056 * 2
def baseEnd_1477056 : Nat := 758439681607478245307149

theorem tailTrace_1477056 : CollatzResearch.WordTrace tailWord_1477056 prefixEnd_1477056 758439681607478245307149 := by
  unfold tailWord_1477056
  simp only [CollatzResearch.WordTrace]
  refine ⟨26936329068442923963189511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35915105424590565284252681 26936329068442923963189511)
  ·
    refine ⟨40404493602664385944784267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26936329068442923963189511 40404493602664385944784267)
    ·
      refine ⟨60606740403996578917176401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40404493602664385944784267 60606740403996578917176401)
      ·
        refine ⟨45455055302997434187882301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60606740403996578917176401 45455055302997434187882301)
        ·
          refine ⟨17045645738624037820455863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45455055302997434187882301 17045645738624037820455863)
          ·
            refine ⟨25568468607936056730683795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17045645738624037820455863 25568468607936056730683795)
            ·
              refine ⟨38352702911904085096025693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25568468607936056730683795 38352702911904085096025693)
              ·
                refine ⟨14382263591964031911009635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38352702911904085096025693 14382263591964031911009635)
                ·
                  refine ⟨21573395387946047866514453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14382263591964031911009635 21573395387946047866514453)
                  ·
                    refine ⟨1011252908809970993742865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21573395387946047866514453 1011252908809970993742865)
                    ·
                      refine ⟨758439681607478245307149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1011252908809970993742865 758439681607478245307149)
                      ·
                        rfl

theorem cell23_1477056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 1, 6, 2].length) (baseStart_1477056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477056 prefixEnd_1477056 := by exact prefixLift 1477056
  have htrace : WordTrace (prefixWord ++ tailWord_1477056) baseStart_1477056 baseEnd_1477056 := by
    simpa [prefixWord, tailWord_1477056, baseEnd_1477056] using wordTrace_append hprefix tailTrace_1477056
  have hstable : (prefixWord ++ tailWord_1477056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477056).length < 2 ^ (prefixWord ++ tailWord_1477056).sum := by decide
  have hdescent : baseEnd_1477056 < baseStart_1477056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477066 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 5, 4]
def baseStart_1477066 : Nat := 118140960795 + 1477066 * 2 ^ 59
def prefixEnd_1477066 : Nat := 4983230072969 + 3 ^ 40 * 1477066 * 2
def baseEnd_1477066 : Nat := 252814938804674402060701

theorem tailTrace_1477066 : CollatzResearch.WordTrace tailWord_1477066 prefixEnd_1477066 252814938804674402060701 := by
  unfold tailWord_1477066
  simp only [CollatzResearch.WordTrace]
  refine ⟨13468255716712404908560763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35915348577899746422828701 13468255716712404908560763)
  ·
    refine ⟨20202383575068607362841145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13468255716712404908560763 20202383575068607362841145)
    ·
      refine ⟨15151787681301455522130859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20202383575068607362841145 15151787681301455522130859)
      ·
        refine ⟨22727681521952183283196289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15151787681301455522130859 22727681521952183283196289)
        ·
          refine ⟨17045761141464137462397217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22727681521952183283196289 17045761141464137462397217)
          ·
            refine ⟨12784320856098103096797913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17045761141464137462397217 12784320856098103096797913)
            ·
              refine ⟨9588240642073577322598435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12784320856098103096797913 9588240642073577322598435)
              ·
                refine ⟨14382360963110365983897653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9588240642073577322598435 14382360963110365983897653)
                ·
                  refine ⟨1348346340291596810990405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14382360963110365983897653 1348346340291596810990405)
                  ·
                    refine ⟨252814938804674402060701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1348346340291596810990405 252814938804674402060701)
                    ·
                      rfl

theorem cell23_1477066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_1477066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477066 prefixEnd_1477066 := by exact prefixLift 1477066
  have htrace : WordTrace (prefixWord ++ tailWord_1477066) baseStart_1477066 baseEnd_1477066 := by
    simpa [prefixWord, tailWord_1477066, baseEnd_1477066] using wordTrace_append hprefix tailTrace_1477066
  have hstable : (prefixWord ++ tailWord_1477066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477066).length < 2 ^ (prefixWord ++ tailWord_1477066).sum := by decide
  have hdescent : baseEnd_1477066 < baseStart_1477066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477096 : List Nat := [2, 1, 4, 1, 1, 3, 1, 4, 6]
def baseStart_1477096 : Nat := 118140960795 + 1477096 * 2 ^ 59
def prefixEnd_1477096 : Nat := 4983230072969 + 3 ^ 40 * 1477096 * 2
def baseEnd_1477096 : Nat := 84273357870406454311885

theorem tailTrace_1477096 : CollatzResearch.WordTrace tailWord_1477096 prefixEnd_1477096 84273357870406454311885 := by
  unfold tailWord_1477096
  simp only [CollatzResearch.WordTrace]
  refine ⟨26937058528370467378917571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35916078037827289838556761 26937058528370467378917571)
  ·
    refine ⟨40405587792555701068376357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26937058528370467378917571 40405587792555701068376357)
    ·
      refine ⟨7576047711104193950320567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40405587792555701068376357 7576047711104193950320567)
      ·
        refine ⟨11364071566656290925480851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7576047711104193950320567 11364071566656290925480851)
        ·
          refine ⟨17046107349984436388221277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11364071566656290925480851 17046107349984436388221277)
          ·
            refine ⟨6392290256244163645582979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17046107349984436388221277 6392290256244163645582979)
            ·
              refine ⟨9588435384366245468374469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6392290256244163645582979 9588435384366245468374469)
              ·
                refine ⟨1797831634568671025320213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9588435384366245468374469 1797831634568671025320213)
                ·
                  refine ⟨84273357870406454311885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1797831634568671025320213 84273357870406454311885)
                  ·
                    rfl

theorem cell23_1477096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 6].length) (baseStart_1477096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477096 prefixEnd_1477096 := by exact prefixLift 1477096
  have htrace : WordTrace (prefixWord ++ tailWord_1477096) baseStart_1477096 baseEnd_1477096 := by
    simpa [prefixWord, tailWord_1477096, baseEnd_1477096] using wordTrace_append hprefix tailTrace_1477096
  have hstable : (prefixWord ++ tailWord_1477096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477096).length < 2 ^ (prefixWord ++ tailWord_1477096).sum := by decide
  have hdescent : baseEnd_1477096 < baseStart_1477096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477099 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 6]
def baseStart_1477099 : Nat := 118140960795 + 1477099 * 2 ^ 59
def prefixEnd_1477099 : Nat := 4983230072969 + 3 ^ 40 * 1477099 * 2
def baseEnd_1477099 : Nat := 758461761275621577069451

theorem tailTrace_1477099 : CollatzResearch.WordTrace tailWord_1477099 prefixEnd_1477099 758461761275621577069451 := by
  unfold tailWord_1477099
  simp only [CollatzResearch.WordTrace]
  refine ⟨53874226475730066270194351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35916150983820044180129567 53874226475730066270194351)
  ·
    refine ⟨80811339713595099405291527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53874226475730066270194351 80811339713595099405291527)
    ·
      refine ⟨121217009570392649107937291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80811339713595099405291527 121217009570392649107937291)
      ·
        refine ⟨181825514355588973661905937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121217009570392649107937291 181825514355588973661905937)
        ·
          refine ⟨136369135766691730246429453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181825514355588973661905937 136369135766691730246429453)
          ·
            refine ⟨51138425912509398842411045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136369135766691730246429453 51138425912509398842411045)
            ·
              refine ⟨9588454858595512282952071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51138425912509398842411045 9588454858595512282952071)
              ·
                refine ⟨14382682287893268424428107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9588454858595512282952071 14382682287893268424428107)
                ·
                  refine ⟨21574023431839902636642161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14382682287893268424428107 21574023431839902636642161)
                  ·
                    refine ⟨16180517573879926977481621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21574023431839902636642161 16180517573879926977481621)
                    ·
                      refine ⟨758461761275621577069451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16180517573879926977481621 758461761275621577069451)
                      ·
                        rfl

theorem cell23_1477099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 6].length) (baseStart_1477099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477099 prefixEnd_1477099 := by exact prefixLift 1477099
  have htrace : WordTrace (prefixWord ++ tailWord_1477099) baseStart_1477099 baseEnd_1477099 := by
    simpa [prefixWord, tailWord_1477099, baseEnd_1477099] using wordTrace_append hprefix tailTrace_1477099
  have hstable : (prefixWord ++ tailWord_1477099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477099).length < 2 ^ (prefixWord ++ tailWord_1477099).sum := by decide
  have hdescent : baseEnd_1477099 < baseStart_1477099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477119 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 7]
def baseStart_1477119 : Nat := 118140960795 + 1477119 * 2 ^ 59
def prefixEnd_1477119 : Nat := 4983230072969 + 3 ^ 40 * 1477119 * 2
def baseEnd_1477119 : Nat := 758472030888711498819359

theorem tailTrace_1477119 : CollatzResearch.WordTrace tailWord_1477119 prefixEnd_1477119 758472030888711498819359 := by
  unfold tailWord_1477119
  simp only [CollatzResearch.WordTrace]
  refine ⟨53874955935657609685922411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35916637290438406457281607 53874955935657609685922411)
  ·
    refine ⟨80812433903486414528883617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53874955935657609685922411 80812433903486414528883617)
    ·
      refine ⟨60609325427614810896662713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80812433903486414528883617 60609325427614810896662713)
      ·
        refine ⟨45456994070711108172497035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60609325427614810896662713 45456994070711108172497035)
        ·
          refine ⟨68185491106066662258745553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45456994070711108172497035 68185491106066662258745553)
          ·
            refine ⟨51139118329549996694059165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68185491106066662258745553 51139118329549996694059165)
            ·
              refine ⟨19177169373581248760272187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51139118329549996694059165 19177169373581248760272187)
              ·
                refine ⟨28765754060371873140408281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19177169373581248760272187 28765754060371873140408281)
                ·
                  refine ⟨21574315545278904855306211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28765754060371873140408281 21574315545278904855306211)
                  ·
                    refine ⟨32361473317918357282959317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21574315545278904855306211 32361473317918357282959317)
                    ·
                      refine ⟨758472030888711498819359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 32361473317918357282959317 758472030888711498819359)
                      ·
                        rfl

theorem cell23_1477119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_1477119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477119 prefixEnd_1477119 := by exact prefixLift 1477119
  have htrace : WordTrace (prefixWord ++ tailWord_1477119) baseStart_1477119 baseEnd_1477119 := by
    simpa [prefixWord, tailWord_1477119, baseEnd_1477119] using wordTrace_append hprefix tailTrace_1477119
  have hstable : (prefixWord ++ tailWord_1477119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477119).length < 2 ^ (prefixWord ++ tailWord_1477119).sum := by decide
  have hdescent : baseEnd_1477119 < baseStart_1477119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477123 : List Nat := [1, 1, 1, 3, 2, 1, 5, 2, 3, 1, 3]
def baseStart_1477123 : Nat := 118140960795 + 1477123 * 2 ^ 59
def prefixEnd_1477123 : Nat := 4983230072969 + 3 ^ 40 * 1477123 * 2
def baseEnd_1477123 : Nat := 758474084811329483169341

theorem tailTrace_1477123 : CollatzResearch.WordTrace tailWord_1477123 prefixEnd_1477123 758474084811329483169341 := by
  unfold tailWord_1477123
  simp only [CollatzResearch.WordTrace]
  refine ⟨53875101827643118369068023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35916734551762078912712015 53875101827643118369068023)
  ·
    refine ⟨80812652741464677553602035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53875101827643118369068023 80812652741464677553602035)
    ·
      refine ⟨121218979112197016330403053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80812652741464677553602035 121218979112197016330403053)
      ·
        refine ⟨45457117167073881123901145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121218979112197016330403053 45457117167073881123901145)
        ·
          refine ⟨34092837875305410842925859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45457117167073881123901145 34092837875305410842925859)
          ·
            refine ⟨51139256812958116264388789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34092837875305410842925859 51139256812958116264388789)
            ·
              refine ⟨4794305326214823399786449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51139256812958116264388789 4794305326214823399786449)
              ·
                refine ⟨3595728994661117549839837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4794305326214823399786449 3595728994661117549839837)
                ·
                  refine ⟨1348398372997919081189939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3595728994661117549839837 1348398372997919081189939)
                  ·
                    refine ⟨2022597559496878621784909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1348398372997919081189939 2022597559496878621784909)
                    ·
                      refine ⟨758474084811329483169341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2022597559496878621784909 758474084811329483169341)
                      ·
                        rfl

theorem cell23_1477123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3, 1, 3].length) (baseStart_1477123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477123 prefixEnd_1477123 := by exact prefixLift 1477123
  have htrace : WordTrace (prefixWord ++ tailWord_1477123) baseStart_1477123 baseEnd_1477123 := by
    simpa [prefixWord, tailWord_1477123, baseEnd_1477123] using wordTrace_append hprefix tailTrace_1477123
  have hstable : (prefixWord ++ tailWord_1477123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477123).length < 2 ^ (prefixWord ++ tailWord_1477123).sum := by decide
  have hdescent : baseEnd_1477123 < baseStart_1477123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477127 : List Nat := [1, 1, 4, 3, 4, 1, 1, 1, 2, 2, 3]
def baseStart_1477127 : Nat := 118140960795 + 1477127 * 2 ^ 59
def prefixEnd_1477127 : Nat := 4983230072969 + 3 ^ 40 * 1477127 * 2
def baseEnd_1477127 : Nat := 758476138733947467519323

theorem tailTrace_1477127 : CollatzResearch.WordTrace tailWord_1477127 prefixEnd_1477127 758476138733947467519323 := by
  unfold tailWord_1477127
  simp only [CollatzResearch.WordTrace]
  refine ⟨53875247719628627052213635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35916831813085751368142423 53875247719628627052213635)
  ·
    refine ⟨80812871579442940578320453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53875247719628627052213635 80812871579442940578320453)
    ·
      refine ⟨15152413421145551358435085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80812871579442940578320453 15152413421145551358435085)
      ·
        refine ⟨5682155032929581759413157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15152413421145551358435085 5682155032929581759413157)
        ·
          refine ⟨1065404068674296579889967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5682155032929581759413157 1065404068674296579889967)
          ·
            refine ⟨1598106103011444869834951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1065404068674296579889967 1598106103011444869834951)
            ·
              refine ⟨2397159154517167304752427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1598106103011444869834951 2397159154517167304752427)
              ·
                refine ⟨3595738731775750957128641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2397159154517167304752427 3595738731775750957128641)
                ·
                  refine ⟨2696804048831813217846481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3595738731775750957128641 2696804048831813217846481)
                  ·
                    refine ⟨2022603036623859913384861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2696804048831813217846481 2022603036623859913384861)
                    ·
                      refine ⟨758476138733947467519323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2022603036623859913384861 758476138733947467519323)
                      ·
                        rfl

theorem cell23_1477127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_1477127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477127 prefixEnd_1477127 := by exact prefixLift 1477127
  have htrace : WordTrace (prefixWord ++ tailWord_1477127) baseStart_1477127 baseEnd_1477127 := by
    simpa [prefixWord, tailWord_1477127, baseEnd_1477127] using wordTrace_append hprefix tailTrace_1477127
  have hstable : (prefixWord ++ tailWord_1477127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477127).length < 2 ^ (prefixWord ++ tailWord_1477127).sum := by decide
  have hdescent : baseEnd_1477127 < baseStart_1477127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477176 : List Nat := [2, 1, 2, 1, 4, 1, 3, 1, 1, 1, 6]
def baseStart_1477176 : Nat := 118140960795 + 1477176 * 2 ^ 59
def prefixEnd_1477176 : Nat := 4983230072969 + 3 ^ 40 * 1477176 * 2
def baseEnd_1477176 : Nat := 758501299286017775806597

theorem tailTrace_1477176 : CollatzResearch.WordTrace tailWord_1477176 prefixEnd_1477176 758501299286017775806597 := by
  unfold tailWord_1477176
  simp only [CollatzResearch.WordTrace]
  refine ⟨26938517448225554210373691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35918023264300738947164921 26938517448225554210373691)
  ·
    refine ⟨40407776172338331315560537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26938517448225554210373691 40407776172338331315560537)
    ·
      refine ⟨30305832129253748486670403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40407776172338331315560537 30305832129253748486670403)
      ·
        refine ⟨45458748193880622730005605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30305832129253748486670403 45458748193880622730005605)
        ·
          refine ⟨8523515286352616761876051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45458748193880622730005605 8523515286352616761876051)
          ·
            refine ⟨12785272929528925142814077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8523515286352616761876051 12785272929528925142814077)
            ·
              refine ⟨4794477348573346928555279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12785272929528925142814077 4794477348573346928555279)
              ·
                refine ⟨7191716022860020392832919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4794477348573346928555279 7191716022860020392832919)
                ·
                  refine ⟨10787574034290030589249379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7191716022860020392832919 10787574034290030589249379)
                  ·
                    refine ⟨16181361051435045883874069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10787574034290030589249379 16181361051435045883874069)
                    ·
                      refine ⟨758501299286017775806597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16181361051435045883874069 758501299286017775806597)
                      ·
                        rfl

theorem cell23_1477176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_1477176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477176 prefixEnd_1477176 := by exact prefixLift 1477176
  have htrace : WordTrace (prefixWord ++ tailWord_1477176) baseStart_1477176 baseEnd_1477176 := by
    simpa [prefixWord, tailWord_1477176, baseEnd_1477176] using wordTrace_append hprefix tailTrace_1477176
  have hstable : (prefixWord ++ tailWord_1477176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477176).length < 2 ^ (prefixWord ++ tailWord_1477176).sum := by decide
  have hdescent : baseEnd_1477176 < baseStart_1477176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477180 : List Nat := [2, 2, 2, 2, 3, 2, 2, 2, 1, 1, 4]
def baseStart_1477180 : Nat := 118140960795 + 1477180 * 2 ^ 59
def prefixEnd_1477180 : Nat := 4983230072969 + 3 ^ 40 * 1477180 * 2
def baseEnd_1477180 : Nat := 758503353208635760156579

theorem tailTrace_1477180 : CollatzResearch.WordTrace tailWord_1477180 prefixEnd_1477180 758503353208635760156579 := by
  unfold tailWord_1477180
  simp only [CollatzResearch.WordTrace]
  refine ⟨26938590394218308551946497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35918120525624411402595329 26938590394218308551946497)
  ·
    refine ⟨20203942795663731413959873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26938590394218308551946497 20203942795663731413959873)
    ·
      refine ⟨15152957096747798560469905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20203942795663731413959873 15152957096747798560469905)
      ·
        refine ⟨11364717822560848920352429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15152957096747798560469905 11364717822560848920352429)
        ·
          refine ⟨4261769183460318345132161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11364717822560848920352429 4261769183460318345132161)
          ·
            refine ⟨3196326887595238758849121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4261769183460318345132161 3196326887595238758849121)
            ·
              refine ⟨2397245165696429069136841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3196326887595238758849121 2397245165696429069136841)
              ·
                refine ⟨1797933874272321801852631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2397245165696429069136841 1797933874272321801852631)
                ·
                  refine ⟨2696900811408482702778947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1797933874272321801852631 2696900811408482702778947)
                  ·
                    refine ⟨4045351217112724054168421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2696900811408482702778947 4045351217112724054168421)
                    ·
                      refine ⟨758503353208635760156579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4045351217112724054168421 758503353208635760156579)
                      ·
                        rfl

theorem cell23_1477180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_1477180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477180 prefixEnd_1477180 := by exact prefixLift 1477180
  have htrace : WordTrace (prefixWord ++ tailWord_1477180) baseStart_1477180 baseEnd_1477180 := by
    simpa [prefixWord, tailWord_1477180, baseEnd_1477180] using wordTrace_append hprefix tailTrace_1477180
  have hstable : (prefixWord ++ tailWord_1477180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477180).length < 2 ^ (prefixWord ++ tailWord_1477180).sum := by decide
  have hdescent : baseEnd_1477180 < baseStart_1477180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477223 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 2, 7, 2]
def baseStart_1477223 : Nat := 118140960795 + 1477223 * 2 ^ 59
def prefixEnd_1477223 : Nat := 4983230072969 + 3 ^ 40 * 1477223 * 2
def baseEnd_1477223 : Nat := 758525432876779091918881

theorem tailTrace_1477223 : CollatzResearch.WordTrace tailWord_1477223 prefixEnd_1477223 758525432876779091918881 := by
  unfold tailWord_1477223
  simp only [CollatzResearch.WordTrace]
  refine ⟨53878749127280835447708323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35919166084853890298472215 53878749127280835447708323)
  ·
    refine ⟨80818123690921253171562485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53878749127280835447708323 80818123690921253171562485)
    ·
      refine ⟨7576699096023867484833983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80818123690921253171562485 7576699096023867484833983)
      ·
        refine ⟨11365048644035801227250975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7576699096023867484833983 11365048644035801227250975)
        ·
          refine ⟨17047572966053701840876463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11365048644035801227250975 17047572966053701840876463)
          ·
            refine ⟨25571359449080552761314695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17047572966053701840876463 25571359449080552761314695)
            ·
              refine ⟨38357039173620829141972043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25571359449080552761314695 38357039173620829141972043)
              ·
                refine ⟨57535558760431243712958065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38357039173620829141972043 57535558760431243712958065)
                ·
                  refine ⟨43151669070323432784718549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57535558760431243712958065 43151669070323432784718549)
                  ·
                    refine ⟨1011367243835705455891841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43151669070323432784718549 1011367243835705455891841)
                    ·
                      refine ⟨758525432876779091918881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1011367243835705455891841 758525432876779091918881)
                      ·
                        rfl

theorem cell23_1477223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_1477223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477223 prefixEnd_1477223 := by exact prefixLift 1477223
  have htrace : WordTrace (prefixWord ++ tailWord_1477223) baseStart_1477223 baseEnd_1477223 := by
    simpa [prefixWord, tailWord_1477223, baseEnd_1477223] using wordTrace_append hprefix tailTrace_1477223
  have hstable : (prefixWord ++ tailWord_1477223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477223).length < 2 ^ (prefixWord ++ tailWord_1477223).sum := by decide
  have hdescent : baseEnd_1477223 < baseStart_1477223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477224 : List Nat := [2, 1, 4, 3, 2, 2, 2, 1, 2, 4]
def baseStart_1477224 : Nat := 118140960795 + 1477224 * 2 ^ 59
def prefixEnd_1477224 : Nat := 4983230072969 + 3 ^ 40 * 1477224 * 2
def baseEnd_1477224 : Nat := 252841982119144529335459

theorem tailTrace_1477224 : CollatzResearch.WordTrace tailWord_1477224 prefixEnd_1477224 252841982119144529335459 := by
  unfold tailWord_1477224
  simp only [CollatzResearch.WordTrace]
  refine ⟨26939392800138606309247363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35919190400184808412329817 26939392800138606309247363)
  ·
    refine ⟨40409089200207909463871045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26939392800138606309247363 40409089200207909463871045)
    ·
      refine ⟨7576704225038983024475821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40409089200207909463871045 7576704225038983024475821)
      ·
        refine ⟨2841264084389618634178433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7576704225038983024475821 2841264084389618634178433)
        ·
          refine ⟨2130948063292213975633825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2841264084389618634178433 2130948063292213975633825)
          ·
            refine ⟨1598211047469160481725369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2130948063292213975633825 1598211047469160481725369)
            ·
              refine ⟨1198658285601870361294027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1598211047469160481725369 1198658285601870361294027)
              ·
                refine ⟨1797987428402805541941041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1198658285601870361294027 1797987428402805541941041)
                ·
                  refine ⟨1348490571302104156455781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1797987428402805541941041 1348490571302104156455781)
                  ·
                    refine ⟨252841982119144529335459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1348490571302104156455781 252841982119144529335459)
                    ·
                      rfl

theorem cell23_1477224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_1477224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477224 prefixEnd_1477224 := by exact prefixLift 1477224
  have htrace : WordTrace (prefixWord ++ tailWord_1477224) baseStart_1477224 baseEnd_1477224 := by
    simpa [prefixWord, tailWord_1477224, baseEnd_1477224] using wordTrace_append hprefix tailTrace_1477224
  have hstable : (prefixWord ++ tailWord_1477224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477224).length < 2 ^ (prefixWord ++ tailWord_1477224).sum := by decide
  have hdescent : baseEnd_1477224 < baseStart_1477224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477234 : List Nat := [3, 2, 1, 2, 5, 1, 1, 2, 1, 2, 3]
def baseStart_1477234 : Nat := 118140960795 + 1477234 * 2 ^ 59
def prefixEnd_1477234 : Nat := 4983230072969 + 3 ^ 40 * 1477234 * 2
def baseEnd_1477234 : Nat := 758531081163978548881331

theorem tailTrace_1477234 : CollatzResearch.WordTrace tailWord_1477234 prefixEnd_1477234 758531081163978548881331 := by
  unfold tailWord_1477234
  simp only [CollatzResearch.WordTrace]
  refine ⟨13469787582560246081589689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35919433553493989550905837 13469787582560246081589689)
  ·
    refine ⟨10102340686920184561192267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13469787582560246081589689 10102340686920184561192267)
    ·
      refine ⟨15153511030380276841788401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10102340686920184561192267 15153511030380276841788401)
      ·
        refine ⟨11365133272785207631341301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15153511030380276841788401 11365133272785207631341301)
        ·
          refine ⟨1065481244323613215438247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11365133272785207631341301 1065481244323613215438247)
          ·
            refine ⟨1598221866485419823157371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1065481244323613215438247 1598221866485419823157371)
            ·
              refine ⟨2397332799728129734736057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1598221866485419823157371 2397332799728129734736057)
              ·
                refine ⟨1797999599796097301052043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2397332799728129734736057 1797999599796097301052043)
                ·
                  refine ⟨2696999399694145951578065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1797999599796097301052043 2696999399694145951578065)
                  ·
                    refine ⟨2022749549770609463683549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2696999399694145951578065 2022749549770609463683549)
                    ·
                      refine ⟨758531081163978548881331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2022749549770609463683549 758531081163978548881331)
                      ·
                        rfl

theorem cell23_1477234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_1477234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477234 prefixEnd_1477234 := by exact prefixLift 1477234
  have htrace : WordTrace (prefixWord ++ tailWord_1477234) baseStart_1477234 baseEnd_1477234 := by
    simpa [prefixWord, tailWord_1477234, baseEnd_1477234] using wordTrace_append hprefix tailTrace_1477234
  have hstable : (prefixWord ++ tailWord_1477234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477234).length < 2 ^ (prefixWord ++ tailWord_1477234).sum := by decide
  have hdescent : baseEnd_1477234 < baseStart_1477234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477293 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 9]
def baseStart_1477293 : Nat := 118140960795 + 1477293 * 2 ^ 59
def prefixEnd_1477293 : Nat := 4983230072969 + 3 ^ 40 * 1477293 * 2
def baseEnd_1477293 : Nat := 84284597391399313115951

theorem tailTrace_1477293 : CollatzResearch.WordTrace tailWord_1477293 prefixEnd_1477293 84284597391399313115951 := by
  unfold tailWord_1477293
  simp only [CollatzResearch.WordTrace]
  refine ⟨53881302237027237402756533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35920868158018158268504355 53881302237027237402756533)
  ·
    refine ⟨5051372084721303506508425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53881302237027237402756533 5051372084721303506508425)
    ·
      refine ⟨3788529063540977629881319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5051372084721303506508425 3788529063540977629881319)
      ·
        refine ⟨5682793595311466444821979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3788529063540977629881319 5682793595311466444821979)
        ·
          refine ⟨8524190392967199667232969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5682793595311466444821979 8524190392967199667232969)
          ·
            refine ⟨6393142794725399750424727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8524190392967199667232969 6393142794725399750424727)
            ·
              refine ⟨9589714192088099625637091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6393142794725399750424727 9589714192088099625637091)
              ·
                refine ⟨14384571288132149438455637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9589714192088099625637091 14384571288132149438455637)
                ·
                  refine ⟨84284597391399313115951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14384571288132149438455637 84284597391399313115951)
                  ·
                    rfl

theorem cell23_1477293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_1477293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477293 prefixEnd_1477293 := by exact prefixLift 1477293
  have htrace : WordTrace (prefixWord ++ tailWord_1477293) baseStart_1477293 baseEnd_1477293 := by
    simpa [prefixWord, tailWord_1477293, baseEnd_1477293] using wordTrace_append hprefix tailTrace_1477293
  have hstable : (prefixWord ++ tailWord_1477293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477293).length < 2 ^ (prefixWord ++ tailWord_1477293).sum := by decide
  have hdescent : baseEnd_1477293 < baseStart_1477293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477340 : List Nat := [2, 2, 5, 1, 1, 1, 1, 2, 1, 7]
def baseStart_1477340 : Nat := 118140960795 + 1477340 * 2 ^ 59
def prefixEnd_1477340 : Nat := 4983230072969 + 3 ^ 40 * 1477340 * 2
def baseEnd_1477340 : Nat := 252861836704451711385281

theorem tailTrace_1477340 : CollatzResearch.WordTrace tailWord_1477340 prefixEnd_1477340 252861836704451711385281 := by
  unfold tailWord_1477340
  simp only [CollatzResearch.WordTrace]
  refine ⟨26941508233928482214858737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35922010978571309619811649 26941508233928482214858737)
  ·
    refine ⟨20206131175446361661144053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26941508233928482214858737 20206131175446361661144053)
    ·
      refine ⟨1894324797698096405732255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20206131175446361661144053 1894324797698096405732255)
      ·
        refine ⟨2841487196547144608598383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1894324797698096405732255 2841487196547144608598383)
        ·
          refine ⟨4262230794820716912897575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2841487196547144608598383 4262230794820716912897575)
          ·
            refine ⟨6393346192231075369346363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4262230794820716912897575 6393346192231075369346363)
            ·
              refine ⟨9590019288346613054019545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6393346192231075369346363 9590019288346613054019545)
              ·
                refine ⟨7192514466259959790514659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9590019288346613054019545 7192514466259959790514659)
                ·
                  refine ⟨10788771699389939685771989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7192514466259959790514659 10788771699389939685771989)
                  ·
                    refine ⟨252861836704451711385281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10788771699389939685771989 252861836704451711385281)
                    ·
                      rfl

theorem cell23_1477340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_1477340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477340 prefixEnd_1477340 := by exact prefixLift 1477340
  have htrace : WordTrace (prefixWord ++ tailWord_1477340) baseStart_1477340 baseEnd_1477340 := by
    simpa [prefixWord, tailWord_1477340, baseEnd_1477340] using wordTrace_append hprefix tailTrace_1477340
  have hstable : (prefixWord ++ tailWord_1477340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477340).length < 2 ^ (prefixWord ++ tailWord_1477340).sum := by decide
  have hdescent : baseEnd_1477340 < baseStart_1477340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477343 : List Nat := [1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 4]
def baseStart_1477343 : Nat := 118140960795 + 1477343 * 2 ^ 59
def prefixEnd_1477343 : Nat := 4983230072969 + 3 ^ 40 * 1477343 * 2
def baseEnd_1477343 : Nat := 758587050555318622418329

theorem tailTrace_1477343 : CollatzResearch.WordTrace tailWord_1477343 prefixEnd_1477343 758587050555318622418329 := by
  unfold tailWord_1477343
  simp only [CollatzResearch.WordTrace]
  refine ⟨53883125886846095942076683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35922083924564063961384455 53883125886846095942076683)
  ·
    refine ⟨80824688830269143913115025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53883125886846095942076683 80824688830269143913115025)
    ·
      refine ⟨60618516622701857934836269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80824688830269143913115025 60618516622701857934836269)
      ·
        refine ⟨22731943733513196725563601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60618516622701857934836269 22731943733513196725563601)
        ·
          refine ⟨17048957800134897544172701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22731943733513196725563601 17048957800134897544172701)
          ·
            refine ⟨6393359175050586579064763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17048957800134897544172701 6393359175050586579064763)
            ·
              refine ⟨9590038762575879868597145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6393359175050586579064763 9590038762575879868597145)
              ·
                refine ⟨7192529071931909901447859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9590038762575879868597145 7192529071931909901447859)
                ·
                  refine ⟨10788793607897864852171789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7192529071931909901447859 10788793607897864852171789)
                  ·
                    refine ⟨4045797602961699319564421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10788793607897864852171789 4045797602961699319564421)
                    ·
                      refine ⟨758587050555318622418329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4045797602961699319564421 758587050555318622418329)
                      ·
                        rfl

theorem cell23_1477343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_1477343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477343 prefixEnd_1477343 := by exact prefixLift 1477343
  have htrace : WordTrace (prefixWord ++ tailWord_1477343) baseStart_1477343 baseEnd_1477343 := by
    simpa [prefixWord, tailWord_1477343, baseEnd_1477343] using wordTrace_append hprefix tailTrace_1477343
  have hstable : (prefixWord ++ tailWord_1477343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477343).length < 2 ^ (prefixWord ++ tailWord_1477343).sum := by decide
  have hdescent : baseEnd_1477343 < baseStart_1477343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477438 : List Nat := [4, 2, 1, 2, 3, 2, 2, 2, 1, 4]
def baseStart_1477438 : Nat := 118140960795 + 1477438 * 2 ^ 59
def prefixEnd_1477438 : Nat := 4983230072969 + 3 ^ 40 * 1477438 * 2
def baseEnd_1477438 : Nat := 252878610405831916910131

theorem tailTrace_1477438 : CollatzResearch.WordTrace tailWord_1477438 prefixEnd_1477438 252878610405831916910131 := by
  unfold tailWord_1477438
  simp only [CollatzResearch.WordTrace]
  refine ⟨6735823852687740895848121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35924393881001284777856645 6735823852687740895848121)
  ·
    refine ⟨5051867889515805671886091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6735823852687740895848121 5051867889515805671886091)
    ·
      refine ⟨7577801834273708507829137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5051867889515805671886091 7577801834273708507829137)
      ·
        refine ⟨5683351375705281380871853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7577801834273708507829137 5683351375705281380871853)
        ·
          refine ⟨2131256765889480517826945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5683351375705281380871853 2131256765889480517826945)
          ·
            refine ⟨1598442574417110388370209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2131256765889480517826945 1598442574417110388370209)
            ·
              refine ⟨1198831930812832791277657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1598442574417110388370209 1198831930812832791277657)
              ·
                refine ⟨899123948109624593458243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1198831930812832791277657 899123948109624593458243)
                ·
                  refine ⟨1348685922164436890187365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 899123948109624593458243 1348685922164436890187365)
                  ·
                    refine ⟨252878610405831916910131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1348685922164436890187365 252878610405831916910131)
                    ·
                      rfl

theorem cell23_1477438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_1477438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477438 prefixEnd_1477438 := by exact prefixLift 1477438
  have htrace : WordTrace (prefixWord ++ tailWord_1477438) baseStart_1477438 baseEnd_1477438 := by
    simpa [prefixWord, tailWord_1477438, baseEnd_1477438] using wordTrace_append hprefix tailTrace_1477438
  have hstable : (prefixWord ++ tailWord_1477438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477438).length < 2 ^ (prefixWord ++ tailWord_1477438).sum := by decide
  have hdescent : baseEnd_1477438 < baseStart_1477438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477443 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 3, 6]
def baseStart_1477443 : Nat := 118140960795 + 1477443 * 2 ^ 59
def prefixEnd_1477443 : Nat := 4983230072969 + 3 ^ 40 * 1477443 * 2
def baseEnd_1477443 : Nat := 252879466206922743722623

theorem tailTrace_1477443 : CollatzResearch.WordTrace tailWord_1477443 prefixEnd_1477443 252879466206922743722623 := by
  unfold tailWord_1477443
  simp only [CollatzResearch.WordTrace]
  refine ⟨53886773186483813020716983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35924515457655875347144655 53886773186483813020716983)
  ·
    refine ⟨80830159779725719531075475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53886773186483813020716983 80830159779725719531075475)
    ·
      refine ⟨121245239669588579296613213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80830159779725719531075475 121245239669588579296613213)
      ·
        refine ⟨45466964876095717236229955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121245239669588579296613213 45466964876095717236229955)
        ·
          refine ⟨68200447314143575854344933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45466964876095717236229955 68200447314143575854344933)
          ·
            refine ⟨12787583871401920472689675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68200447314143575854344933 12787583871401920472689675)
            ·
              refine ⟨19181375807102880709034513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12787583871401920472689675 19181375807102880709034513)
              ·
                refine ⟨14386031855327160531775885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19181375807102880709034513 14386031855327160531775885)
                ·
                  refine ⟨5394761945747685199415957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14386031855327160531775885 5394761945747685199415957)
                  ·
                    refine ⟨252879466206922743722623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5394761945747685199415957 252879466206922743722623)
                    ·
                      rfl

theorem cell23_1477443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 6].length) (baseStart_1477443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477443 prefixEnd_1477443 := by exact prefixLift 1477443
  have htrace : WordTrace (prefixWord ++ tailWord_1477443) baseStart_1477443 baseEnd_1477443 := by
    simpa [prefixWord, tailWord_1477443, baseEnd_1477443] using wordTrace_append hprefix tailTrace_1477443
  have hstable : (prefixWord ++ tailWord_1477443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477443).length < 2 ^ (prefixWord ++ tailWord_1477443).sum := by decide
  have hdescent : baseEnd_1477443 < baseStart_1477443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477494 : List Nat := [5, 1, 1, 3, 1, 2, 1, 1, 4, 4]
def baseStart_1477494 : Nat := 118140960795 + 1477494 * 2 ^ 59
def prefixEnd_1477494 : Nat := 4983230072969 + 3 ^ 40 * 1477494 * 2
def baseEnd_1477494 : Nat := 252888195378049177210045

theorem tailTrace_1477494 : CollatzResearch.WordTrace tailWord_1477494 prefixEnd_1477494 252888195378049177210045 := by
  unfold tailWord_1477494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3368039581831190545676471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35925755539532699153882357 3368039581831190545676471)
  ·
    refine ⟨5052059372746785818514707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3368039581831190545676471 5052059372746785818514707)
    ·
      refine ⟨7578089059120178727772061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5052059372746785818514707 7578089059120178727772061)
      ·
        refine ⟨2841783397170067022914523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7578089059120178727772061 2841783397170067022914523)
        ·
          refine ⟨4262675095755100534371785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2841783397170067022914523 4262675095755100534371785)
          ·
            refine ⟨3197006321816325400778839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4262675095755100534371785 3197006321816325400778839)
            ·
              refine ⟨4795509482724488101168259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3197006321816325400778839 4795509482724488101168259)
              ·
                refine ⟨7193264224086732151752389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4795509482724488101168259 7193264224086732151752389)
                ·
                  refine ⟨1348737042016262278453573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7193264224086732151752389 1348737042016262278453573)
                  ·
                    refine ⟨252888195378049177210045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1348737042016262278453573 252888195378049177210045)
                    ·
                      rfl

theorem cell23_1477494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_1477494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477494 prefixEnd_1477494 := by exact prefixLift 1477494
  have htrace : WordTrace (prefixWord ++ tailWord_1477494) baseStart_1477494 baseEnd_1477494 := by
    simpa [prefixWord, tailWord_1477494, baseEnd_1477494] using wordTrace_append hprefix tailTrace_1477494
  have hstable : (prefixWord ++ tailWord_1477494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477494).length < 2 ^ (prefixWord ++ tailWord_1477494).sum := by decide
  have hdescent : baseEnd_1477494 < baseStart_1477494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477500 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 3, 3, 3]
def baseStart_1477500 : Nat := 118140960795 + 1477500 * 2 ^ 59
def prefixEnd_1477500 : Nat := 4983230072969 + 3 ^ 40 * 1477500 * 2
def baseEnd_1477500 : Nat := 758667667018074508155107

theorem tailTrace_1477500 : CollatzResearch.WordTrace tailWord_1477500 prefixEnd_1477500 758667667018074508155107 := by
  unfold tailWord_1477500
  simp only [CollatzResearch.WordTrace]
  refine ⟨26944426073638655877770977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35925901431518207837027969 26944426073638655877770977)
  ·
    refine ⟨20208319555228991908328233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26944426073638655877770977 20208319555228991908328233)
    ·
      refine ⟨15156239666421743931246175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20208319555228991908328233 15156239666421743931246175)
      ·
        refine ⟨22734359499632615896869263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15156239666421743931246175 22734359499632615896869263)
        ·
          refine ⟨34101539249448923845303895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22734359499632615896869263 34101539249448923845303895)
          ·
            refine ⟨51152308874173385767955843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34101539249448923845303895 51152308874173385767955843)
            ·
              refine ⟨76728463311260078651933765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51152308874173385767955843 76728463311260078651933765)
              ·
                refine ⟨14386586870861264747237581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76728463311260078651933765 14386586870861264747237581)
                ·
                  refine ⟨5394970076572974280214093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14386586870861264747237581 5394970076572974280214093)
                  ·
                    refine ⟨2023113778714865355080285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5394970076572974280214093 2023113778714865355080285)
                    ·
                      refine ⟨758667667018074508155107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2023113778714865355080285 758667667018074508155107)
                      ·
                        rfl

theorem cell23_1477500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_1477500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477500 prefixEnd_1477500 := by exact prefixLift 1477500
  have htrace : WordTrace (prefixWord ++ tailWord_1477500) baseStart_1477500 baseEnd_1477500 := by
    simpa [prefixWord, tailWord_1477500, baseEnd_1477500] using wordTrace_append hprefix tailTrace_1477500
  have hstable : (prefixWord ++ tailWord_1477500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477500).length < 2 ^ (prefixWord ++ tailWord_1477500).sum := by decide
  have hdescent : baseEnd_1477500 < baseStart_1477500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477501 : List Nat := [1, 4, 1, 1, 2, 1, 4, 4, 1, 2, 2]
def baseStart_1477501 : Nat := 118140960795 + 1477501 * 2 ^ 59
def prefixEnd_1477501 : Nat := 4983230072969 + 3 ^ 40 * 1477501 * 2
def baseEnd_1477501 : Nat := 758668180498729004242603

theorem tailTrace_1477501 : CollatzResearch.WordTrace tailWord_1477501 prefixEnd_1477501 758668180498729004242603 := by
  unfold tailWord_1477501
  simp only [CollatzResearch.WordTrace]
  refine ⟨53888888620273688926328357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35925925746849125950885571 53888888620273688926328357)
  ·
    refine ⟨10104166616301316673686567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53888888620273688926328357 10104166616301316673686567)
    ·
      refine ⟨15156249924451975010529851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10104166616301316673686567 15156249924451975010529851)
      ·
        refine ⟨22734374886677962515794777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15156249924451975010529851 22734374886677962515794777)
        ·
          refine ⟨17050781165008471886846083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22734374886677962515794777 17050781165008471886846083)
          ·
            refine ⟨25576171747512707830269125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17050781165008471886846083 25576171747512707830269125)
            ·
              refine ⟨4795532202658632718175461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25576171747512707830269125 4795532202658632718175461)
              ·
                refine ⟨899162287998493634657899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4795532202658632718175461 899162287998493634657899)
                ·
                  refine ⟨1348743431997740451986849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 899162287998493634657899 1348743431997740451986849)
                  ·
                    refine ⟨1011557573998305338990137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1348743431997740451986849 1011557573998305338990137)
                    ·
                      refine ⟨758668180498729004242603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1011557573998305338990137 758668180498729004242603)
                      ·
                        rfl

theorem cell23_1477501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4, 1, 2, 2].length) (baseStart_1477501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477501 prefixEnd_1477501 := by exact prefixLift 1477501
  have htrace : WordTrace (prefixWord ++ tailWord_1477501) baseStart_1477501 baseEnd_1477501 := by
    simpa [prefixWord, tailWord_1477501, baseEnd_1477501] using wordTrace_append hprefix tailTrace_1477501
  have hstable : (prefixWord ++ tailWord_1477501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477501).length < 2 ^ (prefixWord ++ tailWord_1477501).sum := by decide
  have hdescent : baseEnd_1477501 < baseStart_1477501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477503 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 1, 9]
def baseStart_1477503 : Nat := 118140960795 + 1477503 * 2 ^ 59
def prefixEnd_1477503 : Nat := 4983230072969 + 3 ^ 40 * 1477503 * 2
def baseEnd_1477503 : Nat := 252889735820012665472531

theorem tailTrace_1477503 : CollatzResearch.WordTrace tailWord_1477503 prefixEnd_1477503 252889735820012665472531 := by
  unfold tailWord_1477503
  simp only [CollatzResearch.WordTrace]
  refine ⟨53888961566266443267901163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35925974377510962178600775 53888961566266443267901163)
  ·
    refine ⟨80833442349399664901851745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53888961566266443267901163 80833442349399664901851745)
    ·
      refine ⟨60625081762049748676388809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80833442349399664901851745 60625081762049748676388809)
      ·
        refine ⟨45468811321537311507291607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60625081762049748676388809 45468811321537311507291607)
        ·
          refine ⟨68203216982305967260937411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45468811321537311507291607 68203216982305967260937411)
          ·
            refine ⟨102304825473458950891406117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68203216982305967260937411 102304825473458950891406117)
            ·
              refine ⟨19182154776273553292138647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102304825473458950891406117 19182154776273553292138647)
              ·
                refine ⟨28773232164410329938207971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19182154776273553292138647 28773232164410329938207971)
                ·
                  refine ⟨43159848246615494907311957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28773232164410329938207971 43159848246615494907311957)
                  ·
                    refine ⟨252889735820012665472531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 43159848246615494907311957 252889735820012665472531)
                    ·
                      rfl

theorem cell23_1477503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 9].length) (baseStart_1477503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477503 prefixEnd_1477503 := by exact prefixLift 1477503
  have htrace : WordTrace (prefixWord ++ tailWord_1477503) baseStart_1477503 baseEnd_1477503 := by
    simpa [prefixWord, tailWord_1477503, baseEnd_1477503] using wordTrace_append hprefix tailTrace_1477503
  have hstable : (prefixWord ++ tailWord_1477503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477503).length < 2 ^ (prefixWord ++ tailWord_1477503).sum := by decide
  have hdescent : baseEnd_1477503 < baseStart_1477503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477514 : List Nat := [3, 1, 2, 4, 1, 3, 1, 1, 1, 2, 4]
def baseStart_1477514 : Nat := 118140960795 + 1477514 * 2 ^ 59
def prefixEnd_1477514 : Nat := 4983230072969 + 3 ^ 40 * 1477514 * 2
def baseEnd_1477514 : Nat := 758674855747237453380043

theorem tailTrace_1477514 : CollatzResearch.WordTrace tailWord_1477514 prefixEnd_1477514 758674855747237453380043 := by
  unfold tailWord_1477514
  simp only [CollatzResearch.WordTrace]
  refine ⟨13472340692306648036637899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35926241846151061431034397 13472340692306648036637899)
  ·
    refine ⟨20208511038459972054956849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13472340692306648036637899 20208511038459972054956849)
    ·
      refine ⟨15156383278844979041217637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20208511038459972054956849 15156383278844979041217637)
      ·
        refine ⟨2841821864783433570228307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15156383278844979041217637 2841821864783433570228307)
        ·
          refine ⟨4262732797175150355342461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2841821864783433570228307 4262732797175150355342461)
          ·
            refine ⟨1598524798940681383253423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4262732797175150355342461 1598524798940681383253423)
            ·
              refine ⟨2397787198411022074880135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1598524798940681383253423 2397787198411022074880135)
              ·
                refine ⟨3596680797616533112320203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2397787198411022074880135 3596680797616533112320203)
                ·
                  refine ⟨5395021196424799668480305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3596680797616533112320203 5395021196424799668480305)
                  ·
                    refine ⟨4046265897318599751360229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5395021196424799668480305 4046265897318599751360229)
                    ·
                      refine ⟨758674855747237453380043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4046265897318599751360229 758674855747237453380043)
                      ·
                        rfl

theorem cell23_1477514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_1477514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477514 prefixEnd_1477514 := by exact prefixLift 1477514
  have htrace : WordTrace (prefixWord ++ tailWord_1477514) baseStart_1477514 baseEnd_1477514 := by
    simpa [prefixWord, tailWord_1477514, baseEnd_1477514] using wordTrace_append hprefix tailTrace_1477514
  have hstable : (prefixWord ++ tailWord_1477514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477514).length < 2 ^ (prefixWord ++ tailWord_1477514).sum := by decide
  have hdescent : baseEnd_1477514 < baseStart_1477514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477523 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 8]
def baseStart_1477523 : Nat := 118140960795 + 1477523 * 2 ^ 59
def prefixEnd_1477523 : Nat := 4983230072969 + 3 ^ 40 * 1477523 * 2
def baseEnd_1477523 : Nat := 758679477073127918167501

theorem tailTrace_1477523 : CollatzResearch.WordTrace tailWord_1477523 prefixEnd_1477523 758679477073127918167501 := by
  unfold tailWord_1477523
  simp only [CollatzResearch.WordTrace]
  refine ⟨53889691026193986683629223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35926460684129324455752815 53889691026193986683629223)
  ·
    refine ⟨80834536539290980025443835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53889691026193986683629223 80834536539290980025443835)
    ·
      refine ⟨121251804808936470038165753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80834536539290980025443835 121251804808936470038165753)
      ·
        refine ⟨90938853606702352528624315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121251804808936470038165753 90938853606702352528624315)
        ·
          refine ⟨136408280410053528792936473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90938853606702352528624315 136408280410053528792936473)
          ·
            refine ⟨102306210307540146594702355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136408280410053528792936473 102306210307540146594702355)
            ·
              refine ⟨153459315461310219892053533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102306210307540146594702355 153459315461310219892053533)
              ·
                refine ⟨57547243297991332459520075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153459315461310219892053533 57547243297991332459520075)
                ·
                  refine ⟨86320864946986998689280113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57547243297991332459520075 86320864946986998689280113)
                  ·
                    refine ⟨64740648710240249016960085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86320864946986998689280113 64740648710240249016960085)
                    ·
                      refine ⟨758679477073127918167501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 64740648710240249016960085 758679477073127918167501)
                      ·
                        rfl

theorem cell23_1477523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_1477523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477523 prefixEnd_1477523 := by exact prefixLift 1477523
  have htrace : WordTrace (prefixWord ++ tailWord_1477523) baseStart_1477523 baseEnd_1477523 := by
    simpa [prefixWord, tailWord_1477523, baseEnd_1477523] using wordTrace_append hprefix tailTrace_1477523
  have hstable : (prefixWord ++ tailWord_1477523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477523).length < 2 ^ (prefixWord ++ tailWord_1477523).sum := by decide
  have hdescent : baseEnd_1477523 < baseStart_1477523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477580 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 9]
def baseStart_1477580 : Nat := 118140960795 + 1477580 * 2 ^ 59
def prefixEnd_1477580 : Nat := 4983230072969 + 3 ^ 40 * 1477580 * 2
def baseEnd_1477580 : Nat := 84300971718937132794971

theorem tailTrace_1477580 : CollatzResearch.WordTrace tailWord_1477580 prefixEnd_1477580 84300971718937132794971 := by
  unfold tailWord_1477580
  simp only [CollatzResearch.WordTrace]
  refine ⟨26945884993493742709227097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35927846657991656945636129 26945884993493742709227097)
  ·
    refine ⟨20209413745120307031920323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26945884993493742709227097 20209413745120307031920323)
    ·
      refine ⟨30314120617680460547880485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20209413745120307031920323 30314120617680460547880485)
      ·
        refine ⟨5683897615815086352727591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30314120617680460547880485 5683897615815086352727591)
        ·
          refine ⟨8525846423722629529091387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5683897615815086352727591 8525846423722629529091387)
          ·
            refine ⟨12788769635583944293637081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8525846423722629529091387 12788769635583944293637081)
            ·
              refine ⟨9591577226687958220227811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12788769635583944293637081 9591577226687958220227811)
              ·
                refine ⟨14387365840031937330341717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9591577226687958220227811 14387365840031937330341717)
                ·
                  refine ⟨84300971718937132794971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14387365840031937330341717 84300971718937132794971)
                  ·
                    rfl

theorem cell23_1477580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 9].length) (baseStart_1477580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477580 prefixEnd_1477580 := by exact prefixLift 1477580
  have htrace : WordTrace (prefixWord ++ tailWord_1477580) baseStart_1477580 baseEnd_1477580 := by
    simpa [prefixWord, tailWord_1477580, baseEnd_1477580] using wordTrace_append hprefix tailTrace_1477580
  have hstable : (prefixWord ++ tailWord_1477580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477580).length < 2 ^ (prefixWord ++ tailWord_1477580).sum := by decide
  have hdescent : baseEnd_1477580 < baseStart_1477580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477621 : List Nat := [1, 3, 5, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_1477621 : Nat := 118140960795 + 1477621 * 2 ^ 59
def prefixEnd_1477621 : Nat := 4983230072969 + 3 ^ 40 * 1477621 * 2
def baseEnd_1477621 : Nat := 758729798177268534742051

theorem tailTrace_1477621 : CollatzResearch.WordTrace tailWord_1477621 prefixEnd_1477621 758729798177268534742051 := by
  unfold tailWord_1477621
  simp only [CollatzResearch.WordTrace]
  refine ⟨53893265379838949420696717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35928843586559299613797811 53893265379838949420696717)
  ·
    refine ⟨20209974517439606032761269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53893265379838949420696717 20209974517439606032761269)
    ·
      refine ⟨1894685111009963065571369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20209974517439606032761269 1894685111009963065571369)
      ·
        refine ⟨1421013833257472299178527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1894685111009963065571369 1421013833257472299178527)
        ·
          refine ⟨2131520749886208448767791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1421013833257472299178527 2131520749886208448767791)
          ·
            refine ⟨3197281124829312673151687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2131520749886208448767791 3197281124829312673151687)
            ·
              refine ⟨4795921687243969009727531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3197281124829312673151687 4795921687243969009727531)
              ·
                refine ⟨7193882530865953514591297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4795921687243969009727531 7193882530865953514591297)
                ·
                  refine ⟨5395411898149465135943473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7193882530865953514591297 5395411898149465135943473)
                  ·
                    refine ⟨4046558923612098851957605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5395411898149465135943473 4046558923612098851957605)
                    ·
                      refine ⟨758729798177268534742051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4046558923612098851957605 758729798177268534742051)
                      ·
                        rfl

theorem cell23_1477621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_1477621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477621 prefixEnd_1477621 := by exact prefixLift 1477621
  have htrace : WordTrace (prefixWord ++ tailWord_1477621) baseStart_1477621 baseEnd_1477621 := by
    simpa [prefixWord, tailWord_1477621, baseEnd_1477621] using wordTrace_append hprefix tailTrace_1477621
  have hstable : (prefixWord ++ tailWord_1477621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477621).length < 2 ^ (prefixWord ++ tailWord_1477621).sum := by decide
  have hdescent : baseEnd_1477621 < baseStart_1477621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477644 : List Nat := [2, 2, 1, 2, 3, 4, 1, 1, 2, 5]
def baseStart_1477644 : Nat := 118140960795 + 1477644 * 2 ^ 59
def prefixEnd_1477644 : Nat := 4983230072969 + 3 ^ 40 * 1477644 * 2
def baseEnd_1477644 : Nat := 252913869410773981584815

theorem tailTrace_1477644 : CollatzResearch.WordTrace tailWord_1477644 prefixEnd_1477644 252913869410773981584815 := by
  unfold tailWord_1477644
  simp only [CollatzResearch.WordTrace]
  refine ⟨26947052129377812174391993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35929402839170416232522657 26947052129377812174391993)
  ·
    refine ⟨20210289097033359130793995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26947052129377812174391993 20210289097033359130793995)
    ·
      refine ⟨30315433645550038696190993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20210289097033359130793995 30315433645550038696190993)
      ·
        refine ⟨22736575234162529022143245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30315433645550038696190993 22736575234162529022143245)
        ·
          refine ⟨8526215712810948383303717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22736575234162529022143245 8526215712810948383303717)
          ·
            refine ⟨1598665446152052821869447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8526215712810948383303717 1598665446152052821869447)
            ·
              refine ⟨2397998169228079232804171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1598665446152052821869447 2397998169228079232804171)
              ·
                refine ⟨3596997253842118849206257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2397998169228079232804171 3596997253842118849206257)
                ·
                  refine ⟨2697747940381589136904693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3596997253842118849206257 2697747940381589136904693)
                  ·
                    refine ⟨252913869410773981584815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2697747940381589136904693 252913869410773981584815)
                    ·
                      rfl

theorem cell23_1477644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 2, 5].length) (baseStart_1477644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477644 prefixEnd_1477644 := by exact prefixLift 1477644
  have htrace : WordTrace (prefixWord ++ tailWord_1477644) baseStart_1477644 baseEnd_1477644 := by
    simpa [prefixWord, tailWord_1477644, baseEnd_1477644] using wordTrace_append hprefix tailTrace_1477644
  have hstable : (prefixWord ++ tailWord_1477644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477644).length < 2 ^ (prefixWord ++ tailWord_1477644).sum := by decide
  have hdescent : baseEnd_1477644 < baseStart_1477644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477725 : List Nat := [1, 4, 4, 1, 3, 1, 1, 1, 3, 4]
def baseStart_1477725 : Nat := 118140960795 + 1477725 * 2 ^ 59
def prefixEnd_1477725 : Nat := 4983230072969 + 3 ^ 40 * 1477725 * 2
def baseEnd_1477725 : Nat := 252927733388445375947191

theorem tailTrace_1477725 : CollatzResearch.WordTrace tailWord_1477725 prefixEnd_1477725 252927733388445375947191 := by
  unfold tailWord_1477725
  simp only [CollatzResearch.WordTrace]
  refine ⟨53897058571462175182482629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35931372380974783454988419 53897058571462175182482629)
  ·
    refine ⟨10105698482149157846715493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53897058571462175182482629 10105698482149157846715493)
    ·
      refine ⟨1894818465402967096259155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10105698482149157846715493 1894818465402967096259155)
      ·
        refine ⟨2842227698104450644388733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1894818465402967096259155 2842227698104450644388733)
        ·
          refine ⟨1065835386789168991645775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2842227698104450644388733 1065835386789168991645775)
          ·
            refine ⟨1598753080183753487468663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1065835386789168991645775 1598753080183753487468663)
            ·
              refine ⟨2398129620275630231202995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1598753080183753487468663 2398129620275630231202995)
              ·
                refine ⟨3597194430413445346804493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2398129620275630231202995 3597194430413445346804493)
                ·
                  refine ⟨1348947911405042005051685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3597194430413445346804493 1348947911405042005051685)
                  ·
                    refine ⟨252927733388445375947191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1348947911405042005051685 252927733388445375947191)
                    ·
                      rfl

theorem cell23_1477725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_1477725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477725 prefixEnd_1477725 := by exact prefixLift 1477725
  have htrace : WordTrace (prefixWord ++ tailWord_1477725) baseStart_1477725 baseEnd_1477725 := by
    simpa [prefixWord, tailWord_1477725, baseEnd_1477725] using wordTrace_append hprefix tailTrace_1477725
  have hstable : (prefixWord ++ tailWord_1477725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477725).length < 2 ^ (prefixWord ++ tailWord_1477725).sum := by decide
  have hdescent : baseEnd_1477725 < baseStart_1477725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477764 : List Nat := [2, 3, 2, 1, 2, 3, 1, 2, 1, 6]
def baseStart_1477764 : Nat := 118140960795 + 1477764 * 2 ^ 59
def prefixEnd_1477764 : Nat := 4983230072969 + 3 ^ 40 * 1477764 * 2
def baseEnd_1477764 : Nat := 252934408636953825084631

theorem tailTrace_1477764 : CollatzResearch.WordTrace tailWord_1477764 prefixEnd_1477764 252934408636953825084631 := by
  unfold tailWord_1477764
  simp only [CollatzResearch.WordTrace]
  refine ⟨26949240509160442421576173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35932320678880589895434897 26949240509160442421576173)
  ·
    refine ⟨10105965190935165908091065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26949240509160442421576173 10105965190935165908091065)
    ·
      refine ⟨7579473893201374431068299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10105965190935165908091065 7579473893201374431068299)
      ·
        refine ⟨11369210839802061646602449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7579473893201374431068299 11369210839802061646602449)
        ·
          refine ⟨8526908129851546234951837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11369210839802061646602449 8526908129851546234951837)
          ·
            refine ⟨3197590548694329838106939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8526908129851546234951837 3197590548694329838106939)
            ·
              refine ⟨4796385823041494757160409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3197590548694329838106939 4796385823041494757160409)
              ·
                refine ⟨3597289367281121067870307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4796385823041494757160409 3597289367281121067870307)
                ·
                  refine ⟨5395934050921681601805461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3597289367281121067870307 5395934050921681601805461)
                  ·
                    refine ⟨252934408636953825084631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5395934050921681601805461 252934408636953825084631)
                    ·
                      rfl

theorem cell23_1477764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_1477764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477764 prefixEnd_1477764 := by exact prefixLift 1477764
  have htrace : WordTrace (prefixWord ++ tailWord_1477764) baseStart_1477764 baseEnd_1477764 := by
    simpa [prefixWord, tailWord_1477764, baseEnd_1477764] using wordTrace_append hprefix tailTrace_1477764
  have hstable : (prefixWord ++ tailWord_1477764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477764).length < 2 ^ (prefixWord ++ tailWord_1477764).sum := by decide
  have hdescent : baseEnd_1477764 < baseStart_1477764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477768 : List Nat := [2, 1, 3, 4, 2, 1, 3, 1, 1, 5]
def baseStart_1477768 : Nat := 118140960795 + 1477768 * 2 ^ 59
def prefixEnd_1477768 : Nat := 4983230072969 + 3 ^ 40 * 1477768 * 2
def baseEnd_1477768 : Nat := 252935093277826486534625

theorem tailTrace_1477768 : CollatzResearch.WordTrace tailWord_1477768 prefixEnd_1477768 252935093277826486534625 := by
  unfold tailWord_1477768
  simp only [CollatzResearch.WordTrace]
  refine ⟨26949313455153196763148979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35932417940204262350865305 26949313455153196763148979)
  ·
    refine ⟨40423970182729795144723469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26949313455153196763148979 40423970182729795144723469)
    ·
      refine ⟨15158988818523673179271301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40423970182729795144723469 15158988818523673179271301)
      ·
        refine ⟨2842310403473188721113369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15158988818523673179271301 2842310403473188721113369)
        ·
          refine ⟨2131732802604891540835027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2842310403473188721113369 2131732802604891540835027)
          ·
            refine ⟨3197599203907337311252541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2131732802604891540835027 3197599203907337311252541)
            ·
              refine ⟨1199099701465251491719703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3197599203907337311252541 1199099701465251491719703)
              ·
                refine ⟨1798649552197877237579555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1199099701465251491719703 1798649552197877237579555)
                ·
                  refine ⟨2697974328296815856369333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1798649552197877237579555 2697974328296815856369333)
                  ·
                    refine ⟨252935093277826486534625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2697974328296815856369333 252935093277826486534625)
                    ·
                      rfl

theorem cell23_1477768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_1477768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477768 prefixEnd_1477768 := by exact prefixLift 1477768
  have htrace : WordTrace (prefixWord ++ tailWord_1477768) baseStart_1477768 baseEnd_1477768 := by
    simpa [prefixWord, tailWord_1477768, baseEnd_1477768] using wordTrace_append hprefix tailTrace_1477768
  have hstable : (prefixWord ++ tailWord_1477768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477768).length < 2 ^ (prefixWord ++ tailWord_1477768).sum := by decide
  have hdescent : baseEnd_1477768 < baseStart_1477768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477787 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 2, 7, 3]
def baseStart_1477787 : Nat := 118140960795 + 1477787 * 2 ^ 59
def prefixEnd_1477787 : Nat := 4983230072969 + 3 ^ 40 * 1477787 * 2
def baseEnd_1477787 : Nat := 758815035965914885266287

theorem tailTrace_1477787 : CollatzResearch.WordTrace tailWord_1477787 prefixEnd_1477787 758815035965914885266287 := by
  unfold tailWord_1477787
  simp only [CollatzResearch.WordTrace]
  refine ⟨53899319897237559771239615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35932879931491706514159743 53899319897237559771239615)
  ·
    refine ⟨80848979845856339656859423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53899319897237559771239615 80848979845856339656859423)
    ·
      refine ⟨121273469768784509485289135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80848979845856339656859423 121273469768784509485289135)
      ·
        refine ⟨181910204653176764227933703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121273469768784509485289135 181910204653176764227933703)
        ·
          refine ⟨272865306979765146341900555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181910204653176764227933703 272865306979765146341900555)
          ·
            refine ⟨409297960469647719512850833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272865306979765146341900555 409297960469647719512850833)
            ·
              refine ⟨306973470352235789634638125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 409297960469647719512850833 306973470352235789634638125)
              ·
                refine ⟨115115051382088421112989297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306973470352235789634638125 115115051382088421112989297)
                ·
                  refine ⟨86336288536566315834741973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115115051382088421112989297 86336288536566315834741973)
                  ·
                    refine ⟨2023506762575773027376765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 86336288536566315834741973 2023506762575773027376765)
                    ·
                      refine ⟨758815035965914885266287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2023506762575773027376765 758815035965914885266287)
                      ·
                        rfl

theorem cell23_1477787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7, 3].length) (baseStart_1477787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477787 prefixEnd_1477787 := by exact prefixLift 1477787
  have htrace : WordTrace (prefixWord ++ tailWord_1477787) baseStart_1477787 baseEnd_1477787 := by
    simpa [prefixWord, tailWord_1477787, baseEnd_1477787] using wordTrace_append hprefix tailTrace_1477787
  have hstable : (prefixWord ++ tailWord_1477787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477787).length < 2 ^ (prefixWord ++ tailWord_1477787).sum := by decide
  have hdescent : baseEnd_1477787 < baseStart_1477787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477805 : List Nat := [1, 5, 2, 1, 3, 1, 1, 2, 3, 2, 2]
def baseStart_1477805 : Nat := 118140960795 + 1477805 * 2 ^ 59
def prefixEnd_1477805 : Nat := 4983230072969 + 3 ^ 40 * 1477805 * 2
def baseEnd_1477805 : Nat := 758824278617695814841205

theorem tailTrace_1477805 : CollatzResearch.WordTrace tailWord_1477805 prefixEnd_1477805 758824278617695814841205 := by
  unfold tailWord_1477805
  simp only [CollatzResearch.WordTrace]
  refine ⟨53899976411172348845394869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35933317607448232563596579 53899976411172348845394869)
  ·
    refine ⟨5053122788547407704255769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53899976411172348845394869 5053122788547407704255769)
    ·
      refine ⟨3789842091410555778191827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5053122788547407704255769 3789842091410555778191827)
      ·
        refine ⟨5684763137115833667287741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3789842091410555778191827 5684763137115833667287741)
        ·
          refine ⟨2131786176418437625232903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5684763137115833667287741 2131786176418437625232903)
          ·
            refine ⟨3197679264627656437849355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2131786176418437625232903 3197679264627656437849355)
            ·
              refine ⟨4796518896941484656774033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3197679264627656437849355 4796518896941484656774033)
              ·
                refine ⟨3597389172706113492580525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4796518896941484656774033 3597389172706113492580525)
                ·
                  refine ⟨1349020939764792559717697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3597389172706113492580525 1349020939764792559717697)
                  ·
                    refine ⟨1011765704823594419788273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1349020939764792559717697 1011765704823594419788273)
                    ·
                      refine ⟨758824278617695814841205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1011765704823594419788273 758824278617695814841205)
                      ·
                        rfl

theorem cell23_1477805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_1477805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477805 prefixEnd_1477805 := by exact prefixLift 1477805
  have htrace : WordTrace (prefixWord ++ tailWord_1477805) baseStart_1477805 baseEnd_1477805 := by
    simpa [prefixWord, tailWord_1477805, baseEnd_1477805] using wordTrace_append hprefix tailTrace_1477805
  have hstable : (prefixWord ++ tailWord_1477805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477805).length < 2 ^ (prefixWord ++ tailWord_1477805).sum := by decide
  have hdescent : baseEnd_1477805 < baseStart_1477805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477822 : List Nat := [4, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2]
def baseStart_1477822 : Nat := 118140960795 + 1477822 * 2 ^ 59
def prefixEnd_1477822 : Nat := 4983230072969 + 3 ^ 40 * 1477822 * 2
def baseEnd_1477822 : Nat := 758833007788822248328627

theorem tailTrace_1477822 : CollatzResearch.WordTrace tailWord_1477822 prefixEnd_1477822 758833007788822248328627 := by
  unfold tailWord_1477822
  simp only [CollatzResearch.WordTrace]
  refine ⟨6737574556513845093595465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35933730968073840499175813 6737574556513845093595465)
  ·
    refine ⟨5053180917385383820196599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6737574556513845093595465 5053180917385383820196599)
    ·
      refine ⟨7579771376078075730294899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5053180917385383820196599 7579771376078075730294899)
      ·
        refine ⟨11369657064117113595442349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7579771376078075730294899 11369657064117113595442349)
        ·
          refine ⟨4263621399043917598290881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11369657064117113595442349 4263621399043917598290881)
          ·
            refine ⟨3197716049282938198718161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4263621399043917598290881 3197716049282938198718161)
            ·
              refine ⟨2398287036962203649038621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3197716049282938198718161 2398287036962203649038621)
              ·
                refine ⟨899357638860826368389483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2398287036962203649038621 899357638860826368389483)
                ·
                  refine ⟨1349036458291239552584225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 899357638860826368389483 1349036458291239552584225)
                  ·
                    refine ⟨1011777343718429664438169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1349036458291239552584225 1011777343718429664438169)
                    ·
                      refine ⟨758833007788822248328627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1011777343718429664438169 758833007788822248328627)
                      ·
                        rfl

theorem cell23_1477822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_1477822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477822 prefixEnd_1477822 := by exact prefixLift 1477822
  have htrace : WordTrace (prefixWord ++ tailWord_1477822) baseStart_1477822 baseEnd_1477822 := by
    simpa [prefixWord, tailWord_1477822, baseEnd_1477822] using wordTrace_append hprefix tailTrace_1477822
  have hstable : (prefixWord ++ tailWord_1477822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477822).length < 2 ^ (prefixWord ++ tailWord_1477822).sum := by decide
  have hdescent : baseEnd_1477822 < baseStart_1477822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477825 : List Nat := [1, 2, 6, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_1477825 : Nat := 118140960795 + 1477825 * 2 ^ 59
def prefixEnd_1477825 : Nat := 4983230072969 + 3 ^ 40 * 1477825 * 2
def baseEnd_1477825 : Nat := 758834548230785736591113

theorem tailTrace_1477825 : CollatzResearch.WordTrace tailWord_1477825 prefixEnd_1477825 758834548230785736591113 := by
  unfold tailWord_1477825
  simp only [CollatzResearch.WordTrace]
  refine ⟨53900705871099892261122929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35933803914066594840748619 53900705871099892261122929)
  ·
    refine ⟨40425529403324919195842197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53900705871099892261122929 40425529403324919195842197)
    ·
      refine ⟨1894946690780855587305103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40425529403324919195842197 1894946690780855587305103)
      ·
        refine ⟨2842420036171283380957655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1894946690780855587305103 2842420036171283380957655)
        ·
          refine ⟨4263630054256925071436483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2842420036171283380957655 4263630054256925071436483)
          ·
            refine ⟨6395445081385387607154725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4263630054256925071436483 6395445081385387607154725)
            ·
              refine ⟨1199145952759760176341511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6395445081385387607154725 1199145952759760176341511)
              ·
                refine ⟨1798718929139640264512267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1199145952759760176341511 1798718929139640264512267)
                ·
                  refine ⟨2698078393709460396768401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1798718929139640264512267 2698078393709460396768401)
                  ·
                    refine ⟨2023558795282095297576301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2698078393709460396768401 2023558795282095297576301)
                    ·
                      refine ⟨758834548230785736591113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2023558795282095297576301 758834548230785736591113)
                      ·
                        rfl

theorem cell23_1477825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_1477825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477825 prefixEnd_1477825 := by exact prefixLift 1477825
  have htrace : WordTrace (prefixWord ++ tailWord_1477825) baseStart_1477825 baseEnd_1477825 := by
    simpa [prefixWord, tailWord_1477825, baseEnd_1477825] using wordTrace_append hprefix tailTrace_1477825
  have hstable : (prefixWord ++ tailWord_1477825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477825).length < 2 ^ (prefixWord ++ tailWord_1477825).sum := by decide
  have hdescent : baseEnd_1477825 < baseStart_1477825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477827 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 4]
def baseStart_1477827 : Nat := 118140960795 + 1477827 * 2 ^ 59
def prefixEnd_1477827 : Nat := 4983230072969 + 3 ^ 40 * 1477827 * 2
def baseEnd_1477827 : Nat := 758835575192094728766103

theorem tailTrace_1477827 : CollatzResearch.WordTrace tailWord_1477827 prefixEnd_1477827 758835575192094728766103 := by
  unfold tailWord_1477827
  simp only [CollatzResearch.WordTrace]
  refine ⟨53900778817092646602695735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35933852544728431068463823 53900778817092646602695735)
  ·
    refine ⟨80851168225638969904043603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53900778817092646602695735 80851168225638969904043603)
    ·
      refine ⟨121276752338458454856065405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80851168225638969904043603 121276752338458454856065405)
      ·
        refine ⟨45478782126921920571024527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121276752338458454856065405 45478782126921920571024527)
        ·
          refine ⟨68218173190382880856536791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45478782126921920571024527 68218173190382880856536791)
          ·
            refine ⟨102327259785574321284805187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68218173190382880856536791 102327259785574321284805187)
            ·
              refine ⟨153490889678361481927207781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102327259785574321284805187 153490889678361481927207781)
              ·
                refine ⟨28779541814692777861351459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153490889678361481927207781 28779541814692777861351459)
                ·
                  refine ⟨43169312722039166792027189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28779541814692777861351459 43169312722039166792027189)
                  ·
                    refine ⟨4047123067691171886752549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43169312722039166792027189 4047123067691171886752549)
                    ·
                      refine ⟨758835575192094728766103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4047123067691171886752549 758835575192094728766103)
                      ·
                        rfl

theorem cell23_1477827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_1477827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477827 prefixEnd_1477827 := by exact prefixLift 1477827
  have htrace : WordTrace (prefixWord ++ tailWord_1477827) baseStart_1477827 baseEnd_1477827 := by
    simpa [prefixWord, tailWord_1477827, baseEnd_1477827] using wordTrace_append hprefix tailTrace_1477827
  have hstable : (prefixWord ++ tailWord_1477827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477827).length < 2 ^ (prefixWord ++ tailWord_1477827).sum := by decide
  have hdescent : baseEnd_1477827 < baseStart_1477827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477838 : List Nat := [4, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3]
def baseStart_1477838 : Nat := 118140960795 + 1477838 * 2 ^ 59
def prefixEnd_1477838 : Nat := 4983230072969 + 3 ^ 40 * 1477838 * 2
def baseEnd_1477838 : Nat := 758841223479294185728553

theorem tailTrace_1477838 : CollatzResearch.WordTrace tailWord_1477838 prefixEnd_1477838 758841223479294185728553 := by
  unfold tailWord_1477838
  simp only [CollatzResearch.WordTrace]
  refine ⟨6737647502506599435168271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35934120013368530320897445 6737647502506599435168271)
  ·
    refine ⟨10106471253759899152752407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6737647502506599435168271 10106471253759899152752407)
    ·
      refine ⟨15159706880639848729128611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10106471253759899152752407 15159706880639848729128611)
      ·
        refine ⟨22739560320959773093692917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15159706880639848729128611 22739560320959773093692917)
        ·
          refine ⟨2131833780089978727533711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22739560320959773093692917 2131833780089978727533711)
          ·
            refine ⟨3197750670134968091300567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2131833780089978727533711 3197750670134968091300567)
            ·
              refine ⟨4796626005202452136950851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3197750670134968091300567 4796626005202452136950851)
              ·
                refine ⟨7194939007803678205426277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4796626005202452136950851 7194939007803678205426277)
                ·
                  refine ⟨1349051063963189663517427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7194939007803678205426277 1349051063963189663517427)
                  ·
                    refine ⟨2023576595944784495276141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1349051063963189663517427 2023576595944784495276141)
                    ·
                      refine ⟨758841223479294185728553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2023576595944784495276141 758841223479294185728553)
                      ·
                        rfl

theorem cell23_1477838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_1477838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477838 prefixEnd_1477838 := by exact prefixLift 1477838
  have htrace : WordTrace (prefixWord ++ tailWord_1477838) baseStart_1477838 baseEnd_1477838 := by
    simpa [prefixWord, tailWord_1477838, baseEnd_1477838] using wordTrace_append hprefix tailTrace_1477838
  have hstable : (prefixWord ++ tailWord_1477838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477838).length < 2 ^ (prefixWord ++ tailWord_1477838).sum := by decide
  have hdescent : baseEnd_1477838 < baseStart_1477838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477864 : List Nat := [2, 1, 4, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_1477864 : Nat := 118140960795 + 1477864 * 2 ^ 59
def prefixEnd_1477864 : Nat := 4983230072969 + 3 ^ 40 * 1477864 * 2
def baseEnd_1477864 : Nat := 758854573976311084003433

theorem tailTrace_1477864 : CollatzResearch.WordTrace tailWord_1477864 prefixEnd_1477864 758854573976311084003433 := by
  unfold tailWord_1477864
  simp only [CollatzResearch.WordTrace]
  refine ⟨26951064158979300960896323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35934752211972401281195097 26951064158979300960896323)
  ·
    refine ⟨40426596238468951441344485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26951064158979300960896323 40426596238468951441344485)
    ·
      refine ⟨7579986794712928395252091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40426596238468951441344485 7579986794712928395252091)
      ·
        refine ⟨11369980192069392592878137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7579986794712928395252091 11369980192069392592878137)
        ·
          refine ⟨8527485144052044444658603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11369980192069392592878137 8527485144052044444658603)
          ·
            refine ⟨12791227716078066666987905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8527485144052044444658603 12791227716078066666987905)
            ·
              refine ⟨9593420787058550000240929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12791227716078066666987905 9593420787058550000240929)
              ·
                refine ⟨7195065590293912500180697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9593420787058550000240929 7195065590293912500180697)
                ·
                  refine ⟨5396299192720434375135523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7195065590293912500180697 5396299192720434375135523)
                  ·
                    refine ⟨8094448789080651562703285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5396299192720434375135523 8094448789080651562703285)
                    ·
                      refine ⟨758854573976311084003433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8094448789080651562703285 758854573976311084003433)
                      ·
                        rfl

theorem cell23_1477864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_1477864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477864 prefixEnd_1477864 := by exact prefixLift 1477864
  have htrace : WordTrace (prefixWord ++ tailWord_1477864) baseStart_1477864 baseEnd_1477864 := by
    simpa [prefixWord, tailWord_1477864, baseEnd_1477864] using wordTrace_append hprefix tailTrace_1477864
  have hstable : (prefixWord ++ tailWord_1477864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477864).length < 2 ^ (prefixWord ++ tailWord_1477864).sum := by decide
  have hdescent : baseEnd_1477864 < baseStart_1477864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477906 : List Nat := [3, 2, 4, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_1477906 : Nat := 118140960795 + 1477906 * 2 ^ 59
def prefixEnd_1477906 : Nat := 4983230072969 + 3 ^ 40 * 1477906 * 2
def baseEnd_1477906 : Nat := 758876140163799919678241

theorem tailTrace_1477906 : CollatzResearch.WordTrace tailWord_1477906 prefixEnd_1477906 758876140163799919678241 := by
  unfold tailWord_1477906
  simp only [CollatzResearch.WordTrace]
  refine ⟨13475915045951610773705393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35935773455870962063214381 13475915045951610773705393)
  ·
    refine ⟨10106936284463708080279045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13475915045951610773705393 10106936284463708080279045)
    ·
      refine ⟨1895050553336945265052321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10106936284463708080279045 1895050553336945265052321)
      ·
        refine ⟨1421287915002708948789241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1895050553336945265052321 1421287915002708948789241)
        ·
          refine ⟨1065965936252031711591931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1421287915002708948789241 1065965936252031711591931)
          ·
            refine ⟨1598948904378047567387897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1065965936252031711591931 1598948904378047567387897)
            ·
              refine ⟨1199211678283535675540923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1598948904378047567387897 1199211678283535675540923)
              ·
                refine ⟨1798817517425303513311385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1199211678283535675540923 1798817517425303513311385)
                ·
                  refine ⟨1349113138068977634983539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1798817517425303513311385 1349113138068977634983539)
                  ·
                    refine ⟨2023669707103466452475309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1349113138068977634983539 2023669707103466452475309)
                    ·
                      refine ⟨758876140163799919678241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2023669707103466452475309 758876140163799919678241)
                      ·
                        rfl

theorem cell23_1477906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_1477906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477906 prefixEnd_1477906 := by exact prefixLift 1477906
  have htrace : WordTrace (prefixWord ++ tailWord_1477906) baseStart_1477906 baseEnd_1477906 := by
    simpa [prefixWord, tailWord_1477906, baseEnd_1477906] using wordTrace_append hprefix tailTrace_1477906
  have hstable : (prefixWord ++ tailWord_1477906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477906).length < 2 ^ (prefixWord ++ tailWord_1477906).sum := by decide
  have hdescent : baseEnd_1477906 < baseStart_1477906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477912 : List Nat := [2, 1, 2, 3, 1, 5, 2, 1, 2, 2, 2]
def baseStart_1477912 : Nat := 118140960795 + 1477912 * 2 ^ 59
def prefixEnd_1477912 : Nat := 4983230072969 + 3 ^ 40 * 1477912 * 2
def baseEnd_1477912 : Nat := 758879221047726896203213

theorem tailTrace_1477912 : CollatzResearch.WordTrace tailWord_1477912 prefixEnd_1477912 758879221047726896203213 := by
  unfold tailWord_1477912
  simp only [CollatzResearch.WordTrace]
  refine ⟨26951939510892353059769995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35935919347856470746359993 26951939510892353059769995)
  ·
    refine ⟨40427909266338529589654993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26951939510892353059769995 40427909266338529589654993)
    ·
      refine ⟨30320931949753897192241245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40427909266338529589654993 30320931949753897192241245)
      ·
        refine ⟨11370349481157711447090467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30320931949753897192241245 11370349481157711447090467)
        ·
          refine ⟨17055524221736567170635701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11370349481157711447090467 17055524221736567170635701)
          ·
            refine ⟨1598955395787803172247097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17055524221736567170635701 1598955395787803172247097)
            ·
              refine ⟨1199216546840852379185323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1598955395787803172247097 1199216546840852379185323)
              ·
                refine ⟨1798824820261278568777985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1199216546840852379185323 1798824820261278568777985)
                ·
                  refine ⟨1349118615195958926583489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1798824820261278568777985 1349118615195958926583489)
                  ·
                    refine ⟨1011838961396969194937617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1349118615195958926583489 1011838961396969194937617)
                    ·
                      refine ⟨758879221047726896203213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1011838961396969194937617 758879221047726896203213)
                      ·
                        rfl

theorem cell23_1477912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_1477912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477912 prefixEnd_1477912 := by exact prefixLift 1477912
  have htrace : WordTrace (prefixWord ++ tailWord_1477912) baseStart_1477912 baseEnd_1477912 := by
    simpa [prefixWord, tailWord_1477912, baseEnd_1477912] using wordTrace_append hprefix tailTrace_1477912
  have hstable : (prefixWord ++ tailWord_1477912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477912).length < 2 ^ (prefixWord ++ tailWord_1477912).sum := by decide
  have hdescent : baseEnd_1477912 < baseStart_1477912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477924 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 1, 1, 7]
def baseStart_1477924 : Nat := 118140960795 + 1477924 * 2 ^ 59
def prefixEnd_1477924 : Nat := 4983230072969 + 3 ^ 40 * 1477924 * 2
def baseEnd_1477924 : Nat := 758885382815580849253157

theorem tailTrace_1477924 : CollatzResearch.WordTrace tailWord_1477924 prefixEnd_1477924 758885382815580849253157 := by
  unfold tailWord_1477924
  simp only [CollatzResearch.WordTrace]
  refine ⟨26952158348870616084488413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35936211131827488112651217 26952158348870616084488413)
  ·
    refine ⟨10107059380826481031683155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26952158348870616084488413 10107059380826481031683155)
    ·
      refine ⟨15160589071239721547524733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10107059380826481031683155 15160589071239721547524733)
      ·
        refine ⟨5685220901714895580321775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15160589071239721547524733 5685220901714895580321775)
        ·
          refine ⟨8527831352572343370482663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5685220901714895580321775 8527831352572343370482663)
          ·
            refine ⟨12791747028858515055723995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8527831352572343370482663 12791747028858515055723995)
            ·
              refine ⟨19187620543287772583585993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12791747028858515055723995 19187620543287772583585993)
              ·
                refine ⟨14390715407465829437689495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19187620543287772583585993 14390715407465829437689495)
                ·
                  refine ⟨21586073111198744156534243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14390715407465829437689495 21586073111198744156534243)
                  ·
                    refine ⟨32379109666798116234801365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21586073111198744156534243 32379109666798116234801365)
                    ·
                      refine ⟨758885382815580849253157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 32379109666798116234801365 758885382815580849253157)
                      ·
                        rfl

theorem cell23_1477924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_1477924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477924 prefixEnd_1477924 := by exact prefixLift 1477924
  have htrace : WordTrace (prefixWord ++ tailWord_1477924) baseStart_1477924 baseEnd_1477924 := by
    simpa [prefixWord, tailWord_1477924, baseEnd_1477924] using wordTrace_append hprefix tailTrace_1477924
  have hstable : (prefixWord ++ tailWord_1477924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477924).length < 2 ^ (prefixWord ++ tailWord_1477924).sum := by decide
  have hdescent : baseEnd_1477924 < baseStart_1477924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477951 : List Nat := [1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 4]
def baseStart_1477951 : Nat := 118140960795 + 1477951 * 2 ^ 59
def prefixEnd_1477951 : Nat := 4983230072969 + 3 ^ 40 * 1477951 * 2
def baseEnd_1477951 : Nat := 758899246793252243615533

theorem tailTrace_1477951 : CollatzResearch.WordTrace tailWord_1477951 prefixEnd_1477951 758899246793252243615533 := by
  unfold tailWord_1477951
  simp only [CollatzResearch.WordTrace]
  refine ⟨53905301468643415780209707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35936867645762277186806471 53905301468643415780209707)
  ·
    refine ⟨80857952202965123670314561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53905301468643415780209707 80857952202965123670314561)
    ·
      refine ⟨60643464152223842752735921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80857952202965123670314561 60643464152223842752735921)
      ·
        refine ⟨45482598114167882064551941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60643464152223842752735921 45482598114167882064551941)
        ·
          refine ⟨8527987146406477887103489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45482598114167882064551941 8527987146406477887103489)
          ·
            refine ⟨6395990359804858415327617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8527987146406477887103489 6395990359804858415327617)
            ·
              refine ⟨4796992769853643811495713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6395990359804858415327617 4796992769853643811495713)
              ·
                refine ⟨3597744577390232858621785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4796992769853643811495713 3597744577390232858621785)
                ·
                  refine ⟨2698308433042674643966339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3597744577390232858621785 2698308433042674643966339)
                  ·
                    refine ⟨4047462649564011965949509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2698308433042674643966339 4047462649564011965949509)
                    ·
                      refine ⟨758899246793252243615533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4047462649564011965949509 758899246793252243615533)
                      ·
                        rfl

theorem cell23_1477951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_1477951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477951 prefixEnd_1477951 := by exact prefixLift 1477951
  have htrace : WordTrace (prefixWord ++ tailWord_1477951) baseStart_1477951 baseEnd_1477951 := by
    simpa [prefixWord, tailWord_1477951, baseEnd_1477951] using wordTrace_append hprefix tailTrace_1477951
  have hstable : (prefixWord ++ tailWord_1477951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477951).length < 2 ^ (prefixWord ++ tailWord_1477951).sum := by decide
  have hdescent : baseEnd_1477951 < baseStart_1477951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1477988 : List Nat := [2, 3, 1, 1, 3, 2, 3, 1, 2, 2, 3]
def baseStart_1477988 : Nat := 118140960795 + 1477988 * 2 ^ 59
def prefixEnd_1477988 : Nat := 4983230072969 + 3 ^ 40 * 1477988 * 2
def baseEnd_1477988 : Nat := 758918245577468598852863

theorem tailTrace_1477988 : CollatzResearch.WordTrace tailWord_1477988 prefixEnd_1477988 758918245577468598852863 := by
  unfold tailWord_1477988
  simp only [CollatzResearch.WordTrace]
  refine ⟨26953325484754685549653309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35937767313006247399537745 26953325484754685549653309)
  ·
    refine ⟨10107497056783007081119991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26953325484754685549653309 10107497056783007081119991)
    ·
      refine ⟨15161245585174510621679987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10107497056783007081119991 15161245585174510621679987)
      ·
        refine ⟨22741868377761765932519981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15161245585174510621679987 22741868377761765932519981)
        ·
          refine ⟨8528200641660662224694993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22741868377761765932519981 8528200641660662224694993)
          ·
            refine ⟨6396150481245496668521245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8528200641660662224694993 6396150481245496668521245)
            ·
              refine ⟨2398556430467061250695467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6396150481245496668521245 2398556430467061250695467)
              ·
                refine ⟨3597834645700591876043201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2398556430467061250695467 3597834645700591876043201)
                ·
                  refine ⟨2698375984275443907032401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3597834645700591876043201 2698375984275443907032401)
                  ·
                    refine ⟨2023781988206582930274301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2698375984275443907032401 2023781988206582930274301)
                    ·
                      refine ⟨758918245577468598852863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2023781988206582930274301 758918245577468598852863)
                      ·
                        rfl

theorem cell23_1477988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_1477988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1477988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1477988 prefixEnd_1477988 := by exact prefixLift 1477988
  have htrace : WordTrace (prefixWord ++ tailWord_1477988) baseStart_1477988 baseEnd_1477988 := by
    simpa [prefixWord, tailWord_1477988, baseEnd_1477988] using wordTrace_append hprefix tailTrace_1477988
  have hstable : (prefixWord ++ tailWord_1477988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1477988).length < 2 ^ (prefixWord ++ tailWord_1477988).sum := by decide
  have hdescent : baseEnd_1477988 < baseStart_1477988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1477988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478046 : List Nat := [4, 3, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_1478046 : Nat := 118140960795 + 1478046 * 2 ^ 59
def prefixEnd_1478046 : Nat := 4983230072969 + 3 ^ 40 * 1478046 * 2
def baseEnd_1478046 : Nat := 252982675818476457309199

theorem tailTrace_1478046 : CollatzResearch.WordTrace tailWord_1478046 prefixEnd_1478046 252982675818476457309199 := by
  unfold tailWord_1478046
  simp only [CollatzResearch.WordTrace]
  refine ⟨6738595800412405875614749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35939177602199498003278661 6738595800412405875614749)
  ·
    refine ⟨2526973425154652203355531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6738595800412405875614749 2526973425154652203355531)
    ·
      refine ⟨3790460137731978305033297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2526973425154652203355531 3790460137731978305033297)
      ·
        refine ⟨2842845103298983728774973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3790460137731978305033297 2842845103298983728774973)
        ·
          refine ⟨1066066913737118898290615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2842845103298983728774973 1066066913737118898290615)
          ·
            refine ⟨1599100370605678347435923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066066913737118898290615 1599100370605678347435923)
            ·
              refine ⟨2398650555908517521153885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1599100370605678347435923 2398650555908517521153885)
              ·
                refine ⟨899493958465694070432707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2398650555908517521153885 899493958465694070432707)
                ·
                  refine ⟨1349240937698541105649061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 899493958465694070432707 1349240937698541105649061)
                  ·
                    refine ⟨252982675818476457309199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1349240937698541105649061 252982675818476457309199)
                    ·
                      rfl

theorem cell23_1478046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_1478046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478046 prefixEnd_1478046 := by exact prefixLift 1478046
  have htrace : WordTrace (prefixWord ++ tailWord_1478046) baseStart_1478046 baseEnd_1478046 := by
    simpa [prefixWord, tailWord_1478046, baseEnd_1478046] using wordTrace_append hprefix tailTrace_1478046
  have hstable : (prefixWord ++ tailWord_1478046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478046).length < 2 ^ (prefixWord ++ tailWord_1478046).sum := by decide
  have hdescent : baseEnd_1478046 < baseStart_1478046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478051 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 6, 4]
def baseStart_1478051 : Nat := 118140960795 + 1478051 * 2 ^ 59
def prefixEnd_1478051 : Nat := 4983230072969 + 3 ^ 40 * 1478051 * 2
def baseEnd_1478051 : Nat := 252983531619567284121691

theorem tailTrace_1478051 : CollatzResearch.WordTrace tailWord_1478051 prefixEnd_1478051 252983531619567284121691 := by
  unfold tailWord_1478051
  simp only [CollatzResearch.WordTrace]
  refine ⟨53908948768281132858850007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35939299178854088572566671 53908948768281132858850007)
  ·
    refine ⟨80863423152421699288275011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53908948768281132858850007 80863423152421699288275011)
    ·
      refine ⟨121295134728632548932412517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80863423152421699288275011 121295134728632548932412517)
      ·
        refine ⟨22742837761618602924827347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121295134728632548932412517 22742837761618602924827347)
        ·
          refine ⟨34114256642427904387241021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22742837761618602924827347 34114256642427904387241021)
          ·
            refine ⟨12792846240910464145215383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34114256642427904387241021 12792846240910464145215383)
            ·
              refine ⟨19189269361365696217823075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12792846240910464145215383 19189269361365696217823075)
              ·
                refine ⟨28783904042048544326734613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19189269361365696217823075 28783904042048544326734613)
                ·
                  refine ⟨1349245501971025515315685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28783904042048544326734613 1349245501971025515315685)
                  ·
                    refine ⟨252983531619567284121691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1349245501971025515315685 252983531619567284121691)
                    ·
                      rfl

theorem cell23_1478051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6, 4].length) (baseStart_1478051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478051 prefixEnd_1478051 := by exact prefixLift 1478051
  have htrace : WordTrace (prefixWord ++ tailWord_1478051) baseStart_1478051 baseEnd_1478051 := by
    simpa [prefixWord, tailWord_1478051, baseEnd_1478051] using wordTrace_append hprefix tailTrace_1478051
  have hstable : (prefixWord ++ tailWord_1478051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478051).length < 2 ^ (prefixWord ++ tailWord_1478051).sum := by decide
  have hdescent : baseEnd_1478051 < baseStart_1478051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478069 : List Nat := [1, 3, 3, 2, 2, 2, 3, 2, 1, 1, 3]
def baseStart_1478069 : Nat := 118140960795 + 1478069 * 2 ^ 59
def prefixEnd_1478069 : Nat := 4983230072969 + 3 ^ 40 * 1478069 * 2
def baseEnd_1478069 : Nat := 758959837510482781939991

theorem tailTrace_1478069 : CollatzResearch.WordTrace tailWord_1478069 prefixEnd_1478069 758959837510482781939991 := by
  unfold tailWord_1478069
  simp only [CollatzResearch.WordTrace]
  refine ⟨53909605282215921933005261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35939736854810614622003507 53909605282215921933005261)
  ·
    refine ⟨20216101980830970724876973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53909605282215921933005261 20216101980830970724876973)
    ·
      refine ⟨7581038242811614021828865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20216101980830970724876973 7581038242811614021828865)
      ·
        refine ⟨5685778682108710516371649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7581038242811614021828865 5685778682108710516371649)
        ·
          refine ⟨4264334011581532887278737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5685778682108710516371649 4264334011581532887278737)
          ·
            refine ⟨3198250508686149665459053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4264334011581532887278737 3198250508686149665459053)
            ·
              refine ⟨1199343940757306124547145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3198250508686149665459053 1199343940757306124547145)
              ·
                refine ⟨899507955567979593410359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1199343940757306124547145 899507955567979593410359)
                ·
                  refine ⟨1349261933351969390115539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 899507955567979593410359 1349261933351969390115539)
                  ·
                    refine ⟨2023892900027954085173309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1349261933351969390115539 2023892900027954085173309)
                    ·
                      refine ⟨758959837510482781939991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2023892900027954085173309 758959837510482781939991)
                      ·
                        rfl

theorem cell23_1478069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_1478069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478069 prefixEnd_1478069 := by exact prefixLift 1478069
  have htrace : WordTrace (prefixWord ++ tailWord_1478069) baseStart_1478069 baseEnd_1478069 := by
    simpa [prefixWord, tailWord_1478069, baseEnd_1478069] using wordTrace_append hprefix tailTrace_1478069
  have hstable : (prefixWord ++ tailWord_1478069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478069).length < 2 ^ (prefixWord ++ tailWord_1478069).sum := by decide
  have hdescent : baseEnd_1478069 < baseStart_1478069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478078 : List Nat := [4, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3]
def baseStart_1478078 : Nat := 118140960795 + 1478078 * 2 ^ 59
def prefixEnd_1478078 : Nat := 4983230072969 + 3 ^ 40 * 1478078 * 2
def baseEnd_1478078 : Nat := 758964458836373246727449

theorem tailTrace_1478078 : CollatzResearch.WordTrace tailWord_1478078 prefixEnd_1478078 758964458836373246727449 := by
  unfold tailWord_1478078
  simp only [CollatzResearch.WordTrace]
  refine ⟨6738741692397914558760361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35939955692788877646721925 6738741692397914558760361)
  ·
    refine ⟨5054056269298435919070271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6738741692397914558760361 5054056269298435919070271)
    ·
      refine ⟨7581084403947653878605407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5054056269298435919070271 7581084403947653878605407)
      ·
        refine ⟨11371626605921480817908111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7581084403947653878605407 11371626605921480817908111)
        ·
          refine ⟨17057439908882221226862167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11371626605921480817908111 17057439908882221226862167)
          ·
            refine ⟨25586159863323331840293251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17057439908882221226862167 25586159863323331840293251)
            ·
              refine ⟨38379239794984997760439877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25586159863323331840293251 38379239794984997760439877)
              ·
                refine ⟨7196107461559687080082477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38379239794984997760439877 7196107461559687080082477)
                ·
                  refine ⟨2698540298084882655030929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7196107461559687080082477 2698540298084882655030929)
                  ·
                    refine ⟨2023905223563661991273197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2698540298084882655030929 2023905223563661991273197)
                    ·
                      refine ⟨758964458836373246727449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2023905223563661991273197 758964458836373246727449)
                      ·
                        rfl

theorem cell23_1478078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_1478078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478078 prefixEnd_1478078 := by exact prefixLift 1478078
  have htrace : WordTrace (prefixWord ++ tailWord_1478078) baseStart_1478078 baseEnd_1478078 := by
    simpa [prefixWord, tailWord_1478078, baseEnd_1478078] using wordTrace_append hprefix tailTrace_1478078
  have hstable : (prefixWord ++ tailWord_1478078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478078).length < 2 ^ (prefixWord ++ tailWord_1478078).sum := by decide
  have hdescent : baseEnd_1478078 < baseStart_1478078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478141 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 1, 8]
def baseStart_1478141 : Nat := 118140960795 + 1478141 * 2 ^ 59
def prefixEnd_1478141 : Nat := 4983230072969 + 3 ^ 40 * 1478141 * 2
def baseEnd_1478141 : Nat := 252998936039202166746553

theorem tailTrace_1478141 : CollatzResearch.WordTrace tailWord_1478141 prefixEnd_1478141 252998936039202166746553 := by
  unfold tailWord_1478141
  simp only [CollatzResearch.WordTrace]
  refine ⟨53912231337955078229626277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35941487558636718819750851 53912231337955078229626277)
  ·
    refine ⟨10108543375866577168054927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53912231337955078229626277 10108543375866577168054927)
    ·
      refine ⟨15162815063799865752082391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10108543375866577168054927 15162815063799865752082391)
      ·
        refine ⟨22744222595699798628123587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15162815063799865752082391 22744222595699798628123587)
        ·
          refine ⟨34116333893549697942185381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22744222595699798628123587 34116333893549697942185381)
          ·
            refine ⟨6396812605040568364159759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34116333893549697942185381 6396812605040568364159759)
            ·
              refine ⟨9595218907560852546239639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6396812605040568364159759 9595218907560852546239639)
              ·
                refine ⟨14392828361341278819359459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9595218907560852546239639 14392828361341278819359459)
                ·
                  refine ⟨21589242542011918229039189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14392828361341278819359459 21589242542011918229039189)
                  ·
                    refine ⟨252998936039202166746553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21589242542011918229039189 252998936039202166746553)
                    ·
                      rfl

theorem cell23_1478141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_1478141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478141 prefixEnd_1478141 := by exact prefixLift 1478141
  have htrace : WordTrace (prefixWord ++ tailWord_1478141) baseStart_1478141 baseEnd_1478141 := by
    simpa [prefixWord, tailWord_1478141, baseEnd_1478141] using wordTrace_append hprefix tailTrace_1478141
  have hstable : (prefixWord ++ tailWord_1478141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478141).length < 2 ^ (prefixWord ++ tailWord_1478141).sum := by decide
  have hdescent : baseEnd_1478141 < baseStart_1478141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478161 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 4]
def baseStart_1478161 : Nat := 118140960795 + 1478161 * 2 ^ 59
def prefixEnd_1478161 : Nat := 4983230072969 + 3 ^ 40 * 1478161 * 2
def baseEnd_1478161 : Nat := 759007077730696421989567

theorem tailTrace_1478161 : CollatzResearch.WordTrace tailWord_1478161 prefixEnd_1478161 759007077730696421989567 := by
  unfold tailWord_1478161
  simp only [CollatzResearch.WordTrace]
  refine ⟨53912960797882621645354337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35941973865255081096902891 53912960797882621645354337)
  ·
    refine ⟨40434720598411966234015753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53912960797882621645354337 40434720598411966234015753)
    ·
      refine ⟨30326040448808974675511815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40434720598411966234015753 30326040448808974675511815)
      ·
        refine ⟨45489060673213462013267723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30326040448808974675511815 45489060673213462013267723)
        ·
          refine ⟨68233591009820193019901585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45489060673213462013267723 68233591009820193019901585)
          ·
            refine ⟨51175193257365144764926189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68233591009820193019901585 51175193257365144764926189)
            ·
              refine ⟨19190697471511929286847321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51175193257365144764926189 19190697471511929286847321)
              ·
                refine ⟨14393023103633946965135491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19190697471511929286847321 14393023103633946965135491)
                ·
                  refine ⟨21589534655450920447703237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14393023103633946965135491 21589534655450920447703237)
                  ·
                    refine ⟨4048037747897047583944357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21589534655450920447703237 4048037747897047583944357)
                    ·
                      refine ⟨759007077730696421989567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4048037747897047583944357 759007077730696421989567)
                      ·
                        rfl

theorem cell23_1478161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_1478161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478161 prefixEnd_1478161 := by exact prefixLift 1478161
  have htrace : WordTrace (prefixWord ++ tailWord_1478161) baseStart_1478161 baseEnd_1478161 := by
    simpa [prefixWord, tailWord_1478161, baseEnd_1478161] using wordTrace_append hprefix tailTrace_1478161
  have hstable : (prefixWord ++ tailWord_1478161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478161).length < 2 ^ (prefixWord ++ tailWord_1478161).sum := by decide
  have hdescent : baseEnd_1478161 < baseStart_1478161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478165 : List Nat := [1, 3, 2, 1, 3, 2, 2, 2, 1, 4, 2]
def baseStart_1478165 : Nat := 118140960795 + 1478165 * 2 ^ 59
def prefixEnd_1478165 : Nat := 4983230072969 + 3 ^ 40 * 1478165 * 2
def baseEnd_1478165 : Nat := 759009131653314406339549

theorem tailTrace_1478165 : CollatzResearch.WordTrace tailWord_1478165 prefixEnd_1478165 759009131653314406339549 := by
  unfold tailWord_1478165
  simp only [CollatzResearch.WordTrace]
  refine ⟨53913106689868130328499949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35942071126578753552333299 53913106689868130328499949)
  ·
    refine ⟨20217415008700548873187481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53913106689868130328499949 20217415008700548873187481)
    ·
      refine ⟨15163061256525411654890611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20217415008700548873187481 15163061256525411654890611)
      ·
        refine ⟨22744591884788117482335917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15163061256525411654890611 22744591884788117482335917)
        ·
          refine ⟨8529221956795544055875969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22744591884788117482335917 8529221956795544055875969)
          ·
            refine ⟨6396916467596658041906977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8529221956795544055875969 6396916467596658041906977)
            ·
              refine ⟨4797687350697493531430233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6396916467596658041906977 4797687350697493531430233)
              ·
                refine ⟨3598265513023120148572675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4797687350697493531430233 3598265513023120148572675)
                ·
                  refine ⟨5397398269534680222859013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3598265513023120148572675 5397398269534680222859013)
                  ·
                    refine ⟨1012012175537752541786065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5397398269534680222859013 1012012175537752541786065)
                    ·
                      refine ⟨759009131653314406339549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1012012175537752541786065 759009131653314406339549)
                      ·
                        rfl

theorem cell23_1478165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 4, 2].length) (baseStart_1478165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478165 prefixEnd_1478165 := by exact prefixLift 1478165
  have htrace : WordTrace (prefixWord ++ tailWord_1478165) baseStart_1478165 baseEnd_1478165 := by
    simpa [prefixWord, tailWord_1478165, baseEnd_1478165] using wordTrace_append hprefix tailTrace_1478165
  have hstable : (prefixWord ++ tailWord_1478165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478165).length < 2 ^ (prefixWord ++ tailWord_1478165).sum := by decide
  have hdescent : baseEnd_1478165 < baseStart_1478165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478178 : List Nat := [3, 3, 1, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_1478178 : Nat := 118140960795 + 1478178 * 2 ^ 59
def prefixEnd_1478178 : Nat := 4983230072969 + 3 ^ 40 * 1478178 * 2
def baseEnd_1478178 : Nat := 759015806901822855476989

theorem tailTrace_1478178 : CollatzResearch.WordTrace tailWord_1478178 prefixEnd_1478178 759015806901822855476989 := by
  unfold tailWord_1478178
  simp only [CollatzResearch.WordTrace]
  refine ⟨13478395209705258387180797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35942387225880689032482125 13478395209705258387180797)
  ·
    refine ⟨5054398203639471895192799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13478395209705258387180797 5054398203639471895192799)
    ·
      refine ⟨7581597305459207842789199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5054398203639471895192799 7581597305459207842789199)
      ·
        refine ⟨11372395958188811764183799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7581597305459207842789199 11372395958188811764183799)
        ·
          refine ⟨17058593937283217646275699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11372395958188811764183799 17058593937283217646275699)
          ·
            refine ⟨25587890905924826469413549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17058593937283217646275699 25587890905924826469413549)
            ·
              refine ⟨9595459089721809926030081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25587890905924826469413549 9595459089721809926030081)
              ·
                refine ⟨7196594317291357444522561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9595459089721809926030081 7196594317291357444522561)
                ·
                  refine ⟨5397445737968518083391921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7196594317291357444522561 5397445737968518083391921)
                  ·
                    refine ⟨4048084303476388562543941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5397445737968518083391921 4048084303476388562543941)
                    ·
                      refine ⟨759015806901822855476989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4048084303476388562543941 759015806901822855476989)
                      ·
                        rfl

theorem cell23_1478178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_1478178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478178 prefixEnd_1478178 := by exact prefixLift 1478178
  have htrace : WordTrace (prefixWord ++ tailWord_1478178) baseStart_1478178 baseEnd_1478178 := by
    simpa [prefixWord, tailWord_1478178, baseEnd_1478178] using wordTrace_append hprefix tailTrace_1478178
  have hstable : (prefixWord ++ tailWord_1478178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478178).length < 2 ^ (prefixWord ++ tailWord_1478178).sum := by decide
  have hdescent : baseEnd_1478178 < baseStart_1478178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478199 : List Nat := [1, 1, 3, 1, 2, 5, 3, 1, 2, 2, 2]
def baseStart_1478199 : Nat := 118140960795 + 1478199 * 2 ^ 59
def prefixEnd_1478199 : Nat := 4983230072969 + 3 ^ 40 * 1478199 * 2
def baseEnd_1478199 : Nat := 759026589995567273314393

theorem tailTrace_1478199 : CollatzResearch.WordTrace tailWord_1478199 prefixEnd_1478199 759026589995567273314393 := by
  unfold tailWord_1478199
  simp only [CollatzResearch.WordTrace]
  refine ⟨53914346771744954135237651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35942897847829969423491767 53914346771744954135237651)
  ·
    refine ⟨80871520157617431202856477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53914346771744954135237651 80871520157617431202856477)
    ·
      refine ⟨30326820059106536701071179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80871520157617431202856477 30326820059106536701071179)
      ·
        refine ⟨45490230088659805051606769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30326820059106536701071179 45490230088659805051606769)
        ·
          refine ⟨34117672566494853788705077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45490230088659805051606769 34117672566494853788705077)
          ·
            refine ⟨3198531803108892542691101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34117672566494853788705077 3198531803108892542691101)
            ·
              refine ⟨1199449426165834703509163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3198531803108892542691101 1199449426165834703509163)
              ·
                refine ⟨1799174139248752055263745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1199449426165834703509163 1799174139248752055263745)
                ·
                  refine ⟨1349380604436564041447809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1799174139248752055263745 1349380604436564041447809)
                  ·
                    refine ⟨1012035453327423031085857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1349380604436564041447809 1012035453327423031085857)
                    ·
                      refine ⟨759026589995567273314393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1012035453327423031085857 759026589995567273314393)
                      ·
                        rfl

theorem cell23_1478199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 2, 2, 2].length) (baseStart_1478199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478199 prefixEnd_1478199 := by exact prefixLift 1478199
  have htrace : WordTrace (prefixWord ++ tailWord_1478199) baseStart_1478199 baseEnd_1478199 := by
    simpa [prefixWord, tailWord_1478199, baseEnd_1478199] using wordTrace_append hprefix tailTrace_1478199
  have hstable : (prefixWord ++ tailWord_1478199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478199).length < 2 ^ (prefixWord ++ tailWord_1478199).sum := by decide
  have hdescent : baseEnd_1478199 < baseStart_1478199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478211 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 5]
def baseStart_1478211 : Nat := 118140960795 + 1478211 * 2 ^ 59
def prefixEnd_1478211 : Nat := 4983230072969 + 3 ^ 40 * 1478211 * 2
def baseEnd_1478211 : Nat := 759032751763421226364337

theorem tailTrace_1478211 : CollatzResearch.WordTrace tailWord_1478211 prefixEnd_1478211 759032751763421226364337 := by
  unfold tailWord_1478211
  simp only [CollatzResearch.WordTrace]
  refine ⟨53914784447701480184674487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35943189631800986789782991 53914784447701480184674487)
  ·
    refine ⟨80872176671552220277011731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53914784447701480184674487 80872176671552220277011731)
    ·
      refine ⟨121308265007328330415517597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80872176671552220277011731 121308265007328330415517597)
      ·
        refine ⟨45490599377748123905819099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121308265007328330415517597 45490599377748123905819099)
        ·
          refine ⟨68235899066622185858728649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45490599377748123905819099 68235899066622185858728649)
          ·
            refine ⟨51176924299966639394046487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68235899066622185858728649 51176924299966639394046487)
            ·
              refine ⟨76765386449949959091069731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51176924299966639394046487 76765386449949959091069731)
              ·
                refine ⟨115148079674924938636604597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76765386449949959091069731 115148079674924938636604597)
                ·
                  refine ⟨10795132469524212997181681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115148079674924938636604597 10795132469524212997181681)
                  ·
                    refine ⟨8096349352143159747886261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10795132469524212997181681 8096349352143159747886261)
                    ·
                      refine ⟨759032751763421226364337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8096349352143159747886261 759032751763421226364337)
                      ·
                        rfl

theorem cell23_1478211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_1478211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478211 prefixEnd_1478211 := by exact prefixLift 1478211
  have htrace : WordTrace (prefixWord ++ tailWord_1478211) baseStart_1478211 baseEnd_1478211 := by
    simpa [prefixWord, tailWord_1478211, baseEnd_1478211] using wordTrace_append hprefix tailTrace_1478211
  have hstable : (prefixWord ++ tailWord_1478211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478211).length < 2 ^ (prefixWord ++ tailWord_1478211).sum := by decide
  have hdescent : baseEnd_1478211 < baseStart_1478211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478218 : List Nat := [3, 1, 2, 1, 1, 3, 2, 3, 2, 5]
def baseStart_1478218 : Nat := 118140960795 + 1478218 * 2 ^ 59
def prefixEnd_1478218 : Nat := 4983230072969 + 3 ^ 40 * 1478218 * 2
def baseEnd_1478218 : Nat := 253012115376000899658935

theorem tailTrace_1478218 : CollatzResearch.WordTrace tailWord_1478218 prefixEnd_1478218 253012115376000899658935 := by
  unfold tailWord_1478218
  simp only [CollatzResearch.WordTrace]
  refine ⟨13478759939669030095044827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35943359839117413586786205 13478759939669030095044827)
  ·
    refine ⟨20218139909503545142567241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13478759939669030095044827 20218139909503545142567241)
    ·
      refine ⟨15163604932127658856925431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20218139909503545142567241 15163604932127658856925431)
      ·
        refine ⟨22745407398191488285388147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15163604932127658856925431 22745407398191488285388147)
        ·
          refine ⟨34118111097287232428082221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22745407398191488285388147 34118111097287232428082221)
          ·
            refine ⟨12794291661482712160530833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34118111097287232428082221 12794291661482712160530833)
            ·
              refine ⟨9595718746112034120398125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12794291661482712160530833 9595718746112034120398125)
              ·
                refine ⟨3598394529792012795149297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9595718746112034120398125 3598394529792012795149297)
                ·
                  refine ⟨2698795897344009596361973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3598394529792012795149297 2698795897344009596361973)
                  ·
                    refine ⟨253012115376000899658935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2698795897344009596361973 253012115376000899658935)
                    ·
                      rfl

theorem cell23_1478218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_1478218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478218 prefixEnd_1478218 := by exact prefixLift 1478218
  have htrace : WordTrace (prefixWord ++ tailWord_1478218) baseStart_1478218 baseEnd_1478218 := by
    simpa [prefixWord, tailWord_1478218, baseEnd_1478218] using wordTrace_append hprefix tailTrace_1478218
  have hstable : (prefixWord ++ tailWord_1478218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478218).length < 2 ^ (prefixWord ++ tailWord_1478218).sum := by decide
  have hdescent : baseEnd_1478218 < baseStart_1478218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478228 : List Nat := [2, 4, 1, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_1478228 : Nat := 118140960795 + 1478228 * 2 ^ 59
def prefixEnd_1478228 : Nat := 4983230072969 + 3 ^ 40 * 1478228 * 2
def baseEnd_1478228 : Nat := 759041480934547659851759

theorem tailTrace_1478228 : CollatzResearch.WordTrace tailWord_1478228 prefixEnd_1478228 759041480934547659851759 := by
  unfold tailWord_1478228
  simp only [CollatzResearch.WordTrace]
  refine ⟨26957702244319946044021669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35943602992426594725362225 26957702244319946044021669)
  ·
    refine ⟨5054569170809989883254063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26957702244319946044021669 5054569170809989883254063)
    ·
      refine ⟨7581853756214984824881095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5054569170809989883254063 7581853756214984824881095)
      ·
        refine ⟨11372780634322477237321643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7581853756214984824881095 11372780634322477237321643)
        ·
          refine ⟨17059170951483715855982465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11372780634322477237321643 17059170951483715855982465)
          ·
            refine ⟨12794378213612786891986849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17059170951483715855982465 12794378213612786891986849)
            ·
              refine ⟨9595783660209590168990137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12794378213612786891986849 9595783660209590168990137)
              ·
                refine ⟨7196837745157192626742603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9595783660209590168990137 7196837745157192626742603)
                ·
                  refine ⟨10795256617735788940113905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7196837745157192626742603 10795256617735788940113905)
                  ·
                    refine ⟨8096442463301841705085429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10795256617735788940113905 8096442463301841705085429)
                    ·
                      refine ⟨759041480934547659851759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8096442463301841705085429 759041480934547659851759)
                      ·
                        rfl

theorem cell23_1478228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_1478228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478228 prefixEnd_1478228 := by exact prefixLift 1478228
  have htrace : WordTrace (prefixWord ++ tailWord_1478228) baseStart_1478228 baseEnd_1478228 := by
    simpa [prefixWord, tailWord_1478228, baseEnd_1478228] using wordTrace_append hprefix tailTrace_1478228
  have hstable : (prefixWord ++ tailWord_1478228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478228).length < 2 ^ (prefixWord ++ tailWord_1478228).sum := by decide
  have hdescent : baseEnd_1478228 < baseStart_1478228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478251 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 6]
def baseStart_1478251 : Nat := 118140960795 + 1478251 * 2 ^ 59
def prefixEnd_1478251 : Nat := 4983230072969 + 3 ^ 40 * 1478251 * 2
def baseEnd_1478251 : Nat := 759053290989601069864153

theorem tailTrace_1478251 : CollatzResearch.WordTrace tailWord_1478251 prefixEnd_1478251 759053290989601069864153 := by
  unfold tailWord_1478251
  simp only [CollatzResearch.WordTrace]
  refine ⟨53916243367556567016130607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35944162245037711344087071 53916243367556567016130607)
  ·
    refine ⟨80874365051334850524195911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53916243367556567016130607 80874365051334850524195911)
    ·
      refine ⟨121311547577002275786293867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80874365051334850524195911 121311547577002275786293867)
      ·
        refine ⟨181967321365503413679440801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121311547577002275786293867 181967321365503413679440801)
        ·
          refine ⟨136475491024127560259580601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181967321365503413679440801 136475491024127560259580601)
          ·
            refine ⟨102356618268095670194685451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136475491024127560259580601 102356618268095670194685451)
            ·
              refine ⟨153534927402143505292028177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102356618268095670194685451 153534927402143505292028177)
              ·
                refine ⟨115151195551607628969021133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153534927402143505292028177 115151195551607628969021133)
                ·
                  refine ⟨43181698331852860863382925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115151195551607628969021133 43181698331852860863382925)
                  ·
                    refine ⟨16193136874444822823768597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43181698331852860863382925 16193136874444822823768597)
                    ·
                      refine ⟨759053290989601069864153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16193136874444822823768597 759053290989601069864153)
                      ·
                        rfl

theorem cell23_1478251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 6].length) (baseStart_1478251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478251 prefixEnd_1478251 := by exact prefixLift 1478251
  have htrace : WordTrace (prefixWord ++ tailWord_1478251) baseStart_1478251 baseEnd_1478251 := by
    simpa [prefixWord, tailWord_1478251, baseEnd_1478251] using wordTrace_append hprefix tailTrace_1478251
  have hstable : (prefixWord ++ tailWord_1478251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478251).length < 2 ^ (prefixWord ++ tailWord_1478251).sum := by decide
  have hdescent : baseEnd_1478251 < baseStart_1478251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478295 : List Nat := [1, 1, 3, 3, 2, 3, 2, 2, 6]
def baseStart_1478295 : Nat := 118140960795 + 1478295 * 2 ^ 59
def prefixEnd_1478295 : Nat := 4983230072969 + 3 ^ 40 * 1478295 * 2
def baseEnd_1478295 : Nat := 84341764904266544190439

theorem tailTrace_1478295 : CollatzResearch.WordTrace tailWord_1478295 prefixEnd_1478295 84341764904266544190439 := by
  unfold tailWord_1478295
  simp only [CollatzResearch.WordTrace]
  refine ⟨53917848179397162530732339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35945232119598108353821559 53917848179397162530732339)
  ·
    refine ⟨80876772269095743796098509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53917848179397162530732339 80876772269095743796098509)
    ·
      refine ⟨30328789600910903923536941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80876772269095743796098509 30328789600910903923536941)
      ·
        refine ⟨11373296100341588971326353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30328789600910903923536941 11373296100341588971326353)
        ·
          refine ⟨8529972075256191728494765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11373296100341588971326353 8529972075256191728494765)
          ·
            refine ⟨3198739528221071898185537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8529972075256191728494765 3198739528221071898185537)
            ·
              refine ⟨2399054646165803923639153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3198739528221071898185537 2399054646165803923639153)
              ·
                refine ⟨1799290984624352942729365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2399054646165803923639153 1799290984624352942729365)
                ·
                  refine ⟨84341764904266544190439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1799290984624352942729365 84341764904266544190439)
                  ·
                    rfl

theorem cell23_1478295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 6].length) (baseStart_1478295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478295 prefixEnd_1478295 := by exact prefixLift 1478295
  have htrace : WordTrace (prefixWord ++ tailWord_1478295) baseStart_1478295 baseEnd_1478295 := by
    simpa [prefixWord, tailWord_1478295, baseEnd_1478295] using wordTrace_append hprefix tailTrace_1478295
  have hstable : (prefixWord ++ tailWord_1478295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478295).length < 2 ^ (prefixWord ++ tailWord_1478295).sum := by decide
  have hdescent : baseEnd_1478295 < baseStart_1478295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478326 : List Nat := [5, 1, 3, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_1478326 : Nat := 118140960795 + 1478326 * 2 ^ 59
def prefixEnd_1478326 : Nat := 4983230072969 + 3 ^ 40 * 1478326 * 2
def baseEnd_1478326 : Nat := 759091802038688276426309

theorem tailTrace_1478326 : CollatzResearch.WordTrace tailWord_1478326 prefixEnd_1478326 759091802038688276426309 := by
  unfold tailWord_1478326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3369936177642803426569427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35945985894856569883407221 3369936177642803426569427)
  ·
    refine ⟨5054904266464205139854141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3369936177642803426569427 5054904266464205139854141)
    ·
      refine ⟨1895589099924076927445303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5054904266464205139854141 1895589099924076927445303)
      ·
        refine ⟨2843383649886115391167955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1895589099924076927445303 2843383649886115391167955)
        ·
          refine ⟨4265075474829173086751933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2843383649886115391167955 4265075474829173086751933)
          ·
            refine ⟨1599403303060939907531975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4265075474829173086751933 1599403303060939907531975)
            ·
              refine ⟨2399104954591409861297963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1599403303060939907531975 2399104954591409861297963)
              ·
                refine ⟨3598657431887114791946945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2399104954591409861297963 3598657431887114791946945)
                ·
                  refine ⟨2698993073915336093960209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3598657431887114791946945 2698993073915336093960209)
                  ·
                    refine ⟨2024244805436502070470157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2698993073915336093960209 2024244805436502070470157)
                    ·
                      refine ⟨759091802038688276426309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2024244805436502070470157 759091802038688276426309)
                      ·
                        rfl

theorem cell23_1478326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_1478326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478326 prefixEnd_1478326 := by exact prefixLift 1478326
  have htrace : WordTrace (prefixWord ++ tailWord_1478326) baseStart_1478326 baseEnd_1478326 := by
    simpa [prefixWord, tailWord_1478326, baseEnd_1478326] using wordTrace_append hprefix tailTrace_1478326
  have hstable : (prefixWord ++ tailWord_1478326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478326).length < 2 ^ (prefixWord ++ tailWord_1478326).sum := by decide
  have hdescent : baseEnd_1478326 < baseStart_1478326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478332 : List Nat := [2, 2, 2, 3, 1, 3, 1, 1, 1, 5, 2]
def baseStart_1478332 : Nat := 118140960795 + 1478332 * 2 ^ 59
def prefixEnd_1478332 : Nat := 4983230072969 + 3 ^ 40 * 1478332 * 2
def baseEnd_1478332 : Nat := 759094882922615252951281

theorem tailTrace_1478332 : CollatzResearch.WordTrace tailWord_1478332 prefixEnd_1478332 759094882922615252951281 := by
  unfold tailWord_1478332
  simp only [CollatzResearch.WordTrace]
  refine ⟨26959598840131558924914625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35946131786842078566552833 26959598840131558924914625)
  ·
    refine ⟨20219699130098669193685969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26959598840131558924914625 20219699130098669193685969)
    ·
      refine ⟨15164774347574001895264477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20219699130098669193685969 15164774347574001895264477)
      ·
        refine ⟨5686790380340250710724179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15164774347574001895264477 5686790380340250710724179)
        ·
          refine ⟨8530185570510376066086269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5686790380340250710724179 8530185570510376066086269)
          ·
            refine ⟨3198819588941391024782351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8530185570510376066086269 3198819588941391024782351)
            ·
              refine ⟨4798229383412086537173527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3198819588941391024782351 4798229383412086537173527)
              ·
                refine ⟨7197344075118129805760291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4798229383412086537173527 7197344075118129805760291)
                ·
                  refine ⟨10796016112677194708640437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7197344075118129805760291 10796016112677194708640437)
                  ·
                    refine ⟨1012126510563487003935041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10796016112677194708640437 1012126510563487003935041)
                    ·
                      refine ⟨759094882922615252951281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1012126510563487003935041 759094882922615252951281)
                      ·
                        rfl

theorem cell23_1478332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_1478332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478332 prefixEnd_1478332 := by exact prefixLift 1478332
  have htrace : WordTrace (prefixWord ++ tailWord_1478332) baseStart_1478332 baseEnd_1478332 := by
    simpa [prefixWord, tailWord_1478332, baseEnd_1478332] using wordTrace_append hprefix tailTrace_1478332
  have hstable : (prefixWord ++ tailWord_1478332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478332).length < 2 ^ (prefixWord ++ tailWord_1478332).sum := by decide
  have hdescent : baseEnd_1478332 < baseStart_1478332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478356 : List Nat := [2, 4, 1, 3, 1, 1, 2, 4, 1, 1, 3]
def baseStart_1478356 : Nat := 118140960795 + 1478356 * 2 ^ 59
def prefixEnd_1478356 : Nat := 4983230072969 + 3 ^ 40 * 1478356 * 2
def baseEnd_1478356 : Nat := 759107206458323159051171

theorem tailTrace_1478356 : CollatzResearch.WordTrace tailWord_1478356 prefixEnd_1478356 759107206458323159051171 := by
  unfold tailWord_1478356
  simp only [CollatzResearch.WordTrace]
  refine ⟨26960036516088084974351461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35946715354784113299135281 26960036516088084974351461)
  ·
    refine ⟨5055006846766515932690899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26960036516088084974351461 5055006846766515932690899)
    ·
      refine ⟨7582510270149773899036349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5055006846766515932690899 7582510270149773899036349)
      ·
        refine ⟨2843441351306165212138631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7582510270149773899036349 2843441351306165212138631)
        ·
          refine ⟨4265162026959247818207947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2843441351306165212138631 4265162026959247818207947)
          ·
            refine ⟨6397743040438871727311921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4265162026959247818207947 6397743040438871727311921)
            ·
              refine ⟨4798307280329153795483941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6397743040438871727311921 4798307280329153795483941)
              ·
                refine ⟨899682615061716336653239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4798307280329153795483941 899682615061716336653239)
                ·
                  refine ⟨1349523922592574504979859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 899682615061716336653239 1349523922592574504979859)
                  ·
                    refine ⟨2024285883888861757469789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1349523922592574504979859 2024285883888861757469789)
                    ·
                      refine ⟨759107206458323159051171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2024285883888861757469789 759107206458323159051171)
                      ·
                        rfl

theorem cell23_1478356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_1478356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478356 prefixEnd_1478356 := by exact prefixLift 1478356
  have htrace : WordTrace (prefixWord ++ tailWord_1478356) baseStart_1478356 baseEnd_1478356 := by
    simpa [prefixWord, tailWord_1478356, baseEnd_1478356] using wordTrace_append hprefix tailTrace_1478356
  have hstable : (prefixWord ++ tailWord_1478356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478356).length < 2 ^ (prefixWord ++ tailWord_1478356).sum := by decide
  have hdescent : baseEnd_1478356 < baseStart_1478356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478385 : List Nat := [1, 2, 2, 2, 2, 3, 4, 7]
def baseStart_1478385 : Nat := 118140960795 + 1478385 * 2 ^ 59
def prefixEnd_1478385 : Nat := 4983230072969 + 3 ^ 40 * 1478385 * 2
def baseEnd_1478385 : Nat := 28115633236937168355131

theorem tailTrace_1478385 : CollatzResearch.WordTrace tailWord_1478385 prefixEnd_1478385 28115633236937168355131 := by
  unfold tailWord_1478385
  simp only [CollatzResearch.WordTrace]
  refine ⟨53921130749071107901508609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35947420499380738601005739 53921130749071107901508609)
  ·
    refine ⟨40440848061803330926131457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53921130749071107901508609 40440848061803330926131457)
    ·
      refine ⟨30330636046352498194598593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40440848061803330926131457 30330636046352498194598593)
      ·
        refine ⟨22747977034764373645948945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30330636046352498194598593 22747977034764373645948945)
        ·
          refine ⟨17060982776073280234461709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22747977034764373645948945 17060982776073280234461709)
          ·
            refine ⟨6397868541027480087923141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17060982776073280234461709 6397868541027480087923141)
            ·
              refine ⟨1199600351442652516485589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6397868541027480087923141 1199600351442652516485589)
              ·
                refine ⟨28115633236937168355131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1199600351442652516485589 28115633236937168355131)
                ·
                  rfl

theorem cell23_1478385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 7].length) (baseStart_1478385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478385 prefixEnd_1478385 := by exact prefixLift 1478385
  have htrace : WordTrace (prefixWord ++ tailWord_1478385) baseStart_1478385 baseEnd_1478385 := by
    simpa [prefixWord, tailWord_1478385, baseEnd_1478385] using wordTrace_append hprefix tailTrace_1478385
  have hstable : (prefixWord ++ tailWord_1478385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478385).length < 2 ^ (prefixWord ++ tailWord_1478385).sum := by decide
  have hdescent : baseEnd_1478385 < baseStart_1478385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478412 : List Nat := [2, 2, 1, 2, 2, 1, 4, 1, 4, 1, 3]
def baseStart_1478412 : Nat := 118140960795 + 1478412 * 2 ^ 59
def prefixEnd_1478412 : Nat := 4983230072969 + 3 ^ 40 * 1478412 * 2
def baseEnd_1478412 : Nat := 759135961374974939950913

theorem tailTrace_1478412 : CollatzResearch.WordTrace tailWord_1478412 prefixEnd_1478412 759135961374974939950913 := by
  unfold tailWord_1478412
  simp only [CollatzResearch.WordTrace]
  refine ⟨26961057759986645756370745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35948077013315527675160993 26961057759986645756370745)
  ·
    refine ⟨20220793319989984317278059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26961057759986645756370745 20220793319989984317278059)
    ·
      refine ⟨30331189979984976475917089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20220793319989984317278059 30331189979984976475917089)
      ·
        refine ⟨22748392484988732356937817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30331189979984976475917089 22748392484988732356937817)
        ·
          refine ⟨17061294363741549267703363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22748392484988732356937817 17061294363741549267703363)
          ·
            refine ⟨25591941545612323901555045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17061294363741549267703363 25591941545612323901555045)
            ·
              refine ⟨4798489039802310731541571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25591941545612323901555045 4798489039802310731541571)
              ·
                refine ⟨7197733559703466097312357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4798489039802310731541571 7197733559703466097312357)
                ·
                  refine ⟨1349575042444399893246067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7197733559703466097312357 1349575042444399893246067)
                  ·
                    refine ⟨2024362563666599839869101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1349575042444399893246067 2024362563666599839869101)
                    ·
                      refine ⟨759135961374974939950913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2024362563666599839869101 759135961374974939950913)
                      ·
                        rfl

theorem cell23_1478412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_1478412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478412 prefixEnd_1478412 := by exact prefixLift 1478412
  have htrace : WordTrace (prefixWord ++ tailWord_1478412) baseStart_1478412 baseEnd_1478412 := by
    simpa [prefixWord, tailWord_1478412, baseEnd_1478412] using wordTrace_append hprefix tailTrace_1478412
  have hstable : (prefixWord ++ tailWord_1478412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478412).length < 2 ^ (prefixWord ++ tailWord_1478412).sum := by decide
  have hdescent : baseEnd_1478412 < baseStart_1478412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478430 : List Nat := [4, 3, 2, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_1478430 : Nat := 118140960795 + 1478430 * 2 ^ 59
def prefixEnd_1478430 : Nat := 4983230072969 + 3 ^ 40 * 1478430 * 2
def baseEnd_1478430 : Nat := 759145204026755869525831

theorem tailTrace_1478430 : CollatzResearch.WordTrace tailWord_1478430 prefixEnd_1478430 759145204026755869525831 := by
  unfold tailWord_1478430
  simp only [CollatzResearch.WordTrace]
  refine ⟨6740346504238510073362093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35948514689272053724597829 6740346504238510073362093)
  ·
    refine ⟨2527629939089441277510785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6740346504238510073362093 2527629939089441277510785)
    ·
      refine ⟨1895722454317080958133089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2527629939089441277510785 1895722454317080958133089)
      ·
        refine ⟨1421791840737810718599817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1895722454317080958133089 1421791840737810718599817)
        ·
          refine ⟨1066343880553358038949863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1421791840737810718599817 1066343880553358038949863)
          ·
            refine ⟨1599515820830037058424795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066343880553358038949863 1599515820830037058424795)
            ·
              refine ⟨2399273731245055587637193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1599515820830037058424795 2399273731245055587637193)
              ·
                refine ⟨1799455298433791690727895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2399273731245055587637193 1799455298433791690727895)
                ·
                  refine ⟨2699182947650687536091843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1799455298433791690727895 2699182947650687536091843)
                  ·
                    refine ⟨4048774421476031304137765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2699182947650687536091843 4048774421476031304137765)
                    ·
                      refine ⟨759145204026755869525831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4048774421476031304137765 759145204026755869525831)
                      ·
                        rfl

theorem cell23_1478430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_1478430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478430 prefixEnd_1478430 := by exact prefixLift 1478430
  have htrace : WordTrace (prefixWord ++ tailWord_1478430) baseStart_1478430 baseEnd_1478430 := by
    simpa [prefixWord, tailWord_1478430, baseEnd_1478430] using wordTrace_append hprefix tailTrace_1478430
  have hstable : (prefixWord ++ tailWord_1478430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478430).length < 2 ^ (prefixWord ++ tailWord_1478430).sum := by decide
  have hdescent : baseEnd_1478430 < baseStart_1478430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478456 : List Nat := [2, 1, 2, 1, 3, 4, 3, 1, 1, 3, 2]
def baseStart_1478456 : Nat := 118140960795 + 1478456 * 2 ^ 59
def prefixEnd_1478456 : Nat := 4983230072969 + 3 ^ 40 * 1478456 * 2
def baseEnd_1478456 : Nat := 759158554523772767800711

theorem tailTrace_1478456 : CollatzResearch.WordTrace tailWord_1478456 prefixEnd_1478456 759158554523772767800711 := by
  unfold tailWord_1478456
  simp only [CollatzResearch.WordTrace]
  refine ⟨26961860165906943513671611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35949146887875924684895481 26961860165906943513671611)
  ·
    refine ⟨40442790248860415270507417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26961860165906943513671611 40442790248860415270507417)
    ·
      refine ⟨30332092686645311452880563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40442790248860415270507417 30332092686645311452880563)
      ·
        refine ⟨45498139029967967179320845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30332092686645311452880563 45498139029967967179320845)
        ·
          refine ⟨17061802136237987692245317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45498139029967967179320845 17061802136237987692245317)
          ·
            refine ⟨3199087900544622692295997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17061802136237987692245317 3199087900544622692295997)
            ·
              refine ⟨1199657962704233509610999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3199087900544622692295997 1199657962704233509610999)
              ·
                refine ⟨1799486944056350264416499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1199657962704233509610999 1799486944056350264416499)
                ·
                  refine ⟨2699230416084525396624749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1799486944056350264416499 2699230416084525396624749)
                  ·
                    refine ⟨1012211406031697023734281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2699230416084525396624749 1012211406031697023734281)
                    ·
                      refine ⟨759158554523772767800711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1012211406031697023734281 759158554523772767800711)
                      ·
                        rfl

theorem cell23_1478456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 1, 3, 2].length) (baseStart_1478456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478456 prefixEnd_1478456 := by exact prefixLift 1478456
  have htrace : WordTrace (prefixWord ++ tailWord_1478456) baseStart_1478456 baseEnd_1478456 := by
    simpa [prefixWord, tailWord_1478456, baseEnd_1478456] using wordTrace_append hprefix tailTrace_1478456
  have hstable : (prefixWord ++ tailWord_1478456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478456).length < 2 ^ (prefixWord ++ tailWord_1478456).sum := by decide
  have hdescent : baseEnd_1478456 < baseStart_1478456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478482 : List Nat := [3, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_1478482 : Nat := 118140960795 + 1478482 * 2 ^ 59
def prefixEnd_1478482 : Nat := 4983230072969 + 3 ^ 40 * 1478482 * 2
def baseEnd_1478482 : Nat := 759171905020789666075591

theorem tailTrace_1478482 : CollatzResearch.WordTrace tailWord_1478482 prefixEnd_1478482 759171905020789666075591 := by
  unfold tailWord_1478482
  simp only [CollatzResearch.WordTrace]
  refine ⟨13481167157429923366947425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35949779086479795645193133 13481167157429923366947425)
  ·
    refine ⟨10110875368072442525210569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13481167157429923366947425 10110875368072442525210569)
    ·
      refine ⟨7583156526054331893907927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10110875368072442525210569 7583156526054331893907927)
      ·
        refine ⟨11374734789081497840861891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7583156526054331893907927 11374734789081497840861891)
        ·
          refine ⟨17062102183622246761292837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11374734789081497840861891 17062102183622246761292837)
          ·
            refine ⟨3199144159429171267742407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17062102183622246761292837 3199144159429171267742407)
            ·
              refine ⟨4798716239143756901613611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3199144159429171267742407 4798716239143756901613611)
              ·
                refine ⟨7198074358715635352420417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4798716239143756901613611 7198074358715635352420417)
                ·
                  refine ⟨5398555769036726514315313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7198074358715635352420417 5398555769036726514315313)
                  ·
                    refine ⟨4048916826777544885736485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5398555769036726514315313 4048916826777544885736485)
                    ·
                      refine ⟨759171905020789666075591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4048916826777544885736485 759171905020789666075591)
                      ·
                        rfl

theorem cell23_1478482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_1478482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478482 prefixEnd_1478482 := by exact prefixLift 1478482
  have htrace : WordTrace (prefixWord ++ tailWord_1478482) baseStart_1478482 baseEnd_1478482 := by
    simpa [prefixWord, tailWord_1478482, baseEnd_1478482] using wordTrace_append hprefix tailTrace_1478482
  have hstable : (prefixWord ++ tailWord_1478482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478482).length < 2 ^ (prefixWord ++ tailWord_1478482).sum := by decide
  have hdescent : baseEnd_1478482 < baseStart_1478482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478526 : List Nat := [4, 2, 3, 1, 1, 1, 2, 4, 5]
def baseStart_1478526 : Nat := 118140960795 + 1478526 * 2 ^ 59
def prefixEnd_1478526 : Nat := 4983230072969 + 3 ^ 40 * 1478526 * 2
def baseEnd_1478526 : Nat := 84354944241065277102821

theorem tailTrace_1478526 : CollatzResearch.WordTrace tailWord_1478526 prefixEnd_1478526 84354944241065277102821 := by
  unfold tailWord_1478526
  simp only [CollatzResearch.WordTrace]
  refine ⟨6740784180195036122798929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35950848961040192654927621 6740784180195036122798929)
  ·
    refine ⟨5055588135146277092099197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6740784180195036122798929 5055588135146277092099197)
    ·
      refine ⟨1895845550679853909537199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5055588135146277092099197 1895845550679853909537199)
      ·
        refine ⟨2843768326019780864305799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1895845550679853909537199 2843768326019780864305799)
        ·
          refine ⟨4265652489029671296458699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2843768326019780864305799 4265652489029671296458699)
          ·
            refine ⟨6398478733544506944688049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4265652489029671296458699 6398478733544506944688049)
            ·
              refine ⟨4798859050158380208516037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6398478733544506944688049 4798859050158380208516037)
              ·
                refine ⟨899786071904696289096757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4798859050158380208516037 899786071904696289096757)
                ·
                  refine ⟨84354944241065277102821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 899786071904696289096757 84354944241065277102821)
                  ·
                    rfl

theorem cell23_1478526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_1478526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478526 prefixEnd_1478526 := by exact prefixLift 1478526
  have htrace : WordTrace (prefixWord ++ tailWord_1478526) baseStart_1478526 baseEnd_1478526 := by
    simpa [prefixWord, tailWord_1478526, baseEnd_1478526] using wordTrace_append hprefix tailTrace_1478526
  have hstable : (prefixWord ++ tailWord_1478526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478526).length < 2 ^ (prefixWord ++ tailWord_1478526).sum := by decide
  have hdescent : baseEnd_1478526 < baseStart_1478526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478569 : List Nat := [1, 2, 1, 1, 1, 1, 4, 7, 1, 4]
def baseStart_1478569 : Nat := 118140960795 + 1478569 * 2 ^ 59
def prefixEnd_1478569 : Nat := 4983230072969 + 3 ^ 40 * 1478569 * 2
def baseEnd_1478569 : Nat := 253072192612576941895897

theorem tailTrace_1478569 : CollatzResearch.WordTrace tailWord_1478569 prefixEnd_1478569 253072192612576941895897 := by
  unfold tailWord_1478569
  simp only [CollatzResearch.WordTrace]
  refine ⟨53927841780404507326206761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35951894520269671550804507 53927841780404507326206761)
  ·
    refine ⟨40445881335303380494655071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53927841780404507326206761 40445881335303380494655071)
    ·
      refine ⟨60668822002955070741982607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40445881335303380494655071 60668822002955070741982607)
      ·
        refine ⟨91003233004432606112973911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60668822002955070741982607 91003233004432606112973911)
        ·
          refine ⟨136504849506648909169460867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91003233004432606112973911 136504849506648909169460867)
          ·
            refine ⟨204757274259973363754191301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136504849506648909169460867 204757274259973363754191301)
            ·
              refine ⟨38391988923745005703910869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 204757274259973363754191301 38391988923745005703910869)
              ·
                refine ⟨899812240400273571185411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 38391988923745005703910869 899812240400273571185411)
                ·
                  refine ⟨1349718360600410356778117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 899812240400273571185411 1349718360600410356778117)
                  ·
                    refine ⟨253072192612576941895897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1349718360600410356778117 253072192612576941895897)
                    ·
                      rfl

theorem cell23_1478569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7, 1, 4].length) (baseStart_1478569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478569 prefixEnd_1478569 := by exact prefixLift 1478569
  have htrace : WordTrace (prefixWord ++ tailWord_1478569) baseStart_1478569 baseEnd_1478569 := by
    simpa [prefixWord, tailWord_1478569, baseEnd_1478569] using wordTrace_append hprefix tailTrace_1478569
  have hstable : (prefixWord ++ tailWord_1478569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478569).length < 2 ^ (prefixWord ++ tailWord_1478569).sum := by decide
  have hdescent : baseEnd_1478569 < baseStart_1478569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478637 : List Nat := [1, 5, 1, 4, 1, 2, 2, 2, 1, 4]
def baseStart_1478637 : Nat := 118140960795 + 1478637 * 2 ^ 59
def prefixEnd_1478637 : Nat := 4983230072969 + 3 ^ 40 * 1478637 * 2
def baseEnd_1478637 : Nat := 253083831507412186545793

theorem tailTrace_1478637 : CollatzResearch.WordTrace tailWord_1478637 prefixEnd_1478637 253083831507412186545793 := by
  unfold tailWord_1478637
  simp only [CollatzResearch.WordTrace]
  refine ⟨53930321944158154939682165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35953547962772103293121443 53930321944158154939682165)
  ·
    refine ⟨5055967682264827025595203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53930321944158154939682165 5055967682264827025595203)
    ·
      refine ⟨7583951523397240538392805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5055967682264827025595203 7583951523397240538392805)
      ·
        refine ⟨1421990910636982600948651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7583951523397240538392805 1421990910636982600948651)
        ·
          refine ⟨2132986365955473901422977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1421990910636982600948651 2132986365955473901422977)
          ·
            refine ⟨1599739774466605426067233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2132986365955473901422977 1599739774466605426067233)
            ·
              refine ⟨1199804830849954069550425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1599739774466605426067233 1199804830849954069550425)
              ·
                refine ⟨899853623137465552162819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1199804830849954069550425 899853623137465552162819)
                ·
                  refine ⟨1349780434706198328244229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 899853623137465552162819 1349780434706198328244229)
                  ·
                    refine ⟨253083831507412186545793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1349780434706198328244229 253083831507412186545793)
                    ·
                      rfl

theorem cell23_1478637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_1478637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478637 prefixEnd_1478637 := by exact prefixLift 1478637
  have htrace : WordTrace (prefixWord ++ tailWord_1478637) baseStart_1478637 baseEnd_1478637 := by
    simpa [prefixWord, tailWord_1478637, baseEnd_1478637] using wordTrace_append hprefix tailTrace_1478637
  have hstable : (prefixWord ++ tailWord_1478637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478637).length < 2 ^ (prefixWord ++ tailWord_1478637).sum := by decide
  have hdescent : baseEnd_1478637 < baseStart_1478637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478652 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 3, 1, 5]
def baseStart_1478652 : Nat := 118140960795 + 1478652 * 2 ^ 59
def prefixEnd_1478652 : Nat := 4983230072969 + 3 ^ 40 * 1478652 * 2
def baseEnd_1478652 : Nat := 759259196732054000949809

theorem tailTrace_1478652 : CollatzResearch.WordTrace tailWord_1478652 prefixEnd_1478652 759259196732054000949809 := by
  unfold tailWord_1478652
  simp only [CollatzResearch.WordTrace]
  refine ⟨26965434519551906250739105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35953912692735875000985473 26965434519551906250739105)
  ·
    refine ⟨20224075889663929688054329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26965434519551906250739105 20224075889663929688054329)
    ·
      refine ⟨15168056917247947266040747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20224075889663929688054329 15168056917247947266040747)
      ·
        refine ⟨22752085375871920899061121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15168056917247947266040747 22752085375871920899061121)
        ·
          refine ⟨17064064031903940674295841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22752085375871920899061121 17064064031903940674295841)
          ·
            refine ⟨12798048023927955505721881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17064064031903940674295841 12798048023927955505721881)
            ·
              refine ⟨9598536017945966629291411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12798048023927955505721881 9598536017945966629291411)
              ·
                refine ⟨14397804026918949943937117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9598536017945966629291411 14397804026918949943937117)
                ·
                  refine ⟨5399176510094606228976419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14397804026918949943937117 5399176510094606228976419)
                  ·
                    refine ⟨8098764765141909343464629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5399176510094606228976419 8098764765141909343464629)
                    ·
                      refine ⟨759259196732054000949809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8098764765141909343464629 759259196732054000949809)
                      ·
                        rfl

theorem cell23_1478652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_1478652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478652 prefixEnd_1478652 := by exact prefixLift 1478652
  have htrace : WordTrace (prefixWord ++ tailWord_1478652) baseStart_1478652 baseEnd_1478652 := by
    simpa [prefixWord, tailWord_1478652, baseEnd_1478652] using wordTrace_append hprefix tailTrace_1478652
  have hstable : (prefixWord ++ tailWord_1478652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478652).length < 2 ^ (prefixWord ++ tailWord_1478652).sum := by decide
  have hdescent : baseEnd_1478652 < baseStart_1478652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478713 : List Nat := [1, 2, 1, 5, 4, 1, 1, 1, 1, 2, 4]
def baseStart_1478713 : Nat := 118140960795 + 1478713 * 2 ^ 59
def prefixEnd_1478713 : Nat := 4983230072969 + 3 ^ 40 * 1478713 * 2
def baseEnd_1478713 : Nat := 759290519051978262287029

theorem tailTrace_1478713 : CollatzResearch.WordTrace tailWord_1478713 prefixEnd_1478713 759290519051978262287029 := by
  unfold tailWord_1478713
  simp only [CollatzResearch.WordTrace]
  refine ⟨53933093891882819919448793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35955395927921879946299195 53933093891882819919448793)
  ·
    refine ⟨40449820418912114939586595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53933093891882819919448793 40449820418912114939586595)
    ·
      refine ⟨60674730628368172409379893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40449820418912114939586595 60674730628368172409379893)
      ·
        refine ⟨5688255996409516163379365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60674730628368172409379893 5688255996409516163379365)
        ·
          refine ⟨1066547999326784280633631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5688255996409516163379365 1066547999326784280633631)
          ·
            refine ⟨1599821998990176420950447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066547999326784280633631 1599821998990176420950447)
            ·
              refine ⟨2399732998485264631425671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1599821998990176420950447 2399732998485264631425671)
              ·
                refine ⟨3599599497727896947138507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2399732998485264631425671 3599599497727896947138507)
                ·
                  refine ⟨5399399246591845420707761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3599599497727896947138507 5399399246591845420707761)
                  ·
                    refine ⟨4049549434943884065530821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5399399246591845420707761 4049549434943884065530821)
                    ·
                      refine ⟨759290519051978262287029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4049549434943884065530821 759290519051978262287029)
                      ·
                        rfl

theorem cell23_1478713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_1478713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478713 prefixEnd_1478713 := by exact prefixLift 1478713
  have htrace : WordTrace (prefixWord ++ tailWord_1478713) baseStart_1478713 baseEnd_1478713 := by
    simpa [prefixWord, tailWord_1478713, baseEnd_1478713] using wordTrace_append hprefix tailTrace_1478713
  have hstable : (prefixWord ++ tailWord_1478713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478713).length < 2 ^ (prefixWord ++ tailWord_1478713).sum := by decide
  have hdescent : baseEnd_1478713 < baseStart_1478713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478732 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 1, 8]
def baseStart_1478732 : Nat := 118140960795 + 1478732 * 2 ^ 59
def prefixEnd_1478732 : Nat := 4983230072969 + 3 ^ 40 * 1478732 * 2
def baseEnd_1478732 : Nat := 253100091728137895983147

theorem tailTrace_1478732 : CollatzResearch.WordTrace tailWord_1478732 prefixEnd_1478732 253100091728137895983147 := by
  unfold tailWord_1478732
  simp only [CollatzResearch.WordTrace]
  refine ⟨26966893439406993082195225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35955857919209324109593633 26966893439406993082195225)
  ·
    refine ⟨20225170079555244811646419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26966893439406993082195225 20225170079555244811646419)
    ·
      refine ⟨30337755119332867217469629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20225170079555244811646419 30337755119332867217469629)
      ·
        refine ⟨11376658169749825206551111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30337755119332867217469629 11376658169749825206551111)
        ·
          refine ⟨17064987254624737809826667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11376658169749825206551111 17064987254624737809826667)
          ·
            refine ⟨25597480881937106714740001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17064987254624737809826667 25597480881937106714740001)
            ·
              refine ⟨19198110661452830036055001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25597480881937106714740001 19198110661452830036055001)
              ·
                refine ⟨14398582996089622527041251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19198110661452830036055001 14398582996089622527041251)
                ·
                  refine ⟨21597874494134433790561877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14398582996089622527041251 21597874494134433790561877)
                  ·
                    refine ⟨253100091728137895983147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21597874494134433790561877 253100091728137895983147)
                    ·
                      rfl

theorem cell23_1478732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_1478732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478732 prefixEnd_1478732 := by exact prefixLift 1478732
  have htrace : WordTrace (prefixWord ++ tailWord_1478732) baseStart_1478732 baseEnd_1478732 := by
    simpa [prefixWord, tailWord_1478732, baseEnd_1478732] using wordTrace_append hprefix tailTrace_1478732
  have hstable : (prefixWord ++ tailWord_1478732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478732).length < 2 ^ (prefixWord ++ tailWord_1478732).sum := by decide
  have hdescent : baseEnd_1478732 < baseStart_1478732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478759 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 2, 4, 3]
def baseStart_1478759 : Nat := 118140960795 + 1478759 * 2 ^ 59
def prefixEnd_1478759 : Nat := 4983230072969 + 3 ^ 40 * 1478759 * 2
def baseEnd_1478759 : Nat := 759314139162085082311817

theorem tailTrace_1478759 : CollatzResearch.WordTrace tailWord_1478759 prefixEnd_1478759 759314139162085082311817 := by
  unfold tailWord_1478759
  simp only [CollatzResearch.WordTrace]
  refine ⟨53934771649716169775623331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35956514433144113183748887 53934771649716169775623331)
  ·
    refine ⟨80902157474574254663434997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53934771649716169775623331 80902157474574254663434997)
    ·
      refine ⟨7584577263241336374697031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80902157474574254663434997 7584577263241336374697031)
      ·
        refine ⟨11376865894862004562045547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7584577263241336374697031 11376865894862004562045547)
        ·
          refine ⟨17065298842293006843068321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11376865894862004562045547 17065298842293006843068321)
          ·
            refine ⟨12798974131719755132301241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17065298842293006843068321 12798974131719755132301241)
            ·
              refine ⟨9599230598789816349225931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12798974131719755132301241 9599230598789816349225931)
              ·
                refine ⟨14398845898184724523838897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9599230598789816349225931 14398845898184724523838897)
                ·
                  refine ⟨10799134423638543392879173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14398845898184724523838897 10799134423638543392879173)
                  ·
                    refine ⟨2024837704432226886164845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10799134423638543392879173 2024837704432226886164845)
                    ·
                      refine ⟨759314139162085082311817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2024837704432226886164845 759314139162085082311817)
                      ·
                        rfl

theorem cell23_1478759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_1478759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478759 prefixEnd_1478759 := by exact prefixLift 1478759
  have htrace : WordTrace (prefixWord ++ tailWord_1478759) baseStart_1478759 baseEnd_1478759 := by
    simpa [prefixWord, tailWord_1478759, baseEnd_1478759] using wordTrace_append hprefix tailTrace_1478759
  have hstable : (prefixWord ++ tailWord_1478759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478759).length < 2 ^ (prefixWord ++ tailWord_1478759).sum := by decide
  have hdescent : baseEnd_1478759 < baseStart_1478759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478813 : List Nat := [1, 4, 2, 1, 1, 3, 4, 2, 5]
def baseStart_1478813 : Nat := 118140960795 + 1478813 * 2 ^ 59
def prefixEnd_1478813 : Nat := 4983230072969 + 3 ^ 40 * 1478813 * 2
def baseEnd_1478813 : Nat := 84371318568603096781841

theorem tailTrace_1478813 : CollatzResearch.WordTrace tailWord_1478813 prefixEnd_1478813 84371318568603096781841 := by
  unfold tailWord_1478813
  simp only [CollatzResearch.WordTrace]
  refine ⟨53936741191520536998089093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35957827461013691332059395 53936741191520536998089093)
  ·
    refine ⟨10113138973410100687141705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53936741191520536998089093 10113138973410100687141705)
    ·
      refine ⟨7584854230057575515356279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10113138973410100687141705 7584854230057575515356279)
      ·
        refine ⟨11377281345086363273034419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7584854230057575515356279 11377281345086363273034419)
        ·
          refine ⟨17065922017629544909551629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11377281345086363273034419 17065922017629544909551629)
          ·
            refine ⟨6399720756611079341081861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17065922017629544909551629 6399720756611079341081861)
            ·
              refine ⟨1199947641864577376452849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6399720756611079341081861 1199947641864577376452849)
              ·
                refine ⟨899960731398433032339637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1199947641864577376452849 899960731398433032339637)
                ·
                  refine ⟨84371318568603096781841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 899960731398433032339637 84371318568603096781841)
                  ·
                    rfl

theorem cell23_1478813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2, 5].length) (baseStart_1478813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478813 prefixEnd_1478813 := by exact prefixLift 1478813
  have htrace : WordTrace (prefixWord ++ tailWord_1478813) baseStart_1478813 baseEnd_1478813 := by
    simpa [prefixWord, tailWord_1478813, baseEnd_1478813] using wordTrace_append hprefix tailTrace_1478813
  have hstable : (prefixWord ++ tailWord_1478813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478813).length < 2 ^ (prefixWord ++ tailWord_1478813).sum := by decide
  have hdescent : baseEnd_1478813 < baseStart_1478813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478816 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 2, 5, 2]
def baseStart_1478816 : Nat := 118140960795 + 1478816 * 2 ^ 59
def prefixEnd_1478816 : Nat := 4983230072969 + 3 ^ 40 * 1478816 * 2
def baseEnd_1478816 : Nat := 759343407559391359299055

theorem tailTrace_1478816 : CollatzResearch.WordTrace tailWord_1478816 prefixEnd_1478816 759343407559391359299055 := by
  unfold tailWord_1478816
  simp only [CollatzResearch.WordTrace]
  refine ⟨26968425305254834255224151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35957900407006445673632201 26968425305254834255224151)
  ·
    refine ⟨40452637957882251382836227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26968425305254834255224151 40452637957882251382836227)
    ·
      refine ⟨60678956936823377074254341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40452637957882251382836227 60678956936823377074254341)
      ·
        refine ⟨11377304425654383201422689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60678956936823377074254341 11377304425654383201422689)
        ·
          refine ⟨8532978319240787401067017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11377304425654383201422689 8532978319240787401067017)
          ·
            refine ⟨6399733739430590550800263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8532978319240787401067017 6399733739430590550800263)
            ·
              refine ⟨9599600609145885826200395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6399733739430590550800263 9599600609145885826200395)
              ·
                refine ⟨14399400913718828739300593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9599600609145885826200395 14399400913718828739300593)
                ·
                  refine ⟨10799550685289121554475445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14399400913718828739300593 10799550685289121554475445)
                  ·
                    refine ⟨1012457876745855145732073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10799550685289121554475445 1012457876745855145732073)
                    ·
                      refine ⟨759343407559391359299055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1012457876745855145732073 759343407559391359299055)
                      ·
                        rfl

theorem cell23_1478816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_1478816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478816 prefixEnd_1478816 := by exact prefixLift 1478816
  have htrace : WordTrace (prefixWord ++ tailWord_1478816) baseStart_1478816 baseEnd_1478816 := by
    simpa [prefixWord, tailWord_1478816, baseEnd_1478816] using wordTrace_append hprefix tailTrace_1478816
  have hstable : (prefixWord ++ tailWord_1478816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478816).length < 2 ^ (prefixWord ++ tailWord_1478816).sum := by decide
  have hdescent : baseEnd_1478816 < baseStart_1478816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478823 : List Nat := [1, 1, 6, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_1478823 : Nat := 118140960795 + 1478823 * 2 ^ 59
def prefixEnd_1478823 : Nat := 4983230072969 + 3 ^ 40 * 1478823 * 2
def baseEnd_1478823 : Nat := 759347001923972831911523

theorem tailTrace_1478823 : CollatzResearch.WordTrace tailWord_1478823 prefixEnd_1478823 759347001923972831911523 := by
  unfold tailWord_1478823
  simp only [CollatzResearch.WordTrace]
  refine ⟨53937105921484308705953123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35958070614322872470635415 53937105921484308705953123)
  ·
    refine ⟨80905658882226463058929685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53937105921484308705953123 80905658882226463058929685)
    ·
      refine ⟨3792452760104365455887329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 80905658882226463058929685 3792452760104365455887329)
      ·
        refine ⟨2844339570078274091915497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3792452760104365455887329 2844339570078274091915497)
        ·
          refine ⟨2133254677558705568936623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2844339570078274091915497 2133254677558705568936623)
          ·
            refine ⟨3199882016338058353404935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2133254677558705568936623 3199882016338058353404935)
            ·
              refine ⟨4799823024507087530107403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3199882016338058353404935 4799823024507087530107403)
              ·
                refine ⟨7199734536760631295161105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4799823024507087530107403 7199734536760631295161105)
                ·
                  refine ⟨5399800902570473471370829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7199734536760631295161105 5399800902570473471370829)
                  ·
                    refine ⟨2024925338463927551764061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5399800902570473471370829 2024925338463927551764061)
                    ·
                      refine ⟨759347001923972831911523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2024925338463927551764061 759347001923972831911523)
                      ·
                        rfl

theorem cell23_1478823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_1478823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478823 prefixEnd_1478823 := by exact prefixLift 1478823
  have htrace : WordTrace (prefixWord ++ tailWord_1478823) baseStart_1478823 baseEnd_1478823 := by
    simpa [prefixWord, tailWord_1478823, baseEnd_1478823] using wordTrace_append hprefix tailTrace_1478823
  have hstable : (prefixWord ++ tailWord_1478823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478823).length < 2 ^ (prefixWord ++ tailWord_1478823).sum := by decide
  have hdescent : baseEnd_1478823 < baseStart_1478823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478873 : List Nat := [1, 2, 1, 2, 3, 1, 4, 4, 1, 4]
def baseStart_1478873 : Nat := 118140960795 + 1478873 * 2 ^ 59
def prefixEnd_1478873 : Nat := 4983230072969 + 3 ^ 40 * 1478873 * 2
def baseEnd_1478873 : Nat := 253124225318899212095431

theorem tailTrace_1478873 : CollatzResearch.WordTrace tailWord_1478873 prefixEnd_1478873 253124225318899212095431 := by
  unfold tailWord_1478873
  simp only [CollatzResearch.WordTrace]
  refine ⟨53938929571303167245273273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35959286380868778163515515 53938929571303167245273273)
  ·
    refine ⟨40454197178477375433954955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53938929571303167245273273 40454197178477375433954955)
    ·
      refine ⟨60681295767716063150932433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40454197178477375433954955 60681295767716063150932433)
      ·
        refine ⟨45510971825787047363199325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60681295767716063150932433 45510971825787047363199325)
        ·
          refine ⟨17066614434670142761199747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45510971825787047363199325 17066614434670142761199747)
          ·
            refine ⟨25599921652005214141799621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17066614434670142761199747 25599921652005214141799621)
            ·
              refine ⟨4799985309750977651587429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25599921652005214141799621 4799985309750977651587429)
              ·
                refine ⟨899997245578308309672643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4799985309750977651587429 899997245578308309672643)
                ·
                  refine ⟨1349995868367462464508965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 899997245578308309672643 1349995868367462464508965)
                  ·
                    refine ⟨253124225318899212095431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1349995868367462464508965 253124225318899212095431)
                    ·
                      rfl

theorem cell23_1478873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4, 1, 4].length) (baseStart_1478873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478873 prefixEnd_1478873 := by exact prefixLift 1478873
  have htrace : WordTrace (prefixWord ++ tailWord_1478873) baseStart_1478873 baseEnd_1478873 := by
    simpa [prefixWord, tailWord_1478873, baseEnd_1478873] using wordTrace_append hprefix tailTrace_1478873
  have hstable : (prefixWord ++ tailWord_1478873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478873).length < 2 ^ (prefixWord ++ tailWord_1478873).sum := by decide
  have hdescent : baseEnd_1478873 < baseStart_1478873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478923 : List Nat := [1, 1, 1, 1, 5, 2, 3, 2, 2, 3, 2]
def baseStart_1478923 : Nat := 118140960795 + 1478923 * 2 ^ 59
def prefixEnd_1478923 : Nat := 4983230072969 + 3 ^ 40 * 1478923 * 2
def baseEnd_1478923 : Nat := 759398349989422440661063

theorem tailTrace_1478923 : CollatzResearch.WordTrace tailWord_1478923 prefixEnd_1478923 759398349989422440661063 := by
  unfold tailWord_1478923
  simp only [CollatzResearch.WordTrace]
  refine ⟨53940753221122025784593423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35960502147414683856395615 53940753221122025784593423)
  ·
    refine ⟨80911129831683038676890135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53940753221122025784593423 80911129831683038676890135)
    ·
      refine ⟨121366694747524558015335203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80911129831683038676890135 121366694747524558015335203)
      ·
        refine ⟨182050042121286837023002805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121366694747524558015335203 182050042121286837023002805)
        ·
          refine ⟨17067191448870640970906513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 182050042121286837023002805 17067191448870640970906513)
          ·
            refine ⟨12800393586652980728179885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17067191448870640970906513 12800393586652980728179885)
            ·
              refine ⟨4800147594994867773067457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12800393586652980728179885 4800147594994867773067457)
              ·
                refine ⟨3600110696246150829800593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4800147594994867773067457 3600110696246150829800593)
                ·
                  refine ⟨2700083022184613122350445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3600110696246150829800593 2700083022184613122350445)
                  ·
                    refine ⟨1012531133319229920881417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2700083022184613122350445 1012531133319229920881417)
                    ·
                      refine ⟨759398349989422440661063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1012531133319229920881417 759398349989422440661063)
                      ·
                        rfl

theorem cell23_1478923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 3, 2].length) (baseStart_1478923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478923 prefixEnd_1478923 := by exact prefixLift 1478923
  have htrace : WordTrace (prefixWord ++ tailWord_1478923) baseStart_1478923 baseEnd_1478923 := by
    simpa [prefixWord, tailWord_1478923, baseEnd_1478923] using wordTrace_append hprefix tailTrace_1478923
  have hstable : (prefixWord ++ tailWord_1478923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478923).length < 2 ^ (prefixWord ++ tailWord_1478923).sum := by decide
  have hdescent : baseEnd_1478923 < baseStart_1478923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478936 : List Nat := [2, 1, 2, 3, 1, 2, 2, 2, 3, 1, 4]
def baseStart_1478936 : Nat := 118140960795 + 1478936 * 2 ^ 59
def prefixEnd_1478936 : Nat := 4983230072969 + 3 ^ 40 * 1478936 * 2
def baseEnd_1478936 : Nat := 759405025237930889798503

theorem tailTrace_1478936 : CollatzResearch.WordTrace tailWord_1478936 prefixEnd_1478936 759405025237930889798503 := by
  unfold tailWord_1478936
  simp only [CollatzResearch.WordTrace]
  refine ⟨26970613685037464502408331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35960818246716619336544441 26970613685037464502408331)
  ·
    refine ⟨40455920527556196753612497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26970613685037464502408331 40455920527556196753612497)
    ·
      refine ⟨30341940395667147565209373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40455920527556196753612497 30341940395667147565209373)
      ·
        refine ⟨11378227648375180336953515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30341940395667147565209373 11378227648375180336953515)
        ·
          refine ⟨17067341472562770505430273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11378227648375180336953515 17067341472562770505430273)
          ·
            refine ⟨12800506104422077879072705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17067341472562770505430273 12800506104422077879072705)
            ·
              refine ⟨9600379578316558409304529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12800506104422077879072705 9600379578316558409304529)
              ·
                refine ⟨7200284683737418806978397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9600379578316558409304529 7200284683737418806978397)
                ·
                  refine ⟨2700106756401532052616899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7200284683737418806978397 2700106756401532052616899)
                  ·
                    refine ⟨4050160134602298078925349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2700106756401532052616899 4050160134602298078925349)
                    ·
                      refine ⟨759405025237930889798503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4050160134602298078925349 759405025237930889798503)
                      ·
                        rfl

theorem cell23_1478936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_1478936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478936 prefixEnd_1478936 := by exact prefixLift 1478936
  have htrace : WordTrace (prefixWord ++ tailWord_1478936) baseStart_1478936 baseEnd_1478936 := by
    simpa [prefixWord, tailWord_1478936, baseEnd_1478936] using wordTrace_append hprefix tailTrace_1478936
  have hstable : (prefixWord ++ tailWord_1478936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478936).length < 2 ^ (prefixWord ++ tailWord_1478936).sum := by decide
  have hdescent : baseEnd_1478936 < baseStart_1478936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478959 : List Nat := [1, 1, 2, 1, 2, 1, 6, 9]
def baseStart_1478959 : Nat := 118140960795 + 1478959 * 2 ^ 59
def prefixEnd_1478959 : Nat := 4983230072969 + 3 ^ 40 * 1478959 * 2
def baseEnd_1478959 : Nat := 28126549455295714807811

theorem tailTrace_1478959 : CollatzResearch.WordTrace tailWord_1478959 prefixEnd_1478959 28126549455295714807811 := by
  unfold tailWord_1478959
  simp only [CollatzResearch.WordTrace]
  refine ⟨53942066248991603932903931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35961377499327735955269287 53942066248991603932903931)
  ·
    refine ⟨80913099373487405899355897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53942066248991603932903931 80913099373487405899355897)
    ·
      refine ⟨60684824530115554424516923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80913099373487405899355897 60684824530115554424516923)
      ·
        refine ⟨91027236795173331636775385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60684824530115554424516923 91027236795173331636775385)
        ·
          refine ⟨68270427596379998727581539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91027236795173331636775385 68270427596379998727581539)
          ·
            refine ⟨102405641394569998091372309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68270427596379998727581539 102405641394569998091372309)
            ·
              refine ⟨4800264440370468660533077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102405641394569998091372309 4800264440370468660533077)
              ·
                refine ⟨28126549455295714807811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4800264440370468660533077 28126549455295714807811)
                ·
                  rfl

theorem cell23_1478959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 9].length) (baseStart_1478959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478959 prefixEnd_1478959 := by exact prefixLift 1478959
  have htrace : WordTrace (prefixWord ++ tailWord_1478959) baseStart_1478959 baseEnd_1478959 := by
    simpa [prefixWord, tailWord_1478959, baseEnd_1478959] using wordTrace_append hprefix tailTrace_1478959
  have hstable : (prefixWord ++ tailWord_1478959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478959).length < 2 ^ (prefixWord ++ tailWord_1478959).sum := by decide
  have hdescent : baseEnd_1478959 < baseStart_1478959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1478970 : List Nat := [3, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4]
def baseStart_1478970 : Nat := 118140960795 + 1478970 * 2 ^ 59
def prefixEnd_1478970 : Nat := 4983230072969 + 3 ^ 40 * 1478970 * 2
def baseEnd_1478970 : Nat := 759422483580183756773347

theorem tailTrace_1478970 : CollatzResearch.WordTrace tailWord_1478970 prefixEnd_1478970 759422483580183756773347 := by
  unfold tailWord_1478970
  simp only [CollatzResearch.WordTrace]
  refine ⟨13485616862987938202888591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35961644967967835207702909 13485616862987938202888591)
  ·
    refine ⟨20228425294481907304332887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13485616862987938202888591 20228425294481907304332887)
    ·
      refine ⟨30342637941722860956499331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20228425294481907304332887 30342637941722860956499331)
      ·
        refine ⟨45513956912584291434748997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30342637941722860956499331 45513956912584291434748997)
        ·
          refine ⟨8533866921109554644015437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45513956912584291434748997 8533866921109554644015437)
          ·
            refine ⟨3200200095416082991505789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8533866921109554644015437 3200200095416082991505789)
            ·
              refine ⟨1200075035781031121814671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3200200095416082991505789 1200075035781031121814671)
              ·
                refine ⟨1800112553671546682722007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1200075035781031121814671 1800112553671546682722007)
                ·
                  refine ⟨2700168830507320024083011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1800112553671546682722007 2700168830507320024083011)
                  ·
                    refine ⟨4050253245760980036124517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2700168830507320024083011 4050253245760980036124517)
                    ·
                      refine ⟨759422483580183756773347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4050253245760980036124517 759422483580183756773347)
                      ·
                        rfl

theorem cell23_1478970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4].length) (baseStart_1478970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1478970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1478970 prefixEnd_1478970 := by exact prefixLift 1478970
  have htrace : WordTrace (prefixWord ++ tailWord_1478970) baseStart_1478970 baseEnd_1478970 := by
    simpa [prefixWord, tailWord_1478970, baseEnd_1478970] using wordTrace_append hprefix tailTrace_1478970
  have hstable : (prefixWord ++ tailWord_1478970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1478970).length < 2 ^ (prefixWord ++ tailWord_1478970).sum := by decide
  have hdescent : baseEnd_1478970 < baseStart_1478970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1478970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479004 : List Nat := [2, 2, 4, 3, 1, 1, 1, 2, 3, 2, 2]
def baseStart_1479004 : Nat := 118140960795 + 1479004 * 2 ^ 59
def prefixEnd_1479004 : Nat := 4983230072969 + 3 ^ 40 * 1479004 * 2
def baseEnd_1479004 : Nat := 759439941922436623748191

theorem tailTrace_1479004 : CollatzResearch.WordTrace tailWord_1479004 prefixEnd_1479004 759439941922436623748191 := by
  unfold tailWord_1479004
  simp only [CollatzResearch.WordTrace]
  refine ⟨26971853766914288309146033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35962471689219051078861377 26971853766914288309146033)
  ·
    refine ⟨20228890325185716231859525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26971853766914288309146033 20228890325185716231859525)
    ·
      refine ⟨3792916935972321793473661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20228890325185716231859525 3792916935972321793473661)
      ·
        refine ⟨1422343850989620672552623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3792916935972321793473661 1422343850989620672552623)
        ·
          refine ⟨2133515776484431008828935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1422343850989620672552623 2133515776484431008828935)
          ·
            refine ⟨3200273664726646513243403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2133515776484431008828935 3200273664726646513243403)
            ·
              refine ⟨4800410497089969769865105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3200273664726646513243403 4800410497089969769865105)
              ·
                refine ⟨3600307872817477327398829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4800410497089969769865105 3600307872817477327398829)
                ·
                  refine ⟨1350115452306553997774561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3600307872817477327398829 1350115452306553997774561)
                  ·
                    refine ⟨1012586589229915498330921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1350115452306553997774561 1012586589229915498330921)
                    ·
                      refine ⟨759439941922436623748191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1012586589229915498330921 759439941922436623748191)
                      ·
                        rfl

theorem cell23_1479004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_1479004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479004 prefixEnd_1479004 := by exact prefixLift 1479004
  have htrace : WordTrace (prefixWord ++ tailWord_1479004) baseStart_1479004 baseEnd_1479004 := by
    simpa [prefixWord, tailWord_1479004, baseEnd_1479004] using wordTrace_append hprefix tailTrace_1479004
  have hstable : (prefixWord ++ tailWord_1479004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479004).length < 2 ^ (prefixWord ++ tailWord_1479004).sum := by decide
  have hdescent : baseEnd_1479004 < baseStart_1479004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479037 : List Nat := [1, 4, 1, 1, 2, 5, 1, 2, 2, 1, 3]
def baseStart_1479037 : Nat := 118140960795 + 1479037 * 2 ^ 59
def prefixEnd_1479037 : Nat := 4983230072969 + 3 ^ 40 * 1479037 * 2
def baseEnd_1479037 : Nat := 759456886784034994635539

theorem tailTrace_1479037 : CollatzResearch.WordTrace tailWord_1479037 prefixEnd_1479037 759456886784034994635539 := by
  unfold tailWord_1479037
  simp only [CollatzResearch.WordTrace]
  refine ⟨53944911142709023254243365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35963274095139348836162243 53944911142709023254243365)
  ·
    refine ⟨10114670839257941860170631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53944911142709023254243365 10114670839257941860170631)
    ·
      refine ⟨15172006258886912790255947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10114670839257941860170631 15172006258886912790255947)
      ·
        refine ⟨22758009388330369185383921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15172006258886912790255947 22758009388330369185383921)
        ·
          refine ⟨17068507041247776889037941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22758009388330369185383921 17068507041247776889037941)
          ·
            refine ⟨1600172535116979083347307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17068507041247776889037941 1600172535116979083347307)
            ·
              refine ⟨2400258802675468625020961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1600172535116979083347307 2400258802675468625020961)
              ·
                refine ⟨1800194102006601468765721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2400258802675468625020961 1800194102006601468765721)
                ·
                  refine ⟨1350145576504951101574291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1800194102006601468765721 1350145576504951101574291)
                  ·
                    refine ⟨2025218364757426652361437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1350145576504951101574291 2025218364757426652361437)
                    ·
                      refine ⟨759456886784034994635539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2025218364757426652361437 759456886784034994635539)
                      ·
                        rfl

theorem cell23_1479037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_1479037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479037 prefixEnd_1479037 := by exact prefixLift 1479037
  have htrace : WordTrace (prefixWord ++ tailWord_1479037) baseStart_1479037 baseEnd_1479037 := by
    simpa [prefixWord, tailWord_1479037, baseEnd_1479037] using wordTrace_append hprefix tailTrace_1479037
  have hstable : (prefixWord ++ tailWord_1479037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479037).length < 2 ^ (prefixWord ++ tailWord_1479037).sum := by decide
  have hdescent : baseEnd_1479037 < baseStart_1479037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479054 : List Nat := [4, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3]
def baseStart_1479054 : Nat := 118140960795 + 1479054 * 2 ^ 59
def prefixEnd_1479054 : Nat := 4983230072969 + 3 ^ 40 * 1479054 * 2
def baseEnd_1479054 : Nat := 759465615955161428122961

theorem tailTrace_1479054 : CollatzResearch.WordTrace tailWord_1479054 prefixEnd_1479054 759465615955161428122961 := by
  unfold tailWord_1479054
  simp only [CollatzResearch.WordTrace]
  refine ⟨6743191397955929394701527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35963687455764956771741477 6743191397955929394701527)
  ·
    refine ⟨10114787096933894092052291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6743191397955929394701527 10114787096933894092052291)
    ·
      refine ⟨15172180645400841138078437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10114787096933894092052291 15172180645400841138078437)
      ·
        refine ⟨2844783871012657713389707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15172180645400841138078437 2844783871012657713389707)
        ·
          refine ⟨4267175806518986570084561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2844783871012657713389707 4267175806518986570084561)
          ·
            refine ⟨3200381854889239927563421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4267175806518986570084561 3200381854889239927563421)
            ·
              refine ⟨1200143195583464972836283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3200381854889239927563421 1200143195583464972836283)
              ·
                refine ⟨1800214793375197459254425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1200143195583464972836283 1800214793375197459254425)
                ·
                  refine ⟨1350161095031398094440819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1800214793375197459254425 1350161095031398094440819)
                  ·
                    refine ⟨2025241642547097141661229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1350161095031398094440819 2025241642547097141661229)
                    ·
                      refine ⟨759465615955161428122961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2025241642547097141661229 759465615955161428122961)
                      ·
                        rfl

theorem cell23_1479054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_1479054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479054 prefixEnd_1479054 := by exact prefixLift 1479054
  have htrace : WordTrace (prefixWord ++ tailWord_1479054) baseStart_1479054 baseEnd_1479054 := by
    simpa [prefixWord, tailWord_1479054, baseEnd_1479054] using wordTrace_append hprefix tailTrace_1479054
  have hstable : (prefixWord ++ tailWord_1479054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479054).length < 2 ^ (prefixWord ++ tailWord_1479054).sum := by decide
  have hdescent : baseEnd_1479054 < baseStart_1479054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479080 : List Nat := [2, 1, 6, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_1479080 : Nat := 118140960795 + 1479080 * 2 ^ 59
def prefixEnd_1479080 : Nat := 4983230072969 + 3 ^ 40 * 1479080 * 2
def baseEnd_1479080 : Nat := 759478966452178326397841

theorem tailTrace_1479080 : CollatzResearch.WordTrace tailWord_1479080 prefixEnd_1479080 759478966452178326397841 := by
  unfold tailWord_1479080
  simp only [CollatzResearch.WordTrace]
  refine ⟨26973239740776620799029347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35964319654368827732039129 26973239740776620799029347)
  ·
    refine ⟨40459859611164931198544021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26973239740776620799029347 40459859611164931198544021)
    ·
      refine ⟨1896555919273356149931751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40459859611164931198544021 1896555919273356149931751)
      ·
        refine ⟨2844833878910034224897627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1896555919273356149931751 2844833878910034224897627)
        ·
          refine ⟨4267250818365051337346441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2844833878910034224897627 4267250818365051337346441)
          ·
            refine ⟨3200438113773788503009831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4267250818365051337346441 3200438113773788503009831)
            ·
              refine ⟨4800657170660682754514747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3200438113773788503009831 4800657170660682754514747)
              ·
                refine ⟨7200985755991024131772121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4800657170660682754514747 7200985755991024131772121)
                ·
                  refine ⟨5400739316993268098829091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7200985755991024131772121 5400739316993268098829091)
                  ·
                    refine ⟨8101108975489902148243637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5400739316993268098829091 8101108975489902148243637)
                    ·
                      refine ⟨759478966452178326397841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8101108975489902148243637 759478966452178326397841)
                      ·
                        rfl

theorem cell23_1479080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_1479080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479080 prefixEnd_1479080 := by exact prefixLift 1479080
  have htrace : WordTrace (prefixWord ++ tailWord_1479080) baseStart_1479080 baseEnd_1479080 := by
    simpa [prefixWord, tailWord_1479080, baseEnd_1479080] using wordTrace_append hprefix tailTrace_1479080
  have hstable : (prefixWord ++ tailWord_1479080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479080).length < 2 ^ (prefixWord ++ tailWord_1479080).sum := by decide
  have hdescent : baseEnd_1479080 < baseStart_1479080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479100 : List Nat := [2, 2, 2, 4, 1, 3, 1, 1, 7]
def baseStart_1479100 : Nat := 118140960795 + 1479100 * 2 ^ 59
def prefixEnd_1479100 : Nat := 4983230072969 + 3 ^ 40 * 1479100 * 2
def baseEnd_1479100 : Nat := 84387692896140916460861

theorem tailTrace_1479100 : CollatzResearch.WordTrace tailWord_1479100 prefixEnd_1479100 84387692896140916460861 := by
  unfold tailWord_1479100
  simp only [CollatzResearch.WordTrace]
  refine ⟨26973604470740392506893377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35964805960987190009191169 26973604470740392506893377)
  ·
    refine ⟨20230203353055294380170033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26973604470740392506893377 20230203353055294380170033)
    ·
      refine ⟨15172652514791470785127525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20230203353055294380170033 15172652514791470785127525)
      ·
        refine ⟨2844872346523400772211411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15172652514791470785127525 2844872346523400772211411)
        ·
          refine ⟨4267308519785101158317117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2844872346523400772211411 4267308519785101158317117)
          ·
            refine ⟨1600240694919412934368919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4267308519785101158317117 1600240694919412934368919)
            ·
              refine ⟨2400361042379119401553379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1600240694919412934368919 2400361042379119401553379)
              ·
                refine ⟨3600541563568679102330069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2400361042379119401553379 3600541563568679102330069)
                ·
                  refine ⟨84387692896140916460861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3600541563568679102330069 84387692896140916460861)
                  ·
                    rfl

theorem cell23_1479100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 7].length) (baseStart_1479100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479100 prefixEnd_1479100 := by exact prefixLift 1479100
  have htrace : WordTrace (prefixWord ++ tailWord_1479100) baseStart_1479100 baseEnd_1479100 := by
    simpa [prefixWord, tailWord_1479100, baseEnd_1479100] using wordTrace_append hprefix tailTrace_1479100
  have hstable : (prefixWord ++ tailWord_1479100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479100).length < 2 ^ (prefixWord ++ tailWord_1479100).sum := by decide
  have hdescent : baseEnd_1479100 < baseStart_1479100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479105 : List Nat := [1, 2, 7, 1, 2, 1, 2, 1, 2, 1, 3]
def baseStart_1479105 : Nat := 118140960795 + 1479105 * 2 ^ 59
def prefixEnd_1479105 : Nat := 4983230072969 + 3 ^ 40 * 1479105 * 2
def baseEnd_1479105 : Nat := 759491803468540728585227

theorem tailTrace_1479105 : CollatzResearch.WordTrace tailWord_1479105 prefixEnd_1479105 759491803468540728585227 := by
  unfold tailWord_1479105
  simp only [CollatzResearch.WordTrace]
  refine ⟨53947391306462670867718769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35964927537641780578479179 53947391306462670867718769)
  ·
    refine ⟨40460543479847003150789077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53947391306462670867718769 40460543479847003150789077)
    ·
      refine ⟨948293987808914136346619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 40460543479847003150789077 948293987808914136346619)
      ·
        refine ⟨1422440981713371204519929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 948293987808914136346619 1422440981713371204519929)
        ·
          refine ⟨1066830736285028403389947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1422440981713371204519929 1066830736285028403389947)
          ·
            refine ⟨1600246104427542605084921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066830736285028403389947 1600246104427542605084921)
            ·
              refine ⟨1200184578320656953813691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1600246104427542605084921 1200184578320656953813691)
              ·
                refine ⟨1800276867480985430720537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1200184578320656953813691 1800276867480985430720537)
                ·
                  refine ⟨1350207650610739073040403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1800276867480985430720537 1350207650610739073040403)
                  ·
                    refine ⟨2025311475916108609560605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1350207650610739073040403 2025311475916108609560605)
                    ·
                      refine ⟨759491803468540728585227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2025311475916108609560605 759491803468540728585227)
                      ·
                        rfl

theorem cell23_1479105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_1479105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479105 prefixEnd_1479105 := by exact prefixLift 1479105
  have htrace : WordTrace (prefixWord ++ tailWord_1479105) baseStart_1479105 baseEnd_1479105 := by
    simpa [prefixWord, tailWord_1479105, baseEnd_1479105] using wordTrace_append hprefix tailTrace_1479105
  have hstable : (prefixWord ++ tailWord_1479105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479105).length < 2 ^ (prefixWord ++ tailWord_1479105).sum := by decide
  have hdescent : baseEnd_1479105 < baseStart_1479105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479150 : List Nat := [4, 1, 2, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_1479150 : Nat := 118140960795 + 1479150 * 2 ^ 59
def prefixEnd_1479150 : Nat := 4983230072969 + 3 ^ 40 * 1479150 * 2
def baseEnd_1479150 : Nat := 759514910097993052522519

theorem tailTrace_1479150 : CollatzResearch.WordTrace tailWord_1479150 prefixEnd_1479150 759514910097993052522519 := by
  unfold tailWord_1479150
  simp only [CollatzResearch.WordTrace]
  refine ⟨6743629073912455444138363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35966021727533095702071269 6743629073912455444138363)
  ·
    refine ⟨10115443610868683166207545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6743629073912455444138363 10115443610868683166207545)
    ·
      refine ⟨7586582708151512374655659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10115443610868683166207545 7586582708151512374655659)
      ·
        refine ⟨11379874062227268561983489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7586582708151512374655659 11379874062227268561983489)
        ·
          refine ⟨8534905546670451421487617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11379874062227268561983489 8534905546670451421487617)
          ·
            refine ⟨6401179160002838566115713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8534905546670451421487617 6401179160002838566115713)
            ·
              refine ⟨4800884370002128924586785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6401179160002838566115713 4800884370002128924586785)
              ·
                refine ⟨3600663277501596693440089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4800884370002128924586785 3600663277501596693440089)
                ·
                  refine ⟨2700497458126197520080067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3600663277501596693440089 2700497458126197520080067)
                  ·
                    refine ⟨4050746187189296280120101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2700497458126197520080067 4050746187189296280120101)
                    ·
                      refine ⟨759514910097993052522519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4050746187189296280120101 759514910097993052522519)
                      ·
                        rfl

theorem cell23_1479150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_1479150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479150 prefixEnd_1479150 := by exact prefixLift 1479150
  have htrace : WordTrace (prefixWord ++ tailWord_1479150) baseStart_1479150 baseEnd_1479150 := by
    simpa [prefixWord, tailWord_1479150, baseEnd_1479150] using wordTrace_append hprefix tailTrace_1479150
  have hstable : (prefixWord ++ tailWord_1479150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479150).length < 2 ^ (prefixWord ++ tailWord_1479150).sum := by decide
  have hdescent : baseEnd_1479150 < baseStart_1479150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479173 : List Nat := [1, 3, 1, 1, 2, 2, 4, 3, 6]
def baseStart_1479173 : Nat := 118140960795 + 1479173 * 2 ^ 59
def prefixEnd_1479173 : Nat := 4983230072969 + 3 ^ 40 * 1479173 * 2
def baseEnd_1479173 : Nat := 84391857794782940281657

theorem tailTrace_1479173 : CollatzResearch.WordTrace tailWord_1479173 prefixEnd_1479173 84391857794782940281657 := by
  unfold tailWord_1479173
  simp only [CollatzResearch.WordTrace]
  refine ⟨53949871470216318481194173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35966580980144212320796115 53949871470216318481194173)
  ·
    refine ⟨20231201801331119430447815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53949871470216318481194173 20231201801331119430447815)
    ·
      refine ⟨30346802701996679145671723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20231201801331119430447815 30346802701996679145671723)
      ·
        refine ⟨45520204052995018718507585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30346802701996679145671723 45520204052995018718507585)
        ·
          refine ⟨34140153039746264038880689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45520204052995018718507585 34140153039746264038880689)
          ·
            refine ⟨25605114779809698029160517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34140153039746264038880689 25605114779809698029160517)
            ·
              refine ⟨4800959021214318380467597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25605114779809698029160517 4800959021214318380467597)
              ·
                refine ⟨1800359632955369392675349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4800959021214318380467597 1800359632955369392675349)
                ·
                  refine ⟨84391857794782940281657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1800359632955369392675349 84391857794782940281657)
                  ·
                    rfl

theorem cell23_1479173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 6].length) (baseStart_1479173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479173 prefixEnd_1479173 := by exact prefixLift 1479173
  have htrace : WordTrace (prefixWord ++ tailWord_1479173) baseStart_1479173 baseEnd_1479173 := by
    simpa [prefixWord, tailWord_1479173, baseEnd_1479173] using wordTrace_append hprefix tailTrace_1479173
  have hstable : (prefixWord ++ tailWord_1479173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479173).length < 2 ^ (prefixWord ++ tailWord_1479173).sum := by decide
  have hdescent : baseEnd_1479173 < baseStart_1479173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479207 : List Nat := [1, 1, 7, 2, 1, 1, 1, 1, 8]
def baseStart_1479207 : Nat := 118140960795 + 1479207 * 2 ^ 59
def prefixEnd_1479207 : Nat := 4983230072969 + 3 ^ 40 * 1479207 * 2
def baseEnd_1479207 : Nat := 84393797610588814389973

theorem tailTrace_1479207 : CollatzResearch.WordTrace tailWord_1479207 prefixEnd_1479207 84393797610588814389973 := by
  unfold tailWord_1479207
  simp only [CollatzResearch.WordTrace]
  refine ⟨53951111552093142287931875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35967407701395428191954583 53951111552093142287931875)
  ·
    refine ⟨80926667328139713431897813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53951111552093142287931875 80926667328139713431897813)
    ·
      refine ⟨1896718765503274533560105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 80926667328139713431897813 1896718765503274533560105)
      ·
        refine ⟨1422539074127455900170079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1896718765503274533560105 1422539074127455900170079)
        ·
          refine ⟨2133808611191183850255119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1422539074127455900170079 2133808611191183850255119)
          ·
            refine ⟨3200712916786775775382679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2133808611191183850255119 3200712916786775775382679)
            ·
              refine ⟨4801069375180163663074019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3200712916786775775382679 4801069375180163663074019)
              ·
                refine ⟨7201604062770245494611029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4801069375180163663074019 7201604062770245494611029)
                ·
                  refine ⟨84393797610588814389973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7201604062770245494611029 84393797610588814389973)
                  ·
                    rfl

theorem cell23_1479207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 8].length) (baseStart_1479207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479207 prefixEnd_1479207 := by exact prefixLift 1479207
  have htrace : WordTrace (prefixWord ++ tailWord_1479207) baseStart_1479207 baseEnd_1479207 := by
    simpa [prefixWord, tailWord_1479207, baseEnd_1479207] using wordTrace_append hprefix tailTrace_1479207
  have hstable : (prefixWord ++ tailWord_1479207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479207).length < 2 ^ (prefixWord ++ tailWord_1479207).sum := by decide
  have hdescent : baseEnd_1479207 < baseStart_1479207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479250 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 6, 4]
def baseStart_1479250 : Nat := 118140960795 + 1479250 * 2 ^ 59
def prefixEnd_1479250 : Nat := 4983230072969 + 3 ^ 40 * 1479250 * 2
def baseEnd_1479250 : Nat := 253188752721147553757353

theorem tailTrace_1479250 : CollatzResearch.WordTrace tailWord_1479250 prefixEnd_1479250 253188752721147553757353 := by
  unfold tailWord_1479250
  simp only [CollatzResearch.WordTrace]
  refine ⟨13488169972734340157936801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35968453260624907087831469 13488169972734340157936801)
  ·
    refine ⟨10116127479550755118452601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13488169972734340157936801 10116127479550755118452601)
    ·
      refine ⟨7587095609663066338839451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10116127479550755118452601 7587095609663066338839451)
      ·
        refine ⟨11380643414494599508259177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7587095609663066338839451 11380643414494599508259177)
        ·
          refine ⟨8535482560870949631194383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11380643414494599508259177 8535482560870949631194383)
          ·
            refine ⟨12803223841306424446791575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8535482560870949631194383 12803223841306424446791575)
            ·
              refine ⟨19204835761959636670187363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12803223841306424446791575 19204835761959636670187363)
              ·
                refine ⟨28807253642939455005281045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19204835761959636670187363 28807253642939455005281045)
                ·
                  refine ⟨1350340014512786953372549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28807253642939455005281045 1350340014512786953372549)
                  ·
                    refine ⟨253188752721147553757353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1350340014512786953372549 253188752721147553757353)
                    ·
                      rfl

theorem cell23_1479250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_1479250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479250 prefixEnd_1479250 := by exact prefixLift 1479250
  have htrace : WordTrace (prefixWord ++ tailWord_1479250) baseStart_1479250 baseEnd_1479250 := by
    simpa [prefixWord, tailWord_1479250, baseEnd_1479250] using wordTrace_append hprefix tailTrace_1479250
  have hstable : (prefixWord ++ tailWord_1479250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479250).length < 2 ^ (prefixWord ++ tailWord_1479250).sum := by decide
  have hdescent : baseEnd_1479250 < baseStart_1479250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479280 : List Nat := [2, 1, 1, 1, 7, 1, 2, 8]
def baseStart_1479280 : Nat := 118140960795 + 1479280 * 2 ^ 59
def prefixEnd_1479280 : Nat := 4983230072969 + 3 ^ 40 * 1479280 * 2
def baseEnd_1479280 : Nat := 28132654169743612736923

theorem tailTrace_1479280 : CollatzResearch.WordTrace tailWord_1479280 prefixEnd_1479280 28132654169743612736923 := by
  unfold tailWord_1479280
  simp only [CollatzResearch.WordTrace]
  refine ⟨26976887040414337877669647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35969182720552450503559529 26976887040414337877669647)
  ·
    refine ⟨40465330560621506816504471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26976887040414337877669647 40465330560621506816504471)
    ·
      refine ⟨60697995840932260224756707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40465330560621506816504471 60697995840932260224756707)
      ·
        refine ⟨91046993761398390337135061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60697995840932260224756707 91046993761398390337135061)
        ·
          refine ⟨2133913916282774773526603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 91046993761398390337135061 2133913916282774773526603)
          ·
            refine ⟨3200870874424162160289905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2133913916282774773526603 3200870874424162160289905)
            ·
              refine ⟨2400653155818121620217429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3200870874424162160289905 2400653155818121620217429)
              ·
                refine ⟨28132654169743612736923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2400653155818121620217429 28132654169743612736923)
                ·
                  rfl

theorem cell23_1479280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 8].length) (baseStart_1479280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479280 prefixEnd_1479280 := by exact prefixLift 1479280
  have htrace : WordTrace (prefixWord ++ tailWord_1479280) baseStart_1479280 baseEnd_1479280 := by
    simpa [prefixWord, tailWord_1479280, baseEnd_1479280] using wordTrace_append hprefix tailTrace_1479280
  have hstable : (prefixWord ++ tailWord_1479280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479280).length < 2 ^ (prefixWord ++ tailWord_1479280).sum := by decide
  have hdescent : baseEnd_1479280 < baseStart_1479280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479324 : List Nat := [2, 2, 3, 2, 2, 1, 1, 4, 2, 1, 3]
def baseStart_1479324 : Nat := 118140960795 + 1479324 * 2 ^ 59
def prefixEnd_1479324 : Nat := 4983230072969 + 3 ^ 40 * 1479324 * 2
def baseEnd_1479324 : Nat := 759604255731875371746719

theorem tailTrace_1479324 : CollatzResearch.WordTrace tailWord_1479324 prefixEnd_1479324 759604255731875371746719 := by
  unfold tailWord_1479324
  simp only [CollatzResearch.WordTrace]
  refine ⟨26977689446334635634970513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35970252595112847513294017 26977689446334635634970513)
  ·
    refine ⟨20233267084750976726227885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26977689446334635634970513 20233267084750976726227885)
    ·
      refine ⟨7587475156781616272335457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20233267084750976726227885 7587475156781616272335457)
      ·
        refine ⟨5690606367586212204251593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7587475156781616272335457 5690606367586212204251593)
        ·
          refine ⟨4267954775689659153188695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5690606367586212204251593 4267954775689659153188695)
          ·
            refine ⟨6401932163534488729783043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4267954775689659153188695 6401932163534488729783043)
            ·
              refine ⟨9602898245301733094674565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6401932163534488729783043 9602898245301733094674565)
              ·
                refine ⟨1800543420994074955251481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9602898245301733094674565 1800543420994074955251481)
                ·
                  refine ⟨1350407565745556216438611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1800543420994074955251481 1350407565745556216438611)
                  ·
                    refine ⟨2025611348618334324657917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1350407565745556216438611 2025611348618334324657917)
                    ·
                      refine ⟨759604255731875371746719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2025611348618334324657917 759604255731875371746719)
                      ·
                        rfl

theorem cell23_1479324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_1479324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479324 prefixEnd_1479324 := by exact prefixLift 1479324
  have htrace : WordTrace (prefixWord ++ tailWord_1479324) baseStart_1479324 baseEnd_1479324 := by
    simpa [prefixWord, tailWord_1479324, baseEnd_1479324] using wordTrace_append hprefix tailTrace_1479324
  have hstable : (prefixWord ++ tailWord_1479324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479324).length < 2 ^ (prefixWord ++ tailWord_1479324).sum := by decide
  have hdescent : baseEnd_1479324 < baseStart_1479324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479347 : List Nat := [1, 1, 1, 2, 3, 4, 1, 3, 1, 4, 2]
def baseStart_1479347 : Nat := 118140960795 + 1479347 * 2 ^ 59
def prefixEnd_1479347 : Nat := 4983230072969 + 3 ^ 40 * 1479347 * 2
def baseEnd_1479347 : Nat := 759616065786928781759113

theorem tailTrace_1479347 : CollatzResearch.WordTrace tailWord_1479347 prefixEnd_1479347 759616065786928781759113 := by
  unfold tailWord_1479347
  simp only [CollatzResearch.WordTrace]
  refine ⟨53956217771585946198028295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35970811847723964132018863 53956217771585946198028295)
  ·
    refine ⟨80934326657378919297042443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53956217771585946198028295 80934326657378919297042443)
    ·
      refine ⟨121401489986068378945563665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80934326657378919297042443 121401489986068378945563665)
      ·
        refine ⟨91051117489551284209172749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121401489986068378945563665 91051117489551284209172749)
        ·
          refine ⟨34144169058581731578439781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91051117489551284209172749 34144169058581731578439781)
          ·
            refine ⟨6402031698484074670957459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34144169058581731578439781 6402031698484074670957459)
            ·
              refine ⟨9603047547726112006436189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6402031698484074670957459 9603047547726112006436189)
              ·
                refine ⟨3601142830397292002413571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9603047547726112006436189 3601142830397292002413571)
                ·
                  refine ⟨5401714245595938003620357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3601142830397292002413571 5401714245595938003620357)
                  ·
                    refine ⟨1012821421049238375678817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5401714245595938003620357 1012821421049238375678817)
                    ·
                      refine ⟨759616065786928781759113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1012821421049238375678817 759616065786928781759113)
                      ·
                        rfl

theorem cell23_1479347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 4, 2].length) (baseStart_1479347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479347 prefixEnd_1479347 := by exact prefixLift 1479347
  have htrace : WordTrace (prefixWord ++ tailWord_1479347) baseStart_1479347 baseEnd_1479347 := by
    simpa [prefixWord, tailWord_1479347, baseEnd_1479347] using wordTrace_append hprefix tailTrace_1479347
  have hstable : (prefixWord ++ tailWord_1479347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479347).length < 2 ^ (prefixWord ++ tailWord_1479347).sum := by decide
  have hdescent : baseEnd_1479347 < baseStart_1479347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479364 : List Nat := [2, 3, 3, 1, 1, 2, 2, 2, 1, 4, 2]
def baseStart_1479364 : Nat := 118140960795 + 1479364 * 2 ^ 59
def prefixEnd_1479364 : Nat := 4983230072969 + 3 ^ 40 * 1479364 * 2
def baseEnd_1479364 : Nat := 759624794958055215246535

theorem tailTrace_1479364 : CollatzResearch.WordTrace tailWord_1479364 prefixEnd_1479364 759624794958055215246535 := by
  unfold tailWord_1479364
  simp only [CollatzResearch.WordTrace]
  refine ⟨26978418906262179050698573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35971225208349572067598097 26978418906262179050698573)
  ·
    refine ⟨10116907089848317144011965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26978418906262179050698573 10116907089848317144011965)
    ·
      refine ⟨3793840158693118929004487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10116907089848317144011965 3793840158693118929004487)
      ·
        refine ⟨5690760238039678393506731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3793840158693118929004487 5690760238039678393506731)
        ·
          refine ⟨8536140357059517590260097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5690760238039678393506731 8536140357059517590260097)
          ·
            refine ⟨6402105267794638192695073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8536140357059517590260097 6402105267794638192695073)
            ·
              refine ⟨4801578950845978644521305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6402105267794638192695073 4801578950845978644521305)
              ·
                refine ⟨3601184213134483983390979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4801578950845978644521305 3601184213134483983390979)
                ·
                  refine ⟨5401776319701725975086469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3601184213134483983390979 5401776319701725975086469)
                  ·
                    refine ⟨1012833059944073620328713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5401776319701725975086469 1012833059944073620328713)
                    ·
                      refine ⟨759624794958055215246535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1012833059944073620328713 759624794958055215246535)
                      ·
                        rfl

theorem cell23_1479364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_1479364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479364 prefixEnd_1479364 := by exact prefixLift 1479364
  have htrace : WordTrace (prefixWord ++ tailWord_1479364) baseStart_1479364 baseEnd_1479364 := by
    simpa [prefixWord, tailWord_1479364, baseEnd_1479364] using wordTrace_append hprefix tailTrace_1479364
  have hstable : (prefixWord ++ tailWord_1479364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479364).length < 2 ^ (prefixWord ++ tailWord_1479364).sum := by decide
  have hdescent : baseEnd_1479364 < baseStart_1479364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479397 : List Nat := [1, 3, 1, 4, 1, 2, 2, 1, 2, 3, 3]
def baseStart_1479397 : Nat := 118140960795 + 1479397 * 2 ^ 59
def prefixEnd_1479397 : Nat := 4983230072969 + 3 ^ 40 * 1479397 * 2
def baseEnd_1479397 : Nat := 759641739819653586133883

theorem tailTrace_1479397 : CollatzResearch.WordTrace tailWord_1479397 prefixEnd_1479397 759641739819653586133883 := by
  unfold tailWord_1479397
  simp only [CollatzResearch.WordTrace]
  refine ⟨53958041421404804737348445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35972027614269869824898963 53958041421404804737348445)
  ·
    refine ⟨20234265533026801776505667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53958041421404804737348445 20234265533026801776505667)
    ·
      refine ⟨30351398299540202664758501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20234265533026801776505667 30351398299540202664758501)
      ·
        refine ⟨5690887181163787999642219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30351398299540202664758501 5690887181163787999642219)
        ·
          refine ⟨8536330771745681999463329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5690887181163787999642219 8536330771745681999463329)
          ·
            refine ⟨6402248078809261499597497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8536330771745681999463329 6402248078809261499597497)
            ·
              refine ⟨4801686059106946124698123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6402248078809261499597497 4801686059106946124698123)
              ·
                refine ⟨7202529088660419187047185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4801686059106946124698123 7202529088660419187047185)
                ·
                  refine ⟨5401896816495314390285389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7202529088660419187047185 5401896816495314390285389)
                  ·
                    refine ⟨2025711306185742896357021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5401896816495314390285389 2025711306185742896357021)
                    ·
                      refine ⟨759641739819653586133883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2025711306185742896357021 759641739819653586133883)
                      ·
                        rfl

theorem cell23_1479397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_1479397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479397 prefixEnd_1479397 := by exact prefixLift 1479397
  have htrace : WordTrace (prefixWord ++ tailWord_1479397) baseStart_1479397 baseEnd_1479397 := by
    simpa [prefixWord, tailWord_1479397, baseEnd_1479397] using wordTrace_append hprefix tailTrace_1479397
  have hstable : (prefixWord ++ tailWord_1479397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479397).length < 2 ^ (prefixWord ++ tailWord_1479397).sum := by decide
  have hdescent : baseEnd_1479397 < baseStart_1479397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479440 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 3]
def baseStart_1479440 : Nat := 118140960795 + 1479440 * 2 ^ 59
def prefixEnd_1479440 : Nat := 4983230072969 + 3 ^ 40 * 1479440 * 2
def baseEnd_1479440 : Nat := 759663819487796917896185

theorem tailTrace_1479440 : CollatzResearch.WordTrace tailWord_1479440 prefixEnd_1479440 759663819487796917896185 := by
  unfold tailWord_1479440
  simp only [CollatzResearch.WordTrace]
  refine ⟨26979804880124511540581887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35973073173499348720775849 26979804880124511540581887)
  ·
    refine ⟨40469707320186767310872831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26979804880124511540581887 40469707320186767310872831)
    ·
      refine ⟨60704560980280150966309247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40469707320186767310872831 60704560980280150966309247)
      ·
        refine ⟨91056841470420226449463871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60704560980280150966309247 91056841470420226449463871)
        ·
          refine ⟨136585262205630339674195807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91056841470420226449463871 136585262205630339674195807)
          ·
            refine ⟨204877893308445509511293711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136585262205630339674195807 204877893308445509511293711)
            ·
              refine ⟨307316839962668264266940567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204877893308445509511293711 307316839962668264266940567)
              ·
                refine ⟨460975259944002396400410851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307316839962668264266940567 460975259944002396400410851)
                ·
                  refine ⟨691462889916003594600616277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 460975259944002396400410851 691462889916003594600616277)
                  ·
                    refine ⟨2025770185300791781056493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 691462889916003594600616277 2025770185300791781056493)
                    ·
                      refine ⟨759663819487796917896185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2025770185300791781056493 759663819487796917896185)
                      ·
                        rfl

theorem cell23_1479440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 3].length) (baseStart_1479440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479440 prefixEnd_1479440 := by exact prefixLift 1479440
  have htrace : WordTrace (prefixWord ++ tailWord_1479440) baseStart_1479440 baseEnd_1479440 := by
    simpa [prefixWord, tailWord_1479440, baseEnd_1479440] using wordTrace_append hprefix tailTrace_1479440
  have hstable : (prefixWord ++ tailWord_1479440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479440).length < 2 ^ (prefixWord ++ tailWord_1479440).sum := by decide
  have hdescent : baseEnd_1479440 < baseStart_1479440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479457 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 4, 2, 3]
def baseStart_1479457 : Nat := 118140960795 + 1479457 * 2 ^ 59
def prefixEnd_1479457 : Nat := 4983230072969 + 3 ^ 40 * 1479457 * 2
def baseEnd_1479457 : Nat := 759672548658923351383607

theorem tailTrace_1479457 : CollatzResearch.WordTrace tailWord_1479457 prefixEnd_1479457 759672548658923351383607 := by
  unfold tailWord_1479457
  simp only [CollatzResearch.WordTrace]
  refine ⟨53960229801187434984532625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35973486534124956656355083 53960229801187434984532625)
  ·
    refine ⟨40470172350890576238399469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53960229801187434984532625 40470172350890576238399469)
    ·
      refine ⟨15176314631583966089399801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40470172350890576238399469 15176314631583966089399801)
      ·
        refine ⟨11382235973687974567049851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15176314631583966089399801 11382235973687974567049851)
        ·
          refine ⟨17073353960531961850574777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11382235973687974567049851 17073353960531961850574777)
          ·
            refine ⟨12805015470398971387931083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17073353960531961850574777 12805015470398971387931083)
            ·
              refine ⟨19207523205598457081896625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12805015470398971387931083 19207523205598457081896625)
              ·
                refine ⟨14405642404198842811422469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19207523205598457081896625 14405642404198842811422469)
                ·
                  refine ⟨2701057950787283027141713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14405642404198842811422469 2701057950787283027141713)
                  ·
                    refine ⟨2025793463090462270356285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2701057950787283027141713 2025793463090462270356285)
                    ·
                      refine ⟨759672548658923351383607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2025793463090462270356285 759672548658923351383607)
                      ·
                        rfl

theorem cell23_1479457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_1479457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479457 prefixEnd_1479457 := by exact prefixLift 1479457
  have htrace : WordTrace (prefixWord ++ tailWord_1479457) baseStart_1479457 baseEnd_1479457 := by
    simpa [prefixWord, tailWord_1479457, baseEnd_1479457] using wordTrace_append hprefix tailTrace_1479457
  have hstable : (prefixWord ++ tailWord_1479457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479457).length < 2 ^ (prefixWord ++ tailWord_1479457).sum := by decide
  have hdescent : baseEnd_1479457 < baseStart_1479457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479474 : List Nat := [3, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3]
def baseStart_1479474 : Nat := 118140960795 + 1479474 * 2 ^ 59
def prefixEnd_1479474 : Nat := 4983230072969 + 3 ^ 40 * 1479474 * 2
def baseEnd_1479474 : Nat := 759681277830049784871029

theorem tailTrace_1479474 : CollatzResearch.WordTrace tailWord_1479474 prefixEnd_1479474 759681277830049784871029 := by
  unfold tailWord_1479474
  simp only [CollatzResearch.WordTrace]
  refine ⟨13490212460531461721975369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35973899894750564591934317 13490212460531461721975369)
  ·
    refine ⟨10117659345398596291481527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13490212460531461721975369 10117659345398596291481527)
    ·
      refine ⟨15176489018097894437222291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10117659345398596291481527 15176489018097894437222291)
      ·
        refine ⟨22764733527146841655833437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15176489018097894437222291 22764733527146841655833437)
        ·
          refine ⟨8536775072680065620937539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22764733527146841655833437 8536775072680065620937539)
          ·
            refine ⟨12805162609020098431406309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8536775072680065620937539 12805162609020098431406309)
            ·
              refine ⟨2400967989191268455888683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12805162609020098431406309 2400967989191268455888683)
              ·
                refine ⟨3601451983786902683833025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2400967989191268455888683 3601451983786902683833025)
                ·
                  refine ⟨2701088987840177012874769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3601451983786902683833025 2701088987840177012874769)
                  ·
                    refine ⟨2025816740880132759656077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2701088987840177012874769 2025816740880132759656077)
                    ·
                      refine ⟨759681277830049784871029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2025816740880132759656077 759681277830049784871029)
                      ·
                        rfl

theorem cell23_1479474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_1479474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479474 prefixEnd_1479474 := by exact prefixLift 1479474
  have htrace : WordTrace (prefixWord ++ tailWord_1479474) baseStart_1479474 baseEnd_1479474 := by
    simpa [prefixWord, tailWord_1479474, baseEnd_1479474] using wordTrace_append hprefix tailTrace_1479474
  have hstable : (prefixWord ++ tailWord_1479474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479474).length < 2 ^ (prefixWord ++ tailWord_1479474).sum := by decide
  have hdescent : baseEnd_1479474 < baseStart_1479474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479537 : List Nat := [1, 2, 2, 2, 1, 4, 2, 2, 1, 6]
def baseStart_1479537 : Nat := 118140960795 + 1479537 * 2 ^ 59
def prefixEnd_1479537 : Nat := 4983230072969 + 3 ^ 40 * 1479537 * 2
def baseEnd_1479537 : Nat := 253237875703761012794413

theorem tailTrace_1479537 : CollatzResearch.WordTrace tailWord_1479537 prefixEnd_1479537 253237875703761012794413 := by
  unfold tailWord_1479537
  simp only [CollatzResearch.WordTrace]
  refine ⟨53963147640897608647444865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35975431760598405764963243 53963147640897608647444865)
  ·
    refine ⟨40472360730673206485583649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53963147640897608647444865 40472360730673206485583649)
    ·
      refine ⟨30354270548004904864187737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40472360730673206485583649 30354270548004904864187737)
      ·
        refine ⟨22765702911003678648140803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30354270548004904864187737 22765702911003678648140803)
        ·
          refine ⟨34148554366505517972211205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22765702911003678648140803 34148554366505517972211205)
          ·
            refine ⟨6402853943719784619789601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34148554366505517972211205 6402853943719784619789601)
            ·
              refine ⟨4802140457789838464842201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6402853943719784619789601 4802140457789838464842201)
              ·
                refine ⟨3601605343342378848631651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4802140457789838464842201 3601605343342378848631651)
                ·
                  refine ⟨5402408015013568272947477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3601605343342378848631651 5402408015013568272947477)
                  ·
                    refine ⟨253237875703761012794413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5402408015013568272947477 253237875703761012794413)
                    ·
                      rfl

theorem cell23_1479537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 6].length) (baseStart_1479537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479537 prefixEnd_1479537 := by exact prefixLift 1479537
  have htrace : WordTrace (prefixWord ++ tailWord_1479537) baseStart_1479537 baseEnd_1479537 := by
    simpa [prefixWord, tailWord_1479537, baseEnd_1479537] using wordTrace_append hprefix tailTrace_1479537
  have hstable : (prefixWord ++ tailWord_1479537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479537).length < 2 ^ (prefixWord ++ tailWord_1479537).sum := by decide
  have hdescent : baseEnd_1479537 < baseStart_1479537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479541 : List Nat := [1, 3, 4, 1, 1, 2, 4, 1, 1, 5]
def baseStart_1479541 : Nat := 118140960795 + 1479541 * 2 ^ 59
def prefixEnd_1479541 : Nat := 4983230072969 + 3 ^ 40 * 1479541 * 2
def baseEnd_1479541 : Nat := 253238560344633674244407

theorem tailTrace_1479541 : CollatzResearch.WordTrace tailWord_1479541 prefixEnd_1479541 253238560344633674244407 := by
  unfold tailWord_1479541
  simp only [CollatzResearch.WordTrace]
  refine ⟨53963293532883117330590477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35975529021922078220393651 53963293532883117330590477)
  ·
    refine ⟨20236235074831168998971429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53963293532883117330590477 20236235074831168998971429)
    ·
      refine ⟨3794294076530844187307143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20236235074831168998971429 3794294076530844187307143)
      ·
        refine ⟨5691441114796266280960715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3794294076530844187307143 5691441114796266280960715)
        ·
          refine ⟨8537161672194399421441073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5691441114796266280960715 8537161672194399421441073)
          ·
            refine ⟨6402871254145799566080805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8537161672194399421441073 6402871254145799566080805)
            ·
              refine ⟨1200538360152337418640151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6402871254145799566080805 1200538360152337418640151)
              ·
                refine ⟨1800807540228506127960227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1200538360152337418640151 1800807540228506127960227)
                ·
                  refine ⟨2701211310342759191940341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1800807540228506127960227 2701211310342759191940341)
                  ·
                    refine ⟨253238560344633674244407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2701211310342759191940341 253238560344633674244407)
                    ·
                      rfl

theorem cell23_1479541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_1479541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479541 prefixEnd_1479541 := by exact prefixLift 1479541
  have htrace : WordTrace (prefixWord ++ tailWord_1479541) baseStart_1479541 baseEnd_1479541 := by
    simpa [prefixWord, tailWord_1479541, baseEnd_1479541] using wordTrace_append hprefix tailTrace_1479541
  have hstable : (prefixWord ++ tailWord_1479541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479541).length < 2 ^ (prefixWord ++ tailWord_1479541).sum := by decide
  have hdescent : baseEnd_1479541 < baseStart_1479541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479561 : List Nat := [1, 2, 1, 1, 5, 2, 1, 3, 3, 2, 2]
def baseStart_1479561 : Nat := 118140960795 + 1479561 * 2 ^ 59
def prefixEnd_1479561 : Nat := 4983230072969 + 3 ^ 40 * 1479561 * 2
def baseEnd_1479561 : Nat := 759725950646990944483129

theorem tailTrace_1479561 : CollatzResearch.WordTrace tailWord_1479561 prefixEnd_1479561 759725950646990944483129 := by
  unfold tailWord_1479561
  simp only [CollatzResearch.WordTrace]
  refine ⟨53964022992810660746318537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35976015328540440497545691 53964022992810660746318537)
  ·
    refine ⟨40473017244607995559738903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53964022992810660746318537 40473017244607995559738903)
    ·
      refine ⟨60709525866911993339608355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40473017244607995559738903 60709525866911993339608355)
      ·
        refine ⟨91064288800367990009412533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60709525866911993339608355 91064288800367990009412533)
        ·
          refine ⟨8537277075034499063382425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91064288800367990009412533 8537277075034499063382425)
          ·
            refine ⟨6402957806275874297536819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8537277075034499063382425 6402957806275874297536819)
            ·
              refine ⟨9604436709413811446305229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6402957806275874297536819 9604436709413811446305229)
              ·
                refine ⟨3601663766030179292364461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9604436709413811446305229 3601663766030179292364461)
                ·
                  refine ⟨1350623912261317234636673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3601663766030179292364461 1350623912261317234636673)
                  ·
                    refine ⟨1012967934195987925977505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1350623912261317234636673 1012967934195987925977505)
                    ·
                      refine ⟨759725950646990944483129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1012967934195987925977505 759725950646990944483129)
                      ·
                        rfl

theorem cell23_1479561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3, 2, 2].length) (baseStart_1479561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479561 prefixEnd_1479561 := by exact prefixLift 1479561
  have htrace : WordTrace (prefixWord ++ tailWord_1479561) baseStart_1479561 baseEnd_1479561 := by
    simpa [prefixWord, tailWord_1479561, baseEnd_1479561] using wordTrace_append hprefix tailTrace_1479561
  have hstable : (prefixWord ++ tailWord_1479561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479561).length < 2 ^ (prefixWord ++ tailWord_1479561).sum := by decide
  have hdescent : baseEnd_1479561 < baseStart_1479561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479581 : List Nat := [1, 4, 2, 1, 2, 1, 4, 2, 1, 2, 3]
def baseStart_1479581 : Nat := 118140960795 + 1479581 * 2 ^ 59
def prefixEnd_1479581 : Nat := 4983230072969 + 3 ^ 40 * 1479581 * 2
def baseEnd_1479581 : Nat := 759736220260080866233037

theorem tailTrace_1479581 : CollatzResearch.WordTrace tailWord_1479581 prefixEnd_1479581 759736220260080866233037 := by
  unfold tailWord_1479581
  simp only [CollatzResearch.WordTrace]
  refine ⟨53964752452738204162046597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35976501635158802774697731 53964752452738204162046597)
  ·
    refine ⟨10118391084888413280383737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53964752452738204162046597 10118391084888413280383737)
    ·
      refine ⟨7588793313666309960287803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10118391084888413280383737 7588793313666309960287803)
      ·
        refine ⟨11383189970499464940431705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7588793313666309960287803 11383189970499464940431705)
        ·
          refine ⟨8537392477874598705323779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11383189970499464940431705 8537392477874598705323779)
          ·
            refine ⟨12806088716811898057985669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8537392477874598705323779 12806088716811898057985669)
            ·
              refine ⟨2401141634402230885872313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12806088716811898057985669 2401141634402230885872313)
              ·
                refine ⟨1800856225801673164404235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2401141634402230885872313 1800856225801673164404235)
                ·
                  refine ⟨2701284338702509746606353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1800856225801673164404235 2701284338702509746606353)
                  ·
                    refine ⟨2025963254026882309954765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2701284338702509746606353 2025963254026882309954765)
                    ·
                      refine ⟨759736220260080866233037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2025963254026882309954765 759736220260080866233037)
                      ·
                        rfl

theorem cell23_1479581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_1479581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479581 prefixEnd_1479581 := by exact prefixLift 1479581
  have htrace : WordTrace (prefixWord ++ tailWord_1479581) baseStart_1479581 baseEnd_1479581 := by
    simpa [prefixWord, tailWord_1479581, baseEnd_1479581] using wordTrace_append hprefix tailTrace_1479581
  have hstable : (prefixWord ++ tailWord_1479581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479581).length < 2 ^ (prefixWord ++ tailWord_1479581).sum := by decide
  have hdescent : baseEnd_1479581 < baseStart_1479581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479606 : List Nat := [5, 1, 4, 1, 1, 1, 3, 2, 1, 1, 3]
def baseStart_1479606 : Nat := 118140960795 + 1479606 * 2 ^ 59
def prefixEnd_1479606 : Nat := 4983230072969 + 3 ^ 40 * 1479606 * 2
def baseEnd_1479606 : Nat := 759749057276443268420423

theorem tailTrace_1479606 : CollatzResearch.WordTrace tailWord_1479606 prefixEnd_1479606 759749057276443268420423 := by
  unfold tailWord_1479606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3372854017352977089481667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35977109518431755621137781 3372854017352977089481667)
  ·
    refine ⟨5059281026029465634222501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3372854017352977089481667 5059281026029465634222501)
    ·
      refine ⟨948615192380524806416719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5059281026029465634222501 948615192380524806416719)
      ·
        refine ⟨1422922788570787209625079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 948615192380524806416719 1422922788570787209625079)
        ·
          refine ⟨2134384182856180814437619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1422922788570787209625079 2134384182856180814437619)
          ·
            refine ⟨3201576274284271221656429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2134384182856180814437619 3201576274284271221656429)
            ·
              refine ⟨1200591102856601708121161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3201576274284271221656429 1200591102856601708121161)
              ·
                refine ⟨900443327142451281090871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1200591102856601708121161 900443327142451281090871)
                ·
                  refine ⟨1350664990713676921636307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 900443327142451281090871 1350664990713676921636307)
                  ·
                    refine ⟨2025997486070515382454461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1350664990713676921636307 2025997486070515382454461)
                    ·
                      refine ⟨759749057276443268420423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2025997486070515382454461 759749057276443268420423)
                      ·
                        rfl

theorem cell23_1479606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_1479606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479606 prefixEnd_1479606 := by exact prefixLift 1479606
  have htrace : WordTrace (prefixWord ++ tailWord_1479606) baseStart_1479606 baseEnd_1479606 := by
    simpa [prefixWord, tailWord_1479606, baseEnd_1479606] using wordTrace_append hprefix tailTrace_1479606
  have hstable : (prefixWord ++ tailWord_1479606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479606).length < 2 ^ (prefixWord ++ tailWord_1479606).sum := by decide
  have hdescent : baseEnd_1479606 < baseStart_1479606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479629 : List Nat := [1, 6, 3, 1, 2, 1, 1, 2, 1, 1, 4]
def baseStart_1479629 : Nat := 118140960795 + 1479629 * 2 ^ 59
def prefixEnd_1479629 : Nat := 4983230072969 + 3 ^ 40 * 1479629 * 2
def baseEnd_1479629 : Nat := 759760867331496678432817

theorem tailTrace_1479629 : CollatzResearch.WordTrace tailWord_1479629 prefixEnd_1479629 759760867331496678432817 := by
  unfold tailWord_1479629
  simp only [CollatzResearch.WordTrace]
  refine ⟨53966503156564308359793941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35977668771042872239862627 53966503156564308359793941)
  ·
    refine ⟨2529679835463951954365341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 53966503156564308359793941 2529679835463951954365341)
    ·
      refine ⟨948629938298981982887003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2529679835463951954365341 948629938298981982887003)
      ·
        refine ⟨1422944907448472974330505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 948629938298981982887003 1422944907448472974330505)
        ·
          refine ⟨1067208680586354730747879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1422944907448472974330505 1067208680586354730747879)
          ·
            refine ⟨1600813020879532096121819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1067208680586354730747879 1600813020879532096121819)
            ·
              refine ⟨2401219531319298144182729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1600813020879532096121819 2401219531319298144182729)
              ·
                refine ⟨1800914648489473608137047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2401219531319298144182729 1800914648489473608137047)
                ·
                  refine ⟨2701371972734210412205571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1800914648489473608137047 2701371972734210412205571)
                  ·
                    refine ⟨4052057959101315618308357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2701371972734210412205571 4052057959101315618308357)
                    ·
                      refine ⟨759760867331496678432817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4052057959101315618308357 759760867331496678432817)
                      ·
                        rfl

theorem cell23_1479629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_1479629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479629 prefixEnd_1479629 := by exact prefixLift 1479629
  have htrace : WordTrace (prefixWord ++ tailWord_1479629) baseStart_1479629 baseEnd_1479629 := by
    simpa [prefixWord, tailWord_1479629, baseEnd_1479629] using wordTrace_append hprefix tailTrace_1479629
  have hstable : (prefixWord ++ tailWord_1479629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479629).length < 2 ^ (prefixWord ++ tailWord_1479629).sum := by decide
  have hdescent : baseEnd_1479629 < baseStart_1479629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1479651 : List Nat := [1, 1, 1, 6, 1, 1, 3, 2, 1, 4, 2]
def baseStart_1479651 : Nat := 118140960795 + 1479651 * 2 ^ 59
def prefixEnd_1479651 : Nat := 4983230072969 + 3 ^ 40 * 1479651 * 2
def baseEnd_1479651 : Nat := 759772163905895592357715

theorem tailTrace_1479651 : CollatzResearch.WordTrace tailWord_1479651 prefixEnd_1479651 759772163905895592357715 := by
  unfold tailWord_1479651
  simp only [CollatzResearch.WordTrace]
  refine ⟨53967305562484606117094807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35978203708323070744729871 53967305562484606117094807)
  ·
    refine ⟨80950958343726909175642211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53967305562484606117094807 80950958343726909175642211)
    ·
      refine ⟨121426437515590363763463317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80950958343726909175642211 121426437515590363763463317)
      ·
        refine ⟨5691864258543298301412343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 121426437515590363763463317 5691864258543298301412343)
        ·
          refine ⟨8537796387814947452118515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5691864258543298301412343 8537796387814947452118515)
          ·
            refine ⟨12806694581722421178177773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8537796387814947452118515 12806694581722421178177773)
            ·
              refine ⟨4802510468145907941816665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12806694581722421178177773 4802510468145907941816665)
              ·
                refine ⟨3601882851109430956362499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4802510468145907941816665 3601882851109430956362499)
                ·
                  refine ⟨5402824276664146434543749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3601882851109430956362499 5402824276664146434543749)
                  ·
                    refine ⟨1013029551874527456476953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5402824276664146434543749 1013029551874527456476953)
                    ·
                      refine ⟨759772163905895592357715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1013029551874527456476953 759772163905895592357715)
                      ·
                        rfl

theorem cell23_1479651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_1479651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1479651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1479651 prefixEnd_1479651 := by exact prefixLift 1479651
  have htrace : WordTrace (prefixWord ++ tailWord_1479651) baseStart_1479651 baseEnd_1479651 := by
    simpa [prefixWord, tailWord_1479651, baseEnd_1479651] using wordTrace_append hprefix tailTrace_1479651
  have hstable : (prefixWord ++ tailWord_1479651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1479651).length < 2 ^ (prefixWord ++ tailWord_1479651).sum := by decide
  have hdescent : baseEnd_1479651 < baseStart_1479651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1479651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
