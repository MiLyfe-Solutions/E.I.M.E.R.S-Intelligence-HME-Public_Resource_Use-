import V185TrunkScan23Chunk1048

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6211118 : List Nat := [4, 1, 3, 1, 2, 3, 2, 2, 1, 1, 3]
def baseStart_6211118 : Nat := 118140960795 + 6211118 * 2 ^ 59
def prefixEnd_6211118 : Nat := 4983230072969 + 3 ^ 40 * 6211118 * 2
def baseEnd_6211118 : Nat := 3189288935792535205960595

theorem tailTrace_6211118 : CollatzResearch.WordTrace tailWord_6211118 prefixEnd_6211118 3189288935792535205960595 := by
  unfold tailWord_6211118
  simp only [CollatzResearch.WordTrace]
  refine ⟨28317260539023466918367251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151025389541458490231292005 28317260539023466918367251)
  ·
    refine ⟨42475890808535200377550877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28317260539023466918367251 42475890808535200377550877)
    ·
      refine ⟨15928459053200700141581579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42475890808535200377550877 15928459053200700141581579)
      ·
        refine ⟨23892688579801050212372369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15928459053200700141581579 23892688579801050212372369)
        ·
          refine ⟨17919516434850787659279277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23892688579801050212372369 17919516434850787659279277)
          ·
            refine ⟨6719818663069045372229729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17919516434850787659279277 6719818663069045372229729)
            ·
              refine ⟨5039863997301784029172297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6719818663069045372229729 5039863997301784029172297)
              ·
                refine ⟨3779897997976338021879223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5039863997301784029172297 3779897997976338021879223)
                ·
                  refine ⟨5669846996964507032818835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3779897997976338021879223 5669846996964507032818835)
                  ·
                    refine ⟨8504770495446760549228253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5669846996964507032818835 8504770495446760549228253)
                    ·
                      refine ⟨3189288935792535205960595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8504770495446760549228253 3189288935792535205960595)
                      ·
                        rfl

theorem cell23_6211118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_6211118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211118 prefixEnd_6211118 := by exact prefixLift 6211118
  have htrace : WordTrace (prefixWord ++ tailWord_6211118) baseStart_6211118 baseEnd_6211118 := by
    simpa [prefixWord, tailWord_6211118, baseEnd_6211118] using wordTrace_append hprefix tailTrace_6211118
  have hstable : (prefixWord ++ tailWord_6211118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211118).length < 2 ^ (prefixWord ++ tailWord_6211118).sum := by decide
  have hdescent : baseEnd_6211118 < baseStart_6211118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211153 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 2, 2, 5]
def baseStart_6211153 : Nat := 118140960795 + 6211153 * 2 ^ 59
def prefixEnd_6211153 : Nat := 4983230072969 + 3 ^ 40 * 6211153 * 2
def baseEnd_6211153 : Nat := 3189306907615442569022933

theorem tailTrace_6211153 : CollatzResearch.WordTrace tailWord_6211153 prefixEnd_6211153 3189306907615442569022933 := by
  unfold tailWord_6211153
  simp only [CollatzResearch.WordTrace]
  refine ⟨226539360867060936324462113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151026240578040624216308075 226539360867060936324462113)
  ·
    refine ⟨169904520650295702243346585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226539360867060936324462113 169904520650295702243346585)
    ·
      refine ⟨127428390487721776682509939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169904520650295702243346585 127428390487721776682509939)
      ·
        refine ⟨191142585731582665023764909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127428390487721776682509939 191142585731582665023764909)
        ·
          refine ⟨71678469649343499383911841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191142585731582665023764909 71678469649343499383911841)
          ·
            refine ⟨53758852237007624537933881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71678469649343499383911841 53758852237007624537933881)
            ·
              refine ⟨40319139177755718403450411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53758852237007624537933881 40319139177755718403450411)
              ·
                refine ⟨60478708766633577605175617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40319139177755718403450411 60478708766633577605175617)
                ·
                  refine ⟨45359031574975183203881713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60478708766633577605175617 45359031574975183203881713)
                  ·
                    refine ⟨34019273681231387402911285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45359031574975183203881713 34019273681231387402911285)
                    ·
                      refine ⟨3189306907615442569022933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34019273681231387402911285 3189306907615442569022933)
                      ·
                        rfl

theorem cell23_6211153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_6211153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211153 prefixEnd_6211153 := by exact prefixLift 6211153
  have htrace : WordTrace (prefixWord ++ tailWord_6211153) baseStart_6211153 baseEnd_6211153 := by
    simpa [prefixWord, tailWord_6211153, baseEnd_6211153] using wordTrace_append hprefix tailTrace_6211153
  have hstable : (prefixWord ++ tailWord_6211153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211153).length < 2 ^ (prefixWord ++ tailWord_6211153).sum := by decide
  have hdescent : baseEnd_6211153 < baseStart_6211153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211183 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 5]
def baseStart_6211183 : Nat := 118140960795 + 6211183 * 2 ^ 59
def prefixEnd_6211183 : Nat := 4983230072969 + 3 ^ 40 * 6211183 * 2
def baseEnd_6211183 : Nat := 3189322312035077451647795

theorem tailTrace_6211183 : CollatzResearch.WordTrace tailWord_6211183 prefixEnd_6211183 3189322312035077451647795 := by
  unfold tailWord_6211183
  simp only [CollatzResearch.WordTrace]
  refine ⟨226540455056952251448054203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151026970037968167632036135 226540455056952251448054203)
  ·
    refine ⟨339810682585428377172081305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226540455056952251448054203 339810682585428377172081305)
    ·
      refine ⟨254858011939071282879060979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339810682585428377172081305 254858011939071282879060979)
      ·
        refine ⟨382287017908606924318591469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254858011939071282879060979 382287017908606924318591469)
        ·
          refine ⟨143357631715727596619471801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 382287017908606924318591469 143357631715727596619471801)
          ·
            refine ⟨107518223786795697464603851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143357631715727596619471801 107518223786795697464603851)
            ·
              refine ⟨161277335680193546196905777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107518223786795697464603851 161277335680193546196905777)
              ·
                refine ⟨120958001760145159647679333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161277335680193546196905777 120958001760145159647679333)
                ·
                  refine ⟨22679625330027217433939875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120958001760145159647679333 22679625330027217433939875)
                  ·
                    refine ⟨34019437995040826150909813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22679625330027217433939875 34019437995040826150909813)
                    ·
                      refine ⟨3189322312035077451647795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34019437995040826150909813 3189322312035077451647795)
                      ·
                        rfl

theorem cell23_6211183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 5].length) (baseStart_6211183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211183 prefixEnd_6211183 := by exact prefixLift 6211183
  have htrace : WordTrace (prefixWord ++ tailWord_6211183) baseStart_6211183 baseEnd_6211183 := by
    simpa [prefixWord, tailWord_6211183, baseEnd_6211183] using wordTrace_append hprefix tailTrace_6211183
  have hstable : (prefixWord ++ tailWord_6211183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211183).length < 2 ^ (prefixWord ++ tailWord_6211183).sum := by decide
  have hdescent : baseEnd_6211183 < baseStart_6211183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211214 : List Nat := [4, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2]
def baseStart_6211214 : Nat := 118140960795 + 6211214 * 2 ^ 59
def prefixEnd_6211214 : Nat := 4983230072969 + 3 ^ 40 * 6211214 * 2
def baseEnd_6211214 : Nat := 3189338229935366830360153

theorem tailTrace_6211214 : CollatzResearch.WordTrace tailWord_6211214 prefixEnd_6211214 3189338229935366830360153 := by
  unfold tailWord_6211214
  simp only [CollatzResearch.WordTrace]
  refine ⟨28317698214979992967804087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151027723813226629161621797 28317698214979992967804087)
  ·
    refine ⟨42476547322469989451706131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28317698214979992967804087 42476547322469989451706131)
    ·
      refine ⟨63714820983704984177559197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42476547322469989451706131 63714820983704984177559197)
      ·
        refine ⟨23893057868889369066584699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63714820983704984177559197 23893057868889369066584699)
        ·
          refine ⟨35839586803334053599877049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23893057868889369066584699 35839586803334053599877049)
          ·
            refine ⟨26879690102500540199907787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35839586803334053599877049 26879690102500540199907787)
            ·
              refine ⟨40319535153750810299861681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26879690102500540199907787 40319535153750810299861681)
              ·
                refine ⟨30239651365313107724896261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40319535153750810299861681 30239651365313107724896261)
                ·
                  refine ⟨5669934630996207698418049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30239651365313107724896261 5669934630996207698418049)
                  ·
                    refine ⟨4252450973247155773813537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5669934630996207698418049 4252450973247155773813537)
                    ·
                      refine ⟨3189338229935366830360153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4252450973247155773813537 3189338229935366830360153)
                      ·
                        rfl

theorem cell23_6211214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_6211214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211214 prefixEnd_6211214 := by exact prefixLift 6211214
  have htrace : WordTrace (prefixWord ++ tailWord_6211214) baseStart_6211214 baseEnd_6211214 := by
    simpa [prefixWord, tailWord_6211214, baseEnd_6211214] using wordTrace_append hprefix tailTrace_6211214
  have hstable : (prefixWord ++ tailWord_6211214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211214).length < 2 ^ (prefixWord ++ tailWord_6211214).sum := by decide
  have hdescent : baseEnd_6211214 < baseStart_6211214 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211273 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 11]
def baseStart_6211273 : Nat := 118140960795 + 6211273 * 2 ^ 59
def prefixEnd_6211273 : Nat := 4983230072969 + 3 ^ 40 * 6211273 * 2
def baseEnd_6211273 : Nat := 3189368525293982099522381

theorem tailTrace_6211273 : CollatzResearch.WordTrace tailWord_6211273 prefixEnd_6211273 3189368525293982099522381 := by
  unfold tailWord_6211273
  simp only [CollatzResearch.WordTrace]
  refine ⟨226543737626626196818830473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151029158417750797879220315 226543737626626196818830473)
  ·
    refine ⟨169907803219969647614122855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226543737626626196818830473 169907803219969647614122855)
    ·
      refine ⟨254861704829954471421184283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169907803219969647614122855 254861704829954471421184283)
      ·
        refine ⟨382292557244931707131776425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254861704829954471421184283 382292557244931707131776425)
        ·
          refine ⟨286719417933698780348832319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382292557244931707131776425 286719417933698780348832319)
          ·
            refine ⟨430079126900548170523248479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286719417933698780348832319 430079126900548170523248479)
            ·
              refine ⟨645118690350822255784872719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430079126900548170523248479 645118690350822255784872719)
              ·
                refine ⟨967678035526233383677309079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645118690350822255784872719 967678035526233383677309079)
                ·
                  refine ⟨1451517053289350075515963619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 967678035526233383677309079 1451517053289350075515963619)
                  ·
                    refine ⟨2177275579934025113273945429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1451517053289350075515963619 2177275579934025113273945429)
                    ·
                      refine ⟨3189368525293982099522381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 2177275579934025113273945429 3189368525293982099522381)
                      ·
                        rfl

theorem cell23_6211273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_6211273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211273 prefixEnd_6211273 := by exact prefixLift 6211273
  have htrace : WordTrace (prefixWord ++ tailWord_6211273) baseStart_6211273 baseEnd_6211273 := by
    simpa [prefixWord, tailWord_6211273, baseEnd_6211273] using wordTrace_append hprefix tailTrace_6211273
  have hstable : (prefixWord ++ tailWord_6211273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211273).length < 2 ^ (prefixWord ++ tailWord_6211273).sum := by decide
  have hdescent : baseEnd_6211273 < baseStart_6211273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211280 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 7, 4]
def baseStart_6211280 : Nat := 118140960795 + 6211280 * 2 ^ 59
def prefixEnd_6211280 : Nat := 4983230072969 + 3 ^ 40 * 6211280 * 2
def baseEnd_6211280 : Nat := 1063124039886187857378283

theorem tailTrace_6211280 : CollatzResearch.WordTrace tailWord_6211280 prefixEnd_6211280 1063124039886187857378283 := by
  unfold tailWord_6211280
  simp only [CollatzResearch.WordTrace]
  refine ⟨113271996468800418507167647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151029328625067224676223529 113271996468800418507167647)
  ·
    refine ⟨169907994703200627760751471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113271996468800418507167647 169907994703200627760751471)
    ·
      refine ⟨254861992054800941641127207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169907994703200627760751471 254861992054800941641127207)
      ·
        refine ⟨382292988082201412461690811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254861992054800941641127207 382292988082201412461690811)
        ·
          refine ⟨573439482123302118692536217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382292988082201412461690811 573439482123302118692536217)
          ·
            refine ⟨430079611592476589019402163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 573439482123302118692536217 430079611592476589019402163)
            ·
              refine ⟨645119417388714883529103245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430079611592476589019402163 645119417388714883529103245)
              ·
                refine ⟨241919781520768081323413717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 645119417388714883529103245 241919781520768081323413717)
                ·
                  refine ⟨5669994879393001906017509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 241919781520768081323413717 5669994879393001906017509)
                  ·
                    refine ⟨1063124039886187857378283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5669994879393001906017509 1063124039886187857378283)
                    ·
                      rfl

theorem cell23_6211280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 7, 4].length) (baseStart_6211280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211280 prefixEnd_6211280 := by exact prefixLift 6211280
  have htrace : WordTrace (prefixWord ++ tailWord_6211280) baseStart_6211280 baseEnd_6211280 := by
    simpa [prefixWord, tailWord_6211280, baseEnd_6211280] using wordTrace_append hprefix tailTrace_6211280
  have hstable : (prefixWord ++ tailWord_6211280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211280).length < 2 ^ (prefixWord ++ tailWord_6211280).sum := by decide
  have hdescent : baseEnd_6211280 < baseStart_6211280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211287 : List Nat := [1, 1, 3, 2, 1, 3, 2, 2, 2, 4, 2]
def baseStart_6211287 : Nat := 118140960795 + 6211287 * 2 ^ 59
def prefixEnd_6211287 : Nat := 4983230072969 + 3 ^ 40 * 6211287 * 2
def baseEnd_6211287 : Nat := 3189375714023145044747317

theorem tailTrace_6211287 : CollatzResearch.WordTrace tailWord_6211287 prefixEnd_6211287 3189375714023145044747317 := by
  unfold tailWord_6211287
  simp only [CollatzResearch.WordTrace]
  refine ⟨226544248248575477209840115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151029498832383651473226743 226544248248575477209840115)
  ·
    refine ⟨339816372372863215814760173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226544248248575477209840115 339816372372863215814760173)
    ·
      refine ⟨127431139639823705930535065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 339816372372863215814760173 127431139639823705930535065)
      ·
        refine ⟨95573354729867779447901299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127431139639823705930535065 95573354729867779447901299)
        ·
          refine ⟨143360032094801669171851949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95573354729867779447901299 143360032094801669171851949)
          ·
            refine ⟨53760012035550625939444481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143360032094801669171851949 53760012035550625939444481)
            ·
              refine ⟨40320009026662969454583361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53760012035550625939444481 40320009026662969454583361)
              ·
                refine ⟨30240006769997227090937521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40320009026662969454583361 30240006769997227090937521)
                ·
                  refine ⟨22680005077497920318203141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30240006769997227090937521 22680005077497920318203141)
                  ·
                    refine ⟨4252500952030860059663089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22680005077497920318203141 4252500952030860059663089)
                    ·
                      refine ⟨3189375714023145044747317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4252500952030860059663089 3189375714023145044747317)
                      ·
                        rfl

theorem cell23_6211287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 4, 2].length) (baseStart_6211287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211287 prefixEnd_6211287 := by exact prefixLift 6211287
  have htrace : WordTrace (prefixWord ++ tailWord_6211287) baseStart_6211287 baseEnd_6211287 := by
    simpa [prefixWord, tailWord_6211287, baseEnd_6211287] using wordTrace_append hprefix tailTrace_6211287
  have hstable : (prefixWord ++ tailWord_6211287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211287).length < 2 ^ (prefixWord ++ tailWord_6211287).sum := by decide
  have hdescent : baseEnd_6211287 < baseStart_6211287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211304 : List Nat := [2, 1, 4, 1, 3, 2, 1, 1, 2, 4, 2]
def baseStart_6211304 : Nat := 118140960795 + 6211304 * 2 ^ 59
def prefixEnd_6211304 : Nat := 4983230072969 + 3 ^ 40 * 6211304 * 2
def baseEnd_6211304 : Nat := 3189384443194271478234739

theorem tailTrace_6211304 : CollatzResearch.WordTrace tailWord_6211304 prefixEnd_6211304 3189384443194271478234739 := by
  unfold tailWord_6211304
  simp only [CollatzResearch.WordTrace]
  refine ⟨113272434144756944556604483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151029912193009259408805977 113272434144756944556604483)
  ·
    refine ⟨169908651217135416834906725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113272434144756944556604483 169908651217135416834906725)
    ·
      refine ⟨31857872103212890656545011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169908651217135416834906725 31857872103212890656545011)
      ·
        refine ⟨47786808154819335984817517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31857872103212890656545011 47786808154819335984817517)
        ·
          refine ⟨17920053058057250994306569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47786808154819335984817517 17920053058057250994306569)
          ·
            refine ⟨13440039793542938245729927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17920053058057250994306569 13440039793542938245729927)
            ·
              refine ⟨20160059690314407368594891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13440039793542938245729927 20160059690314407368594891)
              ·
                refine ⟨30240089535471611052892337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20160059690314407368594891 30240089535471611052892337)
                ·
                  refine ⟨22680067151603708289669253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30240089535471611052892337 22680067151603708289669253)
                  ·
                    refine ⟨4252512590925695304312985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22680067151603708289669253 4252512590925695304312985)
                    ·
                      refine ⟨3189384443194271478234739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4252512590925695304312985 3189384443194271478234739)
                      ·
                        rfl

theorem cell23_6211304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_6211304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211304 prefixEnd_6211304 := by exact prefixLift 6211304
  have htrace : WordTrace (prefixWord ++ tailWord_6211304) baseStart_6211304 baseEnd_6211304 := by
    simpa [prefixWord, tailWord_6211304, baseEnd_6211304] using wordTrace_append hprefix tailTrace_6211304
  have hstable : (prefixWord ++ tailWord_6211304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211304).length < 2 ^ (prefixWord ++ tailWord_6211304).sum := by decide
  have hdescent : baseEnd_6211304 < baseStart_6211304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211320 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 1, 7, 3]
def baseStart_6211320 : Nat := 118140960795 + 6211320 * 2 ^ 59
def prefixEnd_6211320 : Nat := 4983230072969 + 3 ^ 40 * 6211320 * 2
def baseEnd_6211320 : Nat := 3189392658884743415634665

theorem tailTrace_6211320 : CollatzResearch.WordTrace tailWord_6211320 prefixEnd_6211320 3189392658884743415634665 := by
  unfold tailWord_6211320
  simp only [CollatzResearch.WordTrace]
  refine ⟨113272725928727961922895707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151030301238303949230527609 113272725928727961922895707)
  ·
    refine ⟨169909088893091942884343561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113272725928727961922895707 169909088893091942884343561)
    ·
      refine ⟨127431816669818957163257671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169909088893091942884343561 127431816669818957163257671)
      ·
        refine ⟨191147725004728435744886507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127431816669818957163257671 191147725004728435744886507)
        ·
          refine ⟨286721587507092653617329761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191147725004728435744886507 286721587507092653617329761)
          ·
            refine ⟨215041190630319490212997321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286721587507092653617329761 215041190630319490212997321)
            ·
              refine ⟨161280892972739617659747991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215041190630319490212997321 161280892972739617659747991)
              ·
                refine ⟨241921339459109426489621987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161280892972739617659747991 241921339459109426489621987)
                ·
                  refine ⟨362882009188664139734432981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241921339459109426489621987 362882009188664139734432981)
                  ·
                    refine ⟨8505047090359315775025773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 362882009188664139734432981 8505047090359315775025773)
                    ·
                      refine ⟨3189392658884743415634665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8505047090359315775025773 3189392658884743415634665)
                      ·
                        rfl

theorem cell23_6211320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 7, 3].length) (baseStart_6211320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211320 prefixEnd_6211320 := by exact prefixLift 6211320
  have htrace : WordTrace (prefixWord ++ tailWord_6211320) baseStart_6211320 baseEnd_6211320 := by
    simpa [prefixWord, tailWord_6211320, baseEnd_6211320] using wordTrace_append hprefix tailTrace_6211320
  have hstable : (prefixWord ++ tailWord_6211320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211320).length < 2 ^ (prefixWord ++ tailWord_6211320).sum := by decide
  have hdescent : baseEnd_6211320 < baseStart_6211320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211337 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 7, 1, 3]
def baseStart_6211337 : Nat := 118140960795 + 6211337 * 2 ^ 59
def prefixEnd_6211337 : Nat := 4983230072969 + 3 ^ 40 * 6211337 * 2
def baseEnd_6211337 : Nat := 3189401388055869849122087

theorem tailTrace_6211337 : CollatzResearch.WordTrace tailWord_6211337 prefixEnd_6211337 3189401388055869849122087 := by
  unfold tailWord_6211337
  simp only [CollatzResearch.WordTrace]
  refine ⟨226546071898394335749160265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151030714598929557166106843 226546071898394335749160265)
  ·
    refine ⟨169909553923795751811870199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226546071898394335749160265 169909553923795751811870199)
    ·
      refine ⟨254864330885693627717805299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169909553923795751811870199 254864330885693627717805299)
      ·
        refine ⟨382296496328540441576707949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254864330885693627717805299 382296496328540441576707949)
        ·
          refine ⟨143361186123202665591265481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 382296496328540441576707949 143361186123202665591265481)
          ·
            refine ⟨107520889592401999193449111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143361186123202665591265481 107520889592401999193449111)
            ·
              refine ⟨161281334388602998790173667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107520889592401999193449111 161281334388602998790173667)
              ·
                refine ⟨241922001582904498185260501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161281334388602998790173667 241922001582904498185260501)
                ·
                  refine ⟨5670046912099324176217043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 241922001582904498185260501 5670046912099324176217043)
                  ·
                    refine ⟨8505070368148986264325565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5670046912099324176217043 8505070368148986264325565)
                    ·
                      refine ⟨3189401388055869849122087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8505070368148986264325565 3189401388055869849122087)
                      ·
                        rfl

theorem cell23_6211337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7, 1, 3].length) (baseStart_6211337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211337 prefixEnd_6211337 := by exact prefixLift 6211337
  have htrace : WordTrace (prefixWord ++ tailWord_6211337) baseStart_6211337 baseEnd_6211337 := by
    simpa [prefixWord, tailWord_6211337, baseEnd_6211337] using wordTrace_append hprefix tailTrace_6211337
  have hstable : (prefixWord ++ tailWord_6211337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211337).length < 2 ^ (prefixWord ++ tailWord_6211337).sum := by decide
  have hdescent : baseEnd_6211337 < baseStart_6211337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211354 : List Nat := [3, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3]
def baseStart_6211354 : Nat := 118140960795 + 6211354 * 2 ^ 59
def prefixEnd_6211354 : Nat := 4983230072969 + 3 ^ 40 * 6211354 * 2
def baseEnd_6211354 : Nat := 3189410117226996282609509

theorem tailTrace_6211354 : CollatzResearch.WordTrace tailWord_6211354 prefixEnd_6211354 3189410117226996282609509 := by
  unfold tailWord_6211354
  simp only [CollatzResearch.WordTrace]
  refine ⟨56636672984833186913132279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151031127959555165101686077 56636672984833186913132279)
  ·
    refine ⟨84955009477249780369698419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56636672984833186913132279 84955009477249780369698419)
    ·
      refine ⟨127432514215874670554547629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84955009477249780369698419 127432514215874670554547629)
      ·
        refine ⟨47787192830953001457955361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127432514215874670554547629 47787192830953001457955361)
        ·
          refine ⟨35840394623214751093466521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47787192830953001457955361 35840394623214751093466521)
          ·
            refine ⟨26880295967411063320099891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35840394623214751093466521 26880295967411063320099891)
            ·
              refine ⟨40320443951116594980149837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26880295967411063320099891 40320443951116594980149837)
              ·
                refine ⟨15120166481668723117556189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40320443951116594980149837 15120166481668723117556189)
                ·
                  refine ⟨5670062430625771169083571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15120166481668723117556189 5670062430625771169083571)
                  ·
                    refine ⟨8505093645938656753625357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5670062430625771169083571 8505093645938656753625357)
                    ·
                      refine ⟨3189410117226996282609509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8505093645938656753625357 3189410117226996282609509)
                      ·
                        rfl

theorem cell23_6211354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_6211354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211354 prefixEnd_6211354 := by exact prefixLift 6211354
  have htrace : WordTrace (prefixWord ++ tailWord_6211354) baseStart_6211354 baseEnd_6211354 := by
    simpa [prefixWord, tailWord_6211354, baseEnd_6211354] using wordTrace_append hprefix tailTrace_6211354
  have hstable : (prefixWord ++ tailWord_6211354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211354).length < 2 ^ (prefixWord ++ tailWord_6211354).sum := by decide
  have hdescent : baseEnd_6211354 < baseStart_6211354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211364 : List Nat := [2, 3, 1, 3, 2, 1, 1, 2, 1, 5, 2]
def baseStart_6211364 : Nat := 118140960795 + 6211364 * 2 ^ 59
def prefixEnd_6211364 : Nat := 4983230072969 + 3 ^ 40 * 6211364 * 2
def baseEnd_6211364 : Nat := 3189415252033541243484463

theorem tailTrace_6211364 : CollatzResearch.WordTrace tailWord_6211364 prefixEnd_6211364 3189415252033541243484463 := by
  unfold tailWord_6211364
  simp only [CollatzResearch.WordTrace]
  refine ⟨113273528334648259680196573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151031371112864346240262097 113273528334648259680196573)
  ·
    refine ⟨42477573125493097380073715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113273528334648259680196573 42477573125493097380073715)
    ·
      refine ⟨63716359688239646070110573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42477573125493097380073715 63716359688239646070110573)
      ·
        refine ⟨23893634883089867276291465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63716359688239646070110573 23893634883089867276291465)
        ·
          refine ⟨17920226162317400457218599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23893634883089867276291465 17920226162317400457218599)
          ·
            refine ⟨26880339243476100685827899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17920226162317400457218599 26880339243476100685827899)
            ·
              refine ⟨40320508865214151028741849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26880339243476100685827899 40320508865214151028741849)
              ·
                refine ⟨30240381648910613271556387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40320508865214151028741849 30240381648910613271556387)
                ·
                  refine ⟨45360572473365919907334581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30240381648910613271556387 45360572473365919907334581)
                  ·
                    refine ⟨4252553669378054991312617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45360572473365919907334581 4252553669378054991312617)
                    ·
                      refine ⟨3189415252033541243484463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4252553669378054991312617 3189415252033541243484463)
                      ·
                        rfl

theorem cell23_6211364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_6211364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211364 prefixEnd_6211364 := by exact prefixLift 6211364
  have htrace : WordTrace (prefixWord ++ tailWord_6211364) baseStart_6211364 baseEnd_6211364 := by
    simpa [prefixWord, tailWord_6211364, baseEnd_6211364] using wordTrace_append hprefix tailTrace_6211364
  have hstable : (prefixWord ++ tailWord_6211364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211364).length < 2 ^ (prefixWord ++ tailWord_6211364).sum := by decide
  have hdescent : baseEnd_6211364 < baseStart_6211364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211397 : List Nat := [1, 3, 1, 1, 1, 2, 6, 1, 1, 1, 5]
def baseStart_6211397 : Nat := 118140960795 + 6211397 * 2 ^ 59
def prefixEnd_6211397 : Nat := 4983230072969 + 3 ^ 40 * 6211397 * 2
def baseEnd_6211397 : Nat := 3189432196895139614371811

theorem tailTrace_6211397 : CollatzResearch.WordTrace tailWord_6211397 prefixEnd_6211397 3189432196895139614371811 := by
  unfold tailWord_6211397
  simp only [CollatzResearch.WordTrace]
  refine ⟨226548260278176965996344445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151032173518784643997562963 226548260278176965996344445)
  ·
    refine ⟨84955597604316362248629167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226548260278176965996344445 84955597604316362248629167)
    ·
      refine ⟨127433396406474543372943751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84955597604316362248629167 127433396406474543372943751)
      ·
        refine ⟨191150094609711815059415627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127433396406474543372943751 191150094609711815059415627)
        ·
          refine ⟨286725141914567722589123441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191150094609711815059415627 286725141914567722589123441)
          ·
            refine ⟨215043856435925791941842581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286725141914567722589123441 215043856435925791941842581)
            ·
              refine ⟨10080180770434021497273871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 215043856435925791941842581 10080180770434021497273871)
              ·
                refine ⟨15120271155651032245910807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10080180770434021497273871 15120271155651032245910807)
                ·
                  refine ⟨22680406733476548368866211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15120271155651032245910807 22680406733476548368866211)
                  ·
                    refine ⟨34020610100214822553299317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22680406733476548368866211 34020610100214822553299317)
                    ·
                      refine ⟨3189432196895139614371811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34020610100214822553299317 3189432196895139614371811)
                      ·
                        rfl

theorem cell23_6211397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 1, 5].length) (baseStart_6211397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211397 prefixEnd_6211397 := by exact prefixLift 6211397
  have htrace : WordTrace (prefixWord ++ tailWord_6211397) baseStart_6211397 baseEnd_6211397 := by
    simpa [prefixWord, tailWord_6211397, baseEnd_6211397] using wordTrace_append hprefix tailTrace_6211397
  have hstable : (prefixWord ++ tailWord_6211397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211397).length < 2 ^ (prefixWord ++ tailWord_6211397).sum := by decide
  have hdescent : baseEnd_6211397 < baseStart_6211397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211398 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2]
def baseStart_6211398 : Nat := 118140960795 + 6211398 * 2 ^ 59
def prefixEnd_6211398 : Nat := 4983230072969 + 3 ^ 40 * 6211398 * 2
def baseEnd_6211398 : Nat := 3189432710375794110459307

theorem tailTrace_6211398 : CollatzResearch.WordTrace tailWord_6211398 prefixEnd_6211398 3189432710375794110459307 := by
  unfold tailWord_6211398
  simp only [CollatzResearch.WordTrace]
  refine ⟨7079634273474166973972839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 151032197834115562111420565 7079634273474166973972839)
  ·
    refine ⟨10619451410211250460959259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7079634273474166973972839 10619451410211250460959259)
    ·
      refine ⟨15929177115316875691438889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10619451410211250460959259 15929177115316875691438889)
      ·
        refine ⟨11946882836487656768579167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15929177115316875691438889 11946882836487656768579167)
        ·
          refine ⟨17920324254731485152868751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11946882836487656768579167 17920324254731485152868751)
          ·
            refine ⟨26880486382097227729303127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17920324254731485152868751 26880486382097227729303127)
            ·
              refine ⟨40320729573145841593954691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26880486382097227729303127 40320729573145841593954691)
              ·
                refine ⟨60481094359718762390932037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40320729573145841593954691 60481094359718762390932037)
                ·
                  refine ⟨11340205192447267948299757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60481094359718762390932037 11340205192447267948299757)
                  ·
                    refine ⟨4252576947167725480612409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11340205192447267948299757 4252576947167725480612409)
                    ·
                      refine ⟨3189432710375794110459307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4252576947167725480612409 3189432710375794110459307)
                      ·
                        rfl

theorem cell23_6211398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_6211398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211398 prefixEnd_6211398 := by exact prefixLift 6211398
  have htrace : WordTrace (prefixWord ++ tailWord_6211398) baseStart_6211398 baseEnd_6211398 := by
    simpa [prefixWord, tailWord_6211398, baseEnd_6211398] using wordTrace_append hprefix tailTrace_6211398
  have hstable : (prefixWord ++ tailWord_6211398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211398).length < 2 ^ (prefixWord ++ tailWord_6211398).sum := by decide
  have hdescent : baseEnd_6211398 < baseStart_6211398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211400 : List Nat := [2, 1, 3, 1, 1, 4, 11]
def baseStart_6211400 : Nat := 118140960795 + 6211400 * 2 ^ 59
def prefixEnd_6211400 : Nat := 4983230072969 + 3 ^ 40 * 6211400 * 2
def baseEnd_6211400 : Nat := 39375725152309914847337

theorem tailTrace_6211400 : CollatzResearch.WordTrace tailWord_6211400 prefixEnd_6211400 39375725152309914847337 := by
  unfold tailWord_6211400
  simp only [CollatzResearch.WordTrace]
  refine ⟨113274184848583048754351827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151032246464777398339135769 113274184848583048754351827)
  ·
    refine ⟨169911277272874573131527741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113274184848583048754351827 169911277272874573131527741)
    ·
      refine ⟨63716728977327964924322903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169911277272874573131527741 63716728977327964924322903)
      ·
        refine ⟨95575093465991947386484355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63716728977327964924322903 95575093465991947386484355)
        ·
          refine ⟨143362640198987921079726533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95575093465991947386484355 143362640198987921079726533)
          ·
            refine ⟨26880495037310235202448725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143362640198987921079726533 26880495037310235202448725)
            ·
              refine ⟨39375725152309914847337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26880495037310235202448725 39375725152309914847337)
              ·
                rfl

theorem cell23_6211400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 11].length) (baseStart_6211400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211400 prefixEnd_6211400 := by exact prefixLift 6211400
  have htrace : WordTrace (prefixWord ++ tailWord_6211400) baseStart_6211400 baseEnd_6211400 := by
    simpa [prefixWord, tailWord_6211400, baseEnd_6211400] using wordTrace_append hprefix tailTrace_6211400
  have hstable : (prefixWord ++ tailWord_6211400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211400).length < 2 ^ (prefixWord ++ tailWord_6211400).sum := by decide
  have hdescent : baseEnd_6211400 < baseStart_6211400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211428 : List Nat := [2, 3, 1, 1, 6, 1, 1, 2, 1, 1, 4]
def baseStart_6211428 : Nat := 118140960795 + 6211428 * 2 ^ 59
def prefixEnd_6211428 : Nat := 4983230072969 + 3 ^ 40 * 6211428 * 2
def baseEnd_6211428 : Nat := 3189448114795428993084169

theorem tailTrace_6211428 : CollatzResearch.WordTrace tailWord_6211428 prefixEnd_6211428 3189448114795428993084169 := by
  unfold tailWord_6211428
  simp only [CollatzResearch.WordTrace]
  refine ⟨113274695470532329145361469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151032927294043105527148625 113274695470532329145361469)
  ·
    refine ⟨42478010801449623429510551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113274695470532329145361469 42478010801449623429510551)
    ·
      refine ⟨63717016202174435144265827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42478010801449623429510551 63717016202174435144265827)
      ·
        refine ⟨95575524303261652716398741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63717016202174435144265827 95575524303261652716398741)
        ·
          refine ⟨4480102701715389971081191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 95575524303261652716398741 4480102701715389971081191)
          ·
            refine ⟨6720154052573084956621787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4480102701715389971081191 6720154052573084956621787)
            ·
              refine ⟨10080231078859627434932681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6720154052573084956621787 10080231078859627434932681)
              ·
                refine ⟨7560173309144720576199511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10080231078859627434932681 7560173309144720576199511)
                ·
                  refine ⟨11340259963717080864299267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7560173309144720576199511 11340259963717080864299267)
                  ·
                    refine ⟨17010389945575621296448901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11340259963717080864299267 17010389945575621296448901)
                    ·
                      refine ⟨3189448114795428993084169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17010389945575621296448901 3189448114795428993084169)
                      ·
                        rfl

theorem cell23_6211428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 1, 1, 4].length) (baseStart_6211428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211428 prefixEnd_6211428 := by exact prefixLift 6211428
  have htrace : WordTrace (prefixWord ++ tailWord_6211428) baseStart_6211428 baseEnd_6211428 := by
    simpa [prefixWord, tailWord_6211428, baseEnd_6211428] using wordTrace_append hprefix tailTrace_6211428
  have hstable : (prefixWord ++ tailWord_6211428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211428).length < 2 ^ (prefixWord ++ tailWord_6211428).sum := by decide
  have hdescent : baseEnd_6211428 < baseStart_6211428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211461 : List Nat := [1, 3, 1, 1, 3, 2, 4, 2, 2, 1, 3]
def baseStart_6211461 : Nat := 118140960795 + 6211461 * 2 ^ 59
def prefixEnd_6211461 : Nat := 4983230072969 + 3 ^ 40 * 6211461 * 2
def baseEnd_6211461 : Nat := 3189465059657027363971517

theorem tailTrace_6211461 : CollatzResearch.WordTrace tailWord_6211461 prefixEnd_6211461 3189465059657027363971517 := by
  unfold tailWord_6211461
  simp only [CollatzResearch.WordTrace]
  refine ⟨226550594549945104926674237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151033729699963403284449491 226550594549945104926674237)
  ·
    refine ⟨84956472956229414347502839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226550594549945104926674237 84956472956229414347502839)
    ·
      refine ⟨127434709434344121521254259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84956472956229414347502839 127434709434344121521254259)
      ·
        refine ⟨191152064151516182281881389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127434709434344121521254259 191152064151516182281881389)
        ·
          refine ⟨71682024056818568355705521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191152064151516182281881389 71682024056818568355705521)
          ·
            refine ⟨53761518042613926266779141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71682024056818568355705521 53761518042613926266779141)
            ·
              refine ⟨10080284632990111175021089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53761518042613926266779141 10080284632990111175021089)
              ·
                refine ⟨7560213474742583381265817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10080284632990111175021089 7560213474742583381265817)
                ·
                  refine ⟨5670160106056937535949363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7560213474742583381265817 5670160106056937535949363)
                  ·
                    refine ⟨8505240159085406303924045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5670160106056937535949363 8505240159085406303924045)
                    ·
                      refine ⟨3189465059657027363971517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8505240159085406303924045 3189465059657027363971517)
                      ·
                        rfl

theorem cell23_6211461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2, 1, 3].length) (baseStart_6211461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211461 prefixEnd_6211461 := by exact prefixLift 6211461
  have htrace : WordTrace (prefixWord ++ tailWord_6211461) baseStart_6211461 baseEnd_6211461 := by
    simpa [prefixWord, tailWord_6211461, baseEnd_6211461] using wordTrace_append hprefix tailTrace_6211461
  have hstable : (prefixWord ++ tailWord_6211461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211461).length < 2 ^ (prefixWord ++ tailWord_6211461).sum := by decide
  have hdescent : baseEnd_6211461 < baseStart_6211461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211477 : List Nat := [1, 3, 2, 1, 1, 3, 3, 1, 2, 6]
def baseStart_6211477 : Nat := 118140960795 + 6211477 * 2 ^ 59
def prefixEnd_6211477 : Nat := 4983230072969 + 3 ^ 40 * 6211477 * 2
def baseEnd_6211477 : Nat := 1063157758449166433790481

theorem tailTrace_6211477 : CollatzResearch.WordTrace tailWord_6211477 prefixEnd_6211477 1063157758449166433790481 := by
  unfold tailWord_6211477
  simp only [CollatzResearch.WordTrace]
  refine ⟨226551178117887139659256685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151034118745258093106171123 226551178117887139659256685)
  ·
    refine ⟨84956691794207677372221257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226551178117887139659256685 84956691794207677372221257)
    ·
      refine ⟨63717518845655758029165943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84956691794207677372221257 63717518845655758029165943)
      ·
        refine ⟨95576278268483637043748915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63717518845655758029165943 95576278268483637043748915)
        ·
          refine ⟨143364417402725455565623373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95576278268483637043748915 143364417402725455565623373)
          ·
            refine ⟨53761656526022045837108765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143364417402725455565623373 53761656526022045837108765)
            ·
              refine ⟨20160621197258267188915787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53761656526022045837108765 20160621197258267188915787)
              ·
                refine ⟨30240931795887400783373681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20160621197258267188915787 30240931795887400783373681)
                ·
                  refine ⟨22680698846915550587530261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30240931795887400783373681 22680698846915550587530261)
                  ·
                    refine ⟨1063157758449166433790481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22680698846915550587530261 1063157758449166433790481)
                    ·
                      rfl

theorem cell23_6211477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_6211477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211477 prefixEnd_6211477 := by exact prefixLift 6211477
  have htrace : WordTrace (prefixWord ++ tailWord_6211477) baseStart_6211477 baseEnd_6211477 := by
    simpa [prefixWord, tailWord_6211477, baseEnd_6211477] using wordTrace_append hprefix tailTrace_6211477
  have hstable : (prefixWord ++ tailWord_6211477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211477).length < 2 ^ (prefixWord ++ tailWord_6211477).sum := by decide
  have hdescent : baseEnd_6211477 < baseStart_6211477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211505 : List Nat := [1, 2, 2, 4, 2, 3, 2, 1, 1, 3, 2]
def baseStart_6211505 : Nat := 118140960795 + 6211505 * 2 ^ 59
def prefixEnd_6211505 : Nat := 4983230072969 + 3 ^ 40 * 6211505 * 2
def baseEnd_6211505 : Nat := 3189487652805825191821315

theorem tailTrace_6211505 : CollatzResearch.WordTrace tailWord_6211505 prefixEnd_6211505 3189487652805825191821315 := by
  unfold tailWord_6211505
  simp only [CollatzResearch.WordTrace]
  refine ⟨226552199361785700441275969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151034799574523800294183979 226552199361785700441275969)
  ·
    refine ⟨169914149521339275330956977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226552199361785700441275969 169914149521339275330956977)
    ·
      refine ⟨127435612141004456498217733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169914149521339275330956977 127435612141004456498217733)
      ·
        refine ⟨23894177276438335593415825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127435612141004456498217733 23894177276438335593415825)
        ·
          refine ⟨17920632957328751695061869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23894177276438335593415825 17920632957328751695061869)
          ·
            refine ⟨6720237358998281885648201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17920632957328751695061869 6720237358998281885648201)
            ·
              refine ⟨5040178019248711414236151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6720237358998281885648201 5040178019248711414236151)
              ·
                refine ⟨7560267028873067121354227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5040178019248711414236151 7560267028873067121354227)
                ·
                  refine ⟨11340400543309600682031341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7560267028873067121354227 11340400543309600682031341)
                  ·
                    refine ⟨4252650203741100255761753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11340400543309600682031341 4252650203741100255761753)
                    ·
                      refine ⟨3189487652805825191821315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4252650203741100255761753 3189487652805825191821315)
                      ·
                        rfl

theorem cell23_6211505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_6211505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211505 prefixEnd_6211505 := by exact prefixLift 6211505
  have htrace : WordTrace (prefixWord ++ tailWord_6211505) baseStart_6211505 baseEnd_6211505 := by
    simpa [prefixWord, tailWord_6211505, baseEnd_6211505] using wordTrace_append hprefix tailTrace_6211505
  have hstable : (prefixWord ++ tailWord_6211505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211505).length < 2 ^ (prefixWord ++ tailWord_6211505).sum := by decide
  have hdescent : baseEnd_6211505 < baseStart_6211505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211518 : List Nat := [4, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2]
def baseStart_6211518 : Nat := 118140960795 + 6211518 * 2 ^ 59
def prefixEnd_6211518 : Nat := 4983230072969 + 3 ^ 40 * 6211518 * 2
def baseEnd_6211518 : Nat := 3189494328054333640958755

theorem tailTrace_6211518 : CollatzResearch.WordTrace tailWord_6211518 prefixEnd_6211518 3189494328054333640958755 := by
  unfold tailWord_6211518
  simp only [CollatzResearch.WordTrace]
  refine ⟨28319084188842325457687401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151035115673825735774332805 28319084188842325457687401)
  ·
    refine ⟨21239313141631744093265551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28319084188842325457687401 21239313141631744093265551)
    ·
      refine ⟨31858969712447616139898327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21239313141631744093265551 31858969712447616139898327)
      ·
        refine ⟨47788454568671424209847491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31858969712447616139898327 47788454568671424209847491)
        ·
          refine ⟨71682681853007136314771237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47788454568671424209847491 71682681853007136314771237)
          ·
            refine ⟨13440502847438838059019607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71682681853007136314771237 13440502847438838059019607)
            ·
              refine ⟨20160754271158257088529411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13440502847438838059019607 20160754271158257088529411)
              ·
                refine ⟨30241131406737385632794117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20160754271158257088529411 30241131406737385632794117)
                ·
                  refine ⟨5670212138763259806148897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30241131406737385632794117 5670212138763259806148897)
                  ·
                    refine ⟨4252659104072444854611673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5670212138763259806148897 4252659104072444854611673)
                    ·
                      refine ⟨3189494328054333640958755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4252659104072444854611673 3189494328054333640958755)
                      ·
                        rfl

theorem cell23_6211518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_6211518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211518 prefixEnd_6211518 := by exact prefixLift 6211518
  have htrace : WordTrace (prefixWord ++ tailWord_6211518) baseStart_6211518 baseEnd_6211518 := by
    simpa [prefixWord, tailWord_6211518, baseEnd_6211518] using wordTrace_append hprefix tailTrace_6211518
  have hstable : (prefixWord ++ tailWord_6211518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211518).length < 2 ^ (prefixWord ++ tailWord_6211518).sum := by decide
  have hdescent : baseEnd_6211518 < baseStart_6211518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211534 : List Nat := [4, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3]
def baseStart_6211534 : Nat := 118140960795 + 6211534 * 2 ^ 59
def prefixEnd_6211534 : Nat := 4983230072969 + 3 ^ 40 * 6211534 * 2
def baseEnd_6211534 : Nat := 3189502543744805578358681

theorem tailTrace_6211534 : CollatzResearch.WordTrace tailWord_6211534 prefixEnd_6211534 3189502543744805578358681 := by
  unfold tailWord_6211534
  simp only [CollatzResearch.WordTrace]
  refine ⟨28319157134835079799260207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151035504719120425596054437 28319157134835079799260207)
  ·
    refine ⟨42478735702252619698890311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28319157134835079799260207 42478735702252619698890311)
    ·
      refine ⟨63718103553378929548335467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42478735702252619698890311 63718103553378929548335467)
      ·
        refine ⟨95577155330068394322503201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63718103553378929548335467 95577155330068394322503201)
        ·
          refine ⟨71682866497551295741877401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95577155330068394322503201 71682866497551295741877401)
          ·
            refine ⟨53762149873163471806408051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71682866497551295741877401 53762149873163471806408051)
            ·
              refine ⟨80643224809745207709612077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53762149873163471806408051 80643224809745207709612077)
              ·
                refine ⟨30241209303654452891104529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80643224809745207709612077 30241209303654452891104529)
                ·
                  refine ⟨22680906977740839668328397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30241209303654452891104529 22680906977740839668328397)
                  ·
                    refine ⟨8505340116652814875623149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22680906977740839668328397 8505340116652814875623149)
                    ·
                      refine ⟨3189502543744805578358681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8505340116652814875623149 3189502543744805578358681)
                      ·
                        rfl

theorem cell23_6211534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_6211534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211534 prefixEnd_6211534 := by exact prefixLift 6211534
  have htrace : WordTrace (prefixWord ++ tailWord_6211534) baseStart_6211534 baseEnd_6211534 := by
    simpa [prefixWord, tailWord_6211534, baseEnd_6211534] using wordTrace_append hprefix tailTrace_6211534
  have hstable : (prefixWord ++ tailWord_6211534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211534).length < 2 ^ (prefixWord ++ tailWord_6211534).sum := by decide
  have hdescent : baseEnd_6211534 < baseStart_6211534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211537 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 6, 5]
def baseStart_6211537 : Nat := 118140960795 + 6211537 * 2 ^ 59
def prefixEnd_6211537 : Nat := 4983230072969 + 3 ^ 40 * 6211537 * 2
def baseEnd_6211537 : Nat := 1063168028062256355540389

theorem tailTrace_6211537 : CollatzResearch.WordTrace tailWord_6211537 prefixEnd_6211537 1063168028062256355540389 := by
  unfold tailWord_6211537
  simp only [CollatzResearch.WordTrace]
  refine ⟨226553366497669769906440865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151035577665113179937627243 226553366497669769906440865)
  ·
    refine ⟨169915024873252327429830649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226553366497669769906440865 169915024873252327429830649)
    ·
      refine ⟨127436268654939245572372987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169915024873252327429830649 127436268654939245572372987)
      ·
        refine ⟨191154402982408868358559481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127436268654939245572372987 191154402982408868358559481)
        ·
          refine ⟨143365802236806651268919611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191154402982408868358559481 143365802236806651268919611)
          ·
            refine ⟨215048703355209976903379417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143365802236806651268919611 215048703355209976903379417)
            ·
              refine ⟨161286527516407482677534563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215048703355209976903379417 161286527516407482677534563)
              ·
                refine ⟨241929791274611224016301845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161286527516407482677534563 241929791274611224016301845)
                ·
                  refine ⟨11340458965997401125764149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 241929791274611224016301845 11340458965997401125764149)
                  ·
                    refine ⟨1063168028062256355540389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11340458965997401125764149 1063168028062256355540389)
                    ·
                      rfl

theorem cell23_6211537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 5].length) (baseStart_6211537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211537 prefixEnd_6211537 := by exact prefixLift 6211537
  have htrace : WordTrace (prefixWord ++ tailWord_6211537) baseStart_6211537 baseEnd_6211537 := by
    simpa [prefixWord, tailWord_6211537, baseEnd_6211537] using wordTrace_append hprefix tailTrace_6211537
  have hstable : (prefixWord ++ tailWord_6211537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211537).length < 2 ^ (prefixWord ++ tailWord_6211537).sum := by decide
  have hdescent : baseEnd_6211537 < baseStart_6211537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211584 : List Nat := [2, 1, 1, 2, 1, 1, 1, 7, 3, 4]
def baseStart_6211584 : Nat := 118140960795 + 6211584 * 2 ^ 59
def prefixEnd_6211584 : Nat := 4983230072969 + 3 ^ 40 * 6211584 * 2
def baseEnd_6211584 : Nat := 1063176072592510127577817

theorem tailTrace_6211584 : CollatzResearch.WordTrace tailWord_6211584 prefixEnd_6211584 1063176072592510127577817 := by
  unfold tailWord_6211584
  simp only [CollatzResearch.WordTrace]
  refine ⟨113277540364249748466700903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151036720485666331288934537 113277540364249748466700903)
  ·
    refine ⟨169916310546374622700051355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113277540364249748466700903 169916310546374622700051355)
    ·
      refine ⟨254874465819561934050077033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169916310546374622700051355 254874465819561934050077033)
      ·
        refine ⟨191155849364671450537557775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254874465819561934050077033 191155849364671450537557775)
        ·
          refine ⟨286733774047007175806336663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191155849364671450537557775 286733774047007175806336663)
          ·
            refine ⟨430100661070510763709504995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286733774047007175806336663 430100661070510763709504995)
            ·
              refine ⟨645150991605766145564257493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430100661070510763709504995 645150991605766145564257493)
              ·
                refine ⟨15120726365760144036662285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 645150991605766145564257493 15120726365760144036662285)
                ·
                  refine ⟨5670272387160054013748357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15120726365760144036662285 5670272387160054013748357)
                  ·
                    refine ⟨1063176072592510127577817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5670272387160054013748357 1063176072592510127577817)
                    ·
                      rfl

theorem cell23_6211584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 3, 4].length) (baseStart_6211584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211584 prefixEnd_6211584 := by exact prefixLift 6211584
  have htrace : WordTrace (prefixWord ++ tailWord_6211584) baseStart_6211584 baseEnd_6211584 := by
    simpa [prefixWord, tailWord_6211584, baseEnd_6211584] using wordTrace_append hprefix tailTrace_6211584
  have hstable : (prefixWord ++ tailWord_6211584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211584).length < 2 ^ (prefixWord ++ tailWord_6211584).sum := by decide
  have hdescent : baseEnd_6211584 < baseStart_6211584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211587 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 6]
def baseStart_6211587 : Nat := 118140960795 + 6211587 * 2 ^ 59
def prefixEnd_6211587 : Nat := 4983230072969 + 3 ^ 40 * 6211587 * 2
def baseEnd_6211587 : Nat := 3189529758219493870995937

theorem tailTrace_6211587 : CollatzResearch.WordTrace tailWord_6211587 prefixEnd_6211587 3189529758219493870995937 := by
  unfold tailWord_6211587
  simp only [CollatzResearch.WordTrace]
  refine ⟨226555190147488628445761015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151036793431659085630507343 226555190147488628445761015)
  ·
    refine ⟨339832785221232942668641523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226555190147488628445761015 339832785221232942668641523)
    ·
      refine ⟨509749177831849414002962285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339832785221232942668641523 509749177831849414002962285)
      ·
        refine ⟨191155941686943530251110857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 509749177831849414002962285 191155941686943530251110857)
        ·
          refine ⟨143366956265207647688333143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191155941686943530251110857 143366956265207647688333143)
          ·
            refine ⟨215050434397811471532499715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143366956265207647688333143 215050434397811471532499715)
            ·
              refine ⟨322575651596717207298749573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215050434397811471532499715 322575651596717207298749573)
              ·
                refine ⟨60482934674384476368515545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 322575651596717207298749573 60482934674384476368515545)
                ·
                  refine ⟨45362201005788357276386659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60482934674384476368515545 45362201005788357276386659)
                  ·
                    refine ⟨68043301508682535914579989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45362201005788357276386659 68043301508682535914579989)
                    ·
                      refine ⟨3189529758219493870995937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68043301508682535914579989 3189529758219493870995937)
                      ·
                        rfl

theorem cell23_6211587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_6211587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211587 prefixEnd_6211587 := by exact prefixLift 6211587
  have htrace : WordTrace (prefixWord ++ tailWord_6211587) baseStart_6211587 baseEnd_6211587 := by
    simpa [prefixWord, tailWord_6211587, baseEnd_6211587] using wordTrace_append hprefix tailTrace_6211587
  have hstable : (prefixWord ++ tailWord_6211587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211587).length < 2 ^ (prefixWord ++ tailWord_6211587).sum := by decide
  have hdescent : baseEnd_6211587 < baseStart_6211587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211618 : List Nat := [3, 3, 1, 1, 1, 2, 2, 5, 1, 4]
def baseStart_6211618 : Nat := 118140960795 + 6211618 * 2 ^ 59
def prefixEnd_6211618 : Nat := 4983230072969 + 3 ^ 40 * 6211618 * 2
def baseEnd_6211618 : Nat := 1063181892039927749902765

theorem tailTrace_6211618 : CollatzResearch.WordTrace tailWord_6211618 prefixEnd_6211618 1063181892039927749902765 := by
  unfold tailWord_6211618
  simp only [CollatzResearch.WordTrace]
  refine ⟨56639080202594080185034877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151037547206917547160093005 56639080202594080185034877)
  ·
    refine ⟨21239655075972780069388079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56639080202594080185034877 21239655075972780069388079)
    ·
      refine ⟨31859482613959170104082119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21239655075972780069388079 31859482613959170104082119)
      ·
        refine ⟨47789223920938755156123179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31859482613959170104082119 47789223920938755156123179)
        ·
          refine ⟨71683835881408132734184769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47789223920938755156123179 71683835881408132734184769)
          ·
            refine ⟨53762876911056099550638577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71683835881408132734184769 53762876911056099550638577)
            ·
              refine ⟨40322157683292074662978933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53762876911056099550638577 40322157683292074662978933)
              ·
                refine ⟨3780202282808631999654275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40322157683292074662978933 3780202282808631999654275)
                ·
                  refine ⟨5670303424212947999481413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3780202282808631999654275 5670303424212947999481413)
                  ·
                    refine ⟨1063181892039927749902765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5670303424212947999481413 1063181892039927749902765)
                    ·
                      rfl

theorem cell23_6211618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_6211618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211618 prefixEnd_6211618 := by exact prefixLift 6211618
  have htrace : WordTrace (prefixWord ++ tailWord_6211618) baseStart_6211618 baseEnd_6211618 := by
    simpa [prefixWord, tailWord_6211618, baseEnd_6211618] using wordTrace_append hprefix tailTrace_6211618
  have hstable : (prefixWord ++ tailWord_6211618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211618).length < 2 ^ (prefixWord ++ tailWord_6211618).sum := by decide
  have hdescent : baseEnd_6211618 < baseStart_6211618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211644 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 5, 5]
def baseStart_6211644 : Nat := 118140960795 + 6211644 * 2 ^ 59
def prefixEnd_6211644 : Nat := 4983230072969 + 3 ^ 40 * 6211644 * 2
def baseEnd_6211644 : Nat := 1063186342205600049327725

theorem tailTrace_6211644 : CollatzResearch.WordTrace tailWord_6211644 prefixEnd_6211644 1063186342205600049327725 := by
  unfold tailWord_6211644
  simp only [CollatzResearch.WordTrace]
  refine ⟨113278634554141063590292993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151038179405521418120390657 113278634554141063590292993)
  ·
    refine ⟨84958975915605797692719745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113278634554141063590292993 84958975915605797692719745)
    ·
      refine ⟨63719231936704348269539809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84958975915605797692719745 63719231936704348269539809)
      ·
        refine ⟨47789423952528261202154857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63719231936704348269539809 47789423952528261202154857)
        ·
          refine ⟨35842067964396195901616143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47789423952528261202154857 35842067964396195901616143)
          ·
            refine ⟨53763101946594293852424215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35842067964396195901616143 53763101946594293852424215)
            ·
              refine ⟨80644652919891440778636323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53763101946594293852424215 80644652919891440778636323)
              ·
                refine ⟨120966979379837161167954485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80644652919891440778636323 120966979379837161167954485)
                ·
                  refine ⟨11340654316859733859495733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120966979379837161167954485 11340654316859733859495733)
                  ·
                    refine ⟨1063186342205600049327725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11340654316859733859495733 1063186342205600049327725)
                    ·
                      rfl

theorem cell23_6211644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_6211644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211644 prefixEnd_6211644 := by exact prefixLift 6211644
  have htrace : WordTrace (prefixWord ++ tailWord_6211644) baseStart_6211644 baseEnd_6211644 := by
    simpa [prefixWord, tailWord_6211644, baseEnd_6211644] using wordTrace_append hprefix tailTrace_6211644
  have hstable : (prefixWord ++ tailWord_6211644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211644).length < 2 ^ (prefixWord ++ tailWord_6211644).sum := by decide
  have hdescent : baseEnd_6211644 < baseStart_6211644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211661 : List Nat := [1, 6, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_6211661 : Nat := 118140960795 + 6211661 * 2 ^ 59
def prefixEnd_6211661 : Nat := 4983230072969 + 3 ^ 40 * 6211661 * 2
def baseEnd_6211661 : Nat := 1063189251929308860490199

theorem tailTrace_6211661 : CollatzResearch.WordTrace tailWord_6211661 prefixEnd_6211661 1063189251929308860490199 := by
  unfold tailWord_6211661
  simp only [CollatzResearch.WordTrace]
  refine ⟨226557889149220539083954837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151038592766147026055969891 226557889149220539083954837)
  ·
    refine ⟨10619901053869712769560383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 226557889149220539083954837 10619901053869712769560383)
    ·
      refine ⟨15929851580804569154340575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10619901053869712769560383 15929851580804569154340575)
      ·
        refine ⟨23894777371206853731510863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15929851580804569154340575 23894777371206853731510863)
        ·
          refine ⟨35842166056810280597266295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23894777371206853731510863 35842166056810280597266295)
          ·
            refine ⟨53763249085215420895899443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35842166056810280597266295 53763249085215420895899443)
            ·
              refine ⟨80644873627823131343849165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53763249085215420895899443 80644873627823131343849165)
              ·
                refine ⟨30241827610433674253943437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80644873627823131343849165 30241827610433674253943437)
                ·
                  refine ⟨11340685353912627845228789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30241827610433674253943437 11340685353912627845228789)
                  ·
                    refine ⟨1063189251929308860490199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11340685353912627845228789 1063189251929308860490199)
                    ·
                      rfl

theorem cell23_6211661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_6211661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211661 prefixEnd_6211661 := by exact prefixLift 6211661
  have htrace : WordTrace (prefixWord ++ tailWord_6211661) baseStart_6211661 baseEnd_6211661 := by
    simpa [prefixWord, tailWord_6211661, baseEnd_6211661] using wordTrace_append hprefix tailTrace_6211661
  have hstable : (prefixWord ++ tailWord_6211661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211661).length < 2 ^ (prefixWord ++ tailWord_6211661).sum := by decide
  have hdescent : baseEnd_6211661 < baseStart_6211661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211674 : List Nat := [3, 1, 1, 2, 1, 1, 3, 4, 1, 6]
def baseStart_6211674 : Nat := 118140960795 + 6211674 * 2 ^ 59
def prefixEnd_6211674 : Nat := 4983230072969 + 3 ^ 40 * 6211674 * 2
def baseEnd_6211674 : Nat := 1063191477012145010202679

theorem tailTrace_6211674 : CollatzResearch.WordTrace tailWord_6211674 prefixEnd_6211674 1063191477012145010202679 := by
  unfold tailWord_6211674
  simp only [CollatzResearch.WordTrace]
  refine ⟨56639590824543360576044519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151038908865448961536118717 56639590824543360576044519)
  ·
    refine ⟨84959386236815040864066779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56639590824543360576044519 84959386236815040864066779)
    ·
      refine ⟨127439079355222561296100169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84959386236815040864066779 127439079355222561296100169)
      ·
        refine ⟨95579309516416920972075127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127439079355222561296100169 95579309516416920972075127)
        ·
          refine ⟨143368964274625381458112691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95579309516416920972075127 143368964274625381458112691)
          ·
            refine ⟨215053446411938072187169037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143368964274625381458112691 215053446411938072187169037)
            ·
              refine ⟨80645042404476777070188389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215053446411938072187169037 80645042404476777070188389)
              ·
                refine ⟨15120945450839395700660323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80645042404476777070188389 15120945450839395700660323)
                ·
                  refine ⟨22681418176259093550990485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15120945450839395700660323 22681418176259093550990485)
                  ·
                    refine ⟨1063191477012145010202679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22681418176259093550990485 1063191477012145010202679)
                    ·
                      rfl

theorem cell23_6211674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 1, 6].length) (baseStart_6211674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211674 prefixEnd_6211674 := by exact prefixLift 6211674
  have htrace : WordTrace (prefixWord ++ tailWord_6211674) baseStart_6211674 baseEnd_6211674 := by
    simpa [prefixWord, tailWord_6211674, baseEnd_6211674] using wordTrace_append hprefix tailTrace_6211674
  have hstable : (prefixWord ++ tailWord_6211674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211674).length < 2 ^ (prefixWord ++ tailWord_6211674).sum := by decide
  have hdescent : baseEnd_6211674 < baseStart_6211674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211738 : List Nat := [3, 1, 1, 5, 3, 1, 9]
def baseStart_6211738 : Nat := 118140960795 + 6211738 * 2 ^ 59
def prefixEnd_6211738 : Nat := 4983230072969 + 3 ^ 40 * 6211738 * 2
def baseEnd_6211738 : Nat := 39377867824670651607503

theorem tailTrace_6211738 : CollatzResearch.WordTrace tailWord_6211738 prefixEnd_6211738 39377867824670651607503 := by
  unfold tailWord_6211738
  simp only [CollatzResearch.WordTrace]
  refine ⟨56640174392485395308626967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151040465046627720823005245 56640174392485395308626967)
  ·
    refine ⟨84960261588728092962940451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56640174392485395308626967 84960261588728092962940451)
    ·
      refine ⟨127440392383092139444410677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84960261588728092962940451 127440392383092139444410677)
      ·
        refine ⟨11947536785914888072913501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127440392383092139444410677 11947536785914888072913501)
        ·
          refine ⟨4480326294718083027342563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11947536785914888072913501 4480326294718083027342563)
          ·
            refine ⟨6720489442077124541013845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4480326294718083027342563 6720489442077124541013845)
            ·
              refine ⟨39377867824670651607503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6720489442077124541013845 39377867824670651607503)
              ·
                rfl

theorem cell23_6211738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 9].length) (baseStart_6211738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211738 prefixEnd_6211738 := by exact prefixLift 6211738
  have htrace : WordTrace (prefixWord ++ tailWord_6211738) baseStart_6211738 baseEnd_6211738 := by
    simpa [prefixWord, tailWord_6211738, baseEnd_6211738] using wordTrace_append hprefix tailTrace_6211738
  have hstable : (prefixWord ++ tailWord_6211738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211738).length < 2 ^ (prefixWord ++ tailWord_6211738).sum := by decide
  have hdescent : baseEnd_6211738 < baseStart_6211738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211838 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_6211838 : Nat := 118140960795 + 6211838 * 2 ^ 59
def prefixEnd_6211838 : Nat := 4983230072969 + 3 ^ 40 * 6211838 * 2
def baseEnd_6211838 : Nat := 3189658641863772388957283

theorem tailTrace_6211838 : CollatzResearch.WordTrace tailWord_6211838 prefixEnd_6211838 3189658641863772388957283 := by
  unfold tailWord_6211838
  simp only [CollatzResearch.WordTrace]
  refine ⟨28320543108697412289143521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151042896579719532208765445 28320543108697412289143521)
  ·
    refine ⟨21240407331523059216857641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28320543108697412289143521 21240407331523059216857641)
    ·
      refine ⟨15930305498642294412643231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21240407331523059216857641 15930305498642294412643231)
      ·
        refine ⟨23895458247963441618964847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15930305498642294412643231 23895458247963441618964847)
        ·
          refine ⟨35843187371945162428447271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23895458247963441618964847 35843187371945162428447271)
          ·
            refine ⟨53764781057917743642670907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35843187371945162428447271 53764781057917743642670907)
            ·
              refine ⟨80647171586876615464006361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53764781057917743642670907 80647171586876615464006361)
              ·
                refine ⟨60485378690157461598004771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80647171586876615464006361 60485378690157461598004771)
                ·
                  refine ⟨90728068035236192397007157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60485378690157461598004771 90728068035236192397007157)
                  ·
                    refine ⟨8505756378303393037219421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90728068035236192397007157 8505756378303393037219421)
                    ·
                      refine ⟨3189658641863772388957283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8505756378303393037219421 3189658641863772388957283)
                      ·
                        rfl

theorem cell23_6211838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_6211838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211838 prefixEnd_6211838 := by exact prefixLift 6211838
  have htrace : WordTrace (prefixWord ++ tailWord_6211838) baseStart_6211838 baseEnd_6211838 := by
    simpa [prefixWord, tailWord_6211838, baseEnd_6211838] using wordTrace_append hprefix tailTrace_6211838
  have hstable : (prefixWord ++ tailWord_6211838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211838).length < 2 ^ (prefixWord ++ tailWord_6211838).sum := by decide
  have hdescent : baseEnd_6211838 < baseStart_6211838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211841 : List Nat := [1, 2, 4, 1, 1, 2, 3, 1, 1, 7]
def baseStart_6211841 : Nat := 118140960795 + 6211841 * 2 ^ 59
def prefixEnd_6211841 : Nat := 4983230072969 + 3 ^ 40 * 6211841 * 2
def baseEnd_6211841 : Nat := 1063220060768578625739923

theorem tailTrace_6211841 : CollatzResearch.WordTrace tailWord_6211841 prefixEnd_6211841 1063220060768578625739923 := by
  unfold tailWord_6211841
  simp only [CollatzResearch.WordTrace]
  refine ⟨226564454288568429825507377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151042969525712286550338251 226564454288568429825507377)
  ·
    refine ⟨169923340716426322369130533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226564454288568429825507377 169923340716426322369130533)
    ·
      refine ⟨31860626384329935444211975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169923340716426322369130533 31860626384329935444211975)
      ·
        refine ⟨47790939576494903166317963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31860626384329935444211975 47790939576494903166317963)
        ·
          refine ⟨71686409364742354749476945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47790939576494903166317963 71686409364742354749476945)
          ·
            refine ⟨53764807023556766062107709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71686409364742354749476945 53764807023556766062107709)
            ·
              refine ⟨20161802633833787273290391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53764807023556766062107709 20161802633833787273290391)
              ·
                refine ⟨30242703950750680909935587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20161802633833787273290391 30242703950750680909935587)
                ·
                  refine ⟨45364055926126021364903381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30242703950750680909935587 45364055926126021364903381)
                  ·
                    refine ⟨1063220060768578625739923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45364055926126021364903381 1063220060768578625739923)
                    ·
                      rfl

theorem cell23_6211841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_6211841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211841 prefixEnd_6211841 := by exact prefixLift 6211841
  have htrace : WordTrace (prefixWord ++ tailWord_6211841) baseStart_6211841 baseEnd_6211841 := by
    simpa [prefixWord, tailWord_6211841, baseEnd_6211841] using wordTrace_append hprefix tailTrace_6211841
  have hstable : (prefixWord ++ tailWord_6211841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211841).length < 2 ^ (prefixWord ++ tailWord_6211841).sum := by decide
  have hdescent : baseEnd_6211841 < baseStart_6211841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211891 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 4]
def baseStart_6211891 : Nat := 118140960795 + 6211891 * 2 ^ 59
def prefixEnd_6211891 : Nat := 4983230072969 + 3 ^ 40 * 6211891 * 2
def baseEnd_6211891 : Nat := 3189685856338460681594539

theorem tailTrace_6211891 : CollatzResearch.WordTrace tailWord_6211891 prefixEnd_6211891 3189685856338460681594539 := by
  unfold tailWord_6211891
  simp only [CollatzResearch.WordTrace]
  refine ⟨226566277938387288364827527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151044185292258192243218351 226566277938387288364827527)
  ·
    refine ⟨339849416907580932547241291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226566277938387288364827527 339849416907580932547241291)
    ·
      refine ⟨509774125361371398820861937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339849416907580932547241291 509774125361371398820861937)
      ·
        refine ⟨382330594021028549115646453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 509774125361371398820861937 382330594021028549115646453)
        ·
          refine ⟨35843493189471426479591855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 382330594021028549115646453 35843493189471426479591855)
          ·
            refine ⟨53765239784207139719387783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35843493189471426479591855 53765239784207139719387783)
            ·
              refine ⟨80647859676310709579081675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53765239784207139719387783 80647859676310709579081675)
              ·
                refine ⟨120971789514466064368622513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80647859676310709579081675 120971789514466064368622513)
                ·
                  refine ⟨90728842135849548276466885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120971789514466064368622513 90728842135849548276466885)
                  ·
                    refine ⟨17011657900471790301837541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90728842135849548276466885 17011657900471790301837541)
                    ·
                      refine ⟨3189685856338460681594539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17011657900471790301837541 3189685856338460681594539)
                      ·
                        rfl

theorem cell23_6211891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 4].length) (baseStart_6211891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211891 prefixEnd_6211891 := by exact prefixLift 6211891
  have htrace : WordTrace (prefixWord ++ tailWord_6211891) baseStart_6211891 baseEnd_6211891 := by
    simpa [prefixWord, tailWord_6211891, baseEnd_6211891] using wordTrace_append hprefix tailTrace_6211891
  have hstable : (prefixWord ++ tailWord_6211891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211891).length < 2 ^ (prefixWord ++ tailWord_6211891).sum := by decide
  have hdescent : baseEnd_6211891 < baseStart_6211891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211898 : List Nat := [3, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3]
def baseStart_6211898 : Nat := 118140960795 + 6211898 * 2 ^ 59
def prefixEnd_6211898 : Nat := 4983230072969 + 3 ^ 40 * 6211898 * 2
def baseEnd_6211898 : Nat := 3189689450703042154207007

theorem tailTrace_6211898 : CollatzResearch.WordTrace tailWord_6211898 prefixEnd_6211898 3189689450703042154207007 := by
  unfold tailWord_6211898
  simp only [CollatzResearch.WordTrace]
  refine ⟨56641633312340482140083087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151044355499574619040221565 56641633312340482140083087)
  ·
    refine ⟨84962449968510723210124631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56641633312340482140083087 84962449968510723210124631)
    ·
      refine ⟨127443674952766084815186947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84962449968510723210124631 127443674952766084815186947)
      ·
        refine ⟨191165512429149127222780421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127443674952766084815186947 191165512429149127222780421)
        ·
          refine ⟨35843533580465461354271329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191165512429149127222780421 35843533580465461354271329)
          ·
            refine ⟨26882650185349096015703497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35843533580465461354271329 26882650185349096015703497)
            ·
              refine ⟨20161987639011822011777623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26882650185349096015703497 20161987639011822011777623)
              ·
                refine ⟨30242981458517733017666435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20161987639011822011777623 30242981458517733017666435)
                ·
                  refine ⟨45364472187776599526499653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30242981458517733017666435 45364472187776599526499653)
                  ·
                    refine ⟨8505838535208112411218685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45364472187776599526499653 8505838535208112411218685)
                    ·
                      refine ⟨3189689450703042154207007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8505838535208112411218685 3189689450703042154207007)
                      ·
                        rfl

theorem cell23_6211898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3].length) (baseStart_6211898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211898 prefixEnd_6211898 := by exact prefixLift 6211898
  have htrace : WordTrace (prefixWord ++ tailWord_6211898) baseStart_6211898 baseEnd_6211898 := by
    simpa [prefixWord, tailWord_6211898, baseEnd_6211898] using wordTrace_append hprefix tailTrace_6211898
  have hstable : (prefixWord ++ tailWord_6211898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211898).length < 2 ^ (prefixWord ++ tailWord_6211898).sum := by decide
  have hdescent : baseEnd_6211898 < baseStart_6211898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211979 : List Nat := [1, 1, 1, 1, 4, 4, 4, 2, 1, 1, 3]
def baseStart_6211979 : Nat := 118140960795 + 6211979 * 2 ^ 59
def prefixEnd_6211979 : Nat := 4983230072969 + 3 ^ 40 * 6211979 * 2
def baseEnd_6211979 : Nat := 3189731042636056337294135

theorem tailTrace_6211979 : CollatzResearch.WordTrace tailWord_6211979 prefixEnd_6211979 3189731042636056337294135 := by
  unfold tailWord_6211979
  simp only [CollatzResearch.WordTrace]
  refine ⟨226569487562068479394030991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151046325041378986262687327 226569487562068479394030991)
  ·
    refine ⟨339854231343102719091046487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226569487562068479394030991 339854231343102719091046487)
    ·
      refine ⟨509781347014654078636569731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339854231343102719091046487 509781347014654078636569731)
      ·
        refine ⟨764672020521981117954854597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509781347014654078636569731 764672020521981117954854597)
        ·
          refine ⟨143376003847871459616535237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 764672020521981117954854597 143376003847871459616535237)
          ·
            refine ⟨26883000721475898678100357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143376003847871459616535237 26883000721475898678100357)
            ·
              refine ⟨5040562635276731002143817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26883000721475898678100357 5040562635276731002143817)
              ·
                refine ⟨3780421976457548251607863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5040562635276731002143817 3780421976457548251607863)
                ·
                  refine ⟨5670632964686322377411795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3780421976457548251607863 5670632964686322377411795)
                  ·
                    refine ⟨8505949447029483566117693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5670632964686322377411795 8505949447029483566117693)
                    ·
                      refine ⟨3189731042636056337294135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8505949447029483566117693 3189731042636056337294135)
                      ·
                        rfl

theorem cell23_6211979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2, 1, 1, 3].length) (baseStart_6211979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211979 prefixEnd_6211979 := by exact prefixLift 6211979
  have htrace : WordTrace (prefixWord ++ tailWord_6211979) baseStart_6211979 baseEnd_6211979 := by
    simpa [prefixWord, tailWord_6211979, baseEnd_6211979] using wordTrace_append hprefix tailTrace_6211979
  have hstable : (prefixWord ++ tailWord_6211979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211979).length < 2 ^ (prefixWord ++ tailWord_6211979).sum := by decide
  have hdescent : baseEnd_6211979 < baseStart_6211979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212005 : List Nat := [1, 3, 1, 2, 1, 1, 4, 4, 1, 2, 3]
def baseStart_6212005 : Nat := 118140960795 + 6212005 * 2 ^ 59
def prefixEnd_6212005 : Nat := 4983230072969 + 3 ^ 40 * 6212005 * 2
def baseEnd_6212005 : Nat := 3189744393133073235569015

theorem tailTrace_6212005 : CollatzResearch.WordTrace tailWord_6212005 prefixEnd_6212005 3189744393133073235569015 := by
  unfold tailWord_6212005
  simp only [CollatzResearch.WordTrace]
  refine ⟨226570435859974285834477469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151046957239982857222984979 226570435859974285834477469)
  ·
    refine ⟨84963913447490357187929051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226570435859974285834477469 84963913447490357187929051)
    ·
      refine ⟨127445870171235535781893577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84963913447490357187929051 127445870171235535781893577)
      ·
        refine ⟨95584402628426651836420183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127445870171235535781893577 95584402628426651836420183)
        ·
          refine ⟨143376603942639977754630275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95584402628426651836420183 143376603942639977754630275)
          ·
            refine ⟨215064905913959966631945413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143376603942639977754630275 215064905913959966631945413)
            ·
              refine ⟨40324669858867493743489765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 215064905913959966631945413 40324669858867493743489765)
              ·
                refine ⟨7560875598537655076904331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40324669858867493743489765 7560875598537655076904331)
                ·
                  refine ⟨11341313397806482615356497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7560875598537655076904331 11341313397806482615356497)
                  ·
                    refine ⟨8505985048354861961517373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11341313397806482615356497 8505985048354861961517373)
                    ·
                      refine ⟨3189744393133073235569015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8505985048354861961517373 3189744393133073235569015)
                      ·
                        rfl

theorem cell23_6212005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_6212005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212005 prefixEnd_6212005 := by exact prefixLift 6212005
  have htrace : WordTrace (prefixWord ++ tailWord_6212005) baseStart_6212005 baseEnd_6212005 := by
    simpa [prefixWord, tailWord_6212005, baseEnd_6212005] using wordTrace_append hprefix tailTrace_6212005
  have hstable : (prefixWord ++ tailWord_6212005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212005).length < 2 ^ (prefixWord ++ tailWord_6212005).sum := by decide
  have hdescent : baseEnd_6212005 < baseStart_6212005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212036 : List Nat := [2, 3, 3, 2, 2, 1, 2, 1, 3, 2, 2]
def baseStart_6212036 : Nat := 118140960795 + 6212036 * 2 ^ 59
def prefixEnd_6212036 : Nat := 4983230072969 + 3 ^ 40 * 6212036 * 2
def baseEnd_6212036 : Nat := 3189760311033362614281373

theorem tailTrace_6212036 : CollatzResearch.WordTrace tailWord_6212036 prefixEnd_6212036 3189760311033362614281373 := by
  unfold tailWord_6212036
  simp only [CollatzResearch.WordTrace]
  refine ⟨113285783261430989064427981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151047711015241318752570641 113285783261430989064427981)
  ·
    refine ⟨42482168723036620899160493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113285783261430989064427981 42482168723036620899160493)
    ·
      refine ⟨15930813271138732837185185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42482168723036620899160493 15930813271138732837185185)
      ·
        refine ⟨11948109953354049627888889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15930813271138732837185185 11948109953354049627888889)
        ·
          refine ⟨8961082465015537220916667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11948109953354049627888889 8961082465015537220916667)
          ·
            refine ⟨13441623697523305831375001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8961082465015537220916667 13441623697523305831375001)
            ·
              refine ⟨10081217773142479373531251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13441623697523305831375001 10081217773142479373531251)
              ·
                refine ⟨15121826659713719060296877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10081217773142479373531251 15121826659713719060296877)
                ·
                  refine ⟨5670684997392644647611329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15121826659713719060296877 5670684997392644647611329)
                  ·
                    refine ⟨4253013748044483485708497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5670684997392644647611329 4253013748044483485708497)
                    ·
                      refine ⟨3189760311033362614281373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4253013748044483485708497 3189760311033362614281373)
                      ·
                        rfl

theorem cell23_6212036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_6212036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212036 prefixEnd_6212036 := by exact prefixLift 6212036
  have htrace : WordTrace (prefixWord ++ tailWord_6212036) baseStart_6212036 baseEnd_6212036 := by
    simpa [prefixWord, tailWord_6212036, baseEnd_6212036] using wordTrace_append hprefix tailTrace_6212036
  have hstable : (prefixWord ++ tailWord_6212036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212036).length < 2 ^ (prefixWord ++ tailWord_6212036).sum := by decide
  have hdescent : baseEnd_6212036 < baseStart_6212036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212052 : List Nat := [2, 4, 1, 2, 2, 1, 3, 1, 1, 3, 3]
def baseStart_6212052 : Nat := 118140960795 + 6212052 * 2 ^ 59
def prefixEnd_6212052 : Nat := 4983230072969 + 3 ^ 40 * 6212052 * 2
def baseEnd_6212052 : Nat := 3189768526723834551681299

theorem tailTrace_6212052 : CollatzResearch.WordTrace tailWord_6212052 prefixEnd_6212052 3189768526723834551681299 := by
  unfold tailWord_6212052
  simp only [CollatzResearch.WordTrace]
  refine ⟨113286075045402006430719205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151048100060536008574292273 113286075045402006430719205)
  ·
    refine ⟨21241139071012876205759851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113286075045402006430719205 21241139071012876205759851)
    ·
      refine ⟨31861708606519314308639777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21241139071012876205759851 31861708606519314308639777)
      ·
        refine ⟨23896281454889485731479833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31861708606519314308639777 23896281454889485731479833)
        ·
          refine ⟨17922211091167114298609875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23896281454889485731479833 17922211091167114298609875)
          ·
            refine ⟨26883316636750671447914813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17922211091167114298609875 26883316636750671447914813)
            ·
              refine ⟨10081243738781501792968055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26883316636750671447914813 10081243738781501792968055)
              ·
                refine ⟨15121865608172252689452083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10081243738781501792968055 15121865608172252689452083)
                ·
                  refine ⟨22682798412258379034178125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15121865608172252689452083 22682798412258379034178125)
                  ·
                    refine ⟨8506049404596892137816797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22682798412258379034178125 8506049404596892137816797)
                    ·
                      refine ⟨3189768526723834551681299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8506049404596892137816797 3189768526723834551681299)
                      ·
                        rfl

theorem cell23_6212052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_6212052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212052 prefixEnd_6212052 := by exact prefixLift 6212052
  have htrace : WordTrace (prefixWord ++ tailWord_6212052) baseStart_6212052 baseEnd_6212052 := by
    simpa [prefixWord, tailWord_6212052, baseEnd_6212052] using wordTrace_append hprefix tailTrace_6212052
  have hstable : (prefixWord ++ tailWord_6212052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212052).length < 2 ^ (prefixWord ++ tailWord_6212052).sum := by decide
  have hdescent : baseEnd_6212052 < baseStart_6212052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212075 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 3, 4, 2]
def baseStart_6212075 : Nat := 118140960795 + 6212075 * 2 ^ 59
def prefixEnd_6212075 : Nat := 4983230072969 + 3 ^ 40 * 6212075 * 2
def baseEnd_6212075 : Nat := 3189780336778887961693693

theorem tailTrace_6212075 : CollatzResearch.WordTrace tailWord_6212075 prefixEnd_6212075 3189780336778887961693693 := by
  unfold tailWord_6212075
  simp only [CollatzResearch.WordTrace]
  refine ⟨226572988969720687789525679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151048659313147125193017119 226572988969720687789525679)
  ·
    refine ⟨339859483454581031684288519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226572988969720687789525679 339859483454581031684288519)
    ·
      refine ⟨509789225181871547526432779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339859483454581031684288519 509789225181871547526432779)
      ·
        refine ⟨764683837772807321289649169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509789225181871547526432779 764683837772807321289649169)
        ·
          refine ⟨573512878329605490967236877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 764683837772807321289649169 573512878329605490967236877)
          ·
            refine ⟨215067329373602059112713829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 573512878329605490967236877 215067329373602059112713829)
            ·
              refine ⟨40325124257550386083633843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 215067329373602059112713829 40325124257550386083633843)
              ·
                refine ⟨60487686386325579125450765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40325124257550386083633843 60487686386325579125450765)
                ·
                  refine ⟨22682882394872092172044037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60487686386325579125450765 22682882394872092172044037)
                  ·
                    refine ⟨4253040449038517282258257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22682882394872092172044037 4253040449038517282258257)
                    ·
                      refine ⟨3189780336778887961693693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4253040449038517282258257 3189780336778887961693693)
                      ·
                        rfl

theorem cell23_6212075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 4, 2].length) (baseStart_6212075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212075 prefixEnd_6212075 := by exact prefixLift 6212075
  have htrace : WordTrace (prefixWord ++ tailWord_6212075) baseStart_6212075 baseEnd_6212075 := by
    simpa [prefixWord, tailWord_6212075, baseEnd_6212075] using wordTrace_append hprefix tailTrace_6212075
  have hstable : (prefixWord ++ tailWord_6212075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212075).length < 2 ^ (prefixWord ++ tailWord_6212075).sum := by decide
  have hdescent : baseEnd_6212075 < baseStart_6212075 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212103 : List Nat := [1, 1, 4, 3, 4, 1, 2, 1, 2, 1, 3]
def baseStart_6212103 : Nat := 118140960795 + 6212103 * 2 ^ 59
def prefixEnd_6212103 : Nat := 4983230072969 + 3 ^ 40 * 6212103 * 2
def baseEnd_6212103 : Nat := 3189794714237213852143565

theorem tailTrace_6212103 : CollatzResearch.WordTrace tailWord_6212103 prefixEnd_6212103 3189794714237213852143565 := by
  unfold tailWord_6212103
  simp only [CollatzResearch.WordTrace]
  refine ⟨226574010213619248571544963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151049340142412832381029975 226574010213619248571544963)
  ·
    refine ⟨339861015320428872857317445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226574010213619248571544963 339861015320428872857317445)
    ·
      refine ⟨63723940372580413660747021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 339861015320428872857317445 63723940372580413660747021)
      ·
        refine ⟨23896477639717655122780133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63723940372580413660747021 23896477639717655122780133)
        ·
          refine ⟨4480589557447060335521275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23896477639717655122780133 4480589557447060335521275)
          ·
            refine ⟨6720884336170590503281913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4480589557447060335521275 6720884336170590503281913)
            ·
              refine ⟨5040663252127942877461435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6720884336170590503281913 5040663252127942877461435)
              ·
                refine ⟨7560994878191914316192153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5040663252127942877461435 7560994878191914316192153)
                ·
                  refine ⟨5670746158643935737144115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7560994878191914316192153 5670746158643935737144115)
                  ·
                    refine ⟨8506119237965903605716173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5670746158643935737144115 8506119237965903605716173)
                    ·
                      refine ⟨3189794714237213852143565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8506119237965903605716173 3189794714237213852143565)
                      ·
                        rfl

theorem cell23_6212103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_6212103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212103 prefixEnd_6212103 := by exact prefixLift 6212103
  have htrace : WordTrace (prefixWord ++ tailWord_6212103) baseStart_6212103 baseEnd_6212103 := by
    simpa [prefixWord, tailWord_6212103, baseEnd_6212103] using wordTrace_append hprefix tailTrace_6212103
  have hstable : (prefixWord ++ tailWord_6212103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212103).length < 2 ^ (prefixWord ++ tailWord_6212103).sum := by decide
  have hdescent : baseEnd_6212103 < baseStart_6212103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212145 : List Nat := [1, 2, 2, 3, 1, 1, 4, 2, 2, 5]
def baseStart_6212145 : Nat := 118140960795 + 6212145 * 2 ^ 59
def prefixEnd_6212145 : Nat := 4983230072969 + 3 ^ 40 * 6212145 * 2
def baseEnd_6212145 : Nat := 1063272093474900895939457

theorem tailTrace_6212145 : CollatzResearch.WordTrace tailWord_6212145 prefixEnd_6212145 1063272093474900895939457 := by
  unfold tailWord_6212145
  simp only [CollatzResearch.WordTrace]
  refine ⟨226575542079467089744573889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151050361386311393163049259 226575542079467089744573889)
  ·
    refine ⟨169931656559600317308430417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226575542079467089744573889 169931656559600317308430417)
    ·
      refine ⟨127448742419700237981322813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169931656559600317308430417 127448742419700237981322813)
      ·
        refine ⟨47793278407387589242996055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127448742419700237981322813 47793278407387589242996055)
        ·
          refine ⟨71689917611081383864494083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47793278407387589242996055 71689917611081383864494083)
          ·
            refine ⟨107534876416622075796741125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71689917611081383864494083 107534876416622075796741125)
            ·
              refine ⟨20162789328116639211888961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107534876416622075796741125 20162789328116639211888961)
              ·
                refine ⟨15122091996087479408916721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20162789328116639211888961 15122091996087479408916721)
                ·
                  refine ⟨11341568997065609556687541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15122091996087479408916721 11341568997065609556687541)
                  ·
                    refine ⟨1063272093474900895939457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11341568997065609556687541 1063272093474900895939457)
                    ·
                      rfl

theorem cell23_6212145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 5].length) (baseStart_6212145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212145 prefixEnd_6212145 := by exact prefixLift 6212145
  have htrace : WordTrace (prefixWord ++ tailWord_6212145) baseStart_6212145 baseEnd_6212145 := by
    simpa [prefixWord, tailWord_6212145, baseEnd_6212145] using wordTrace_append hprefix tailTrace_6212145
  have hstable : (prefixWord ++ tailWord_6212145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212145).length < 2 ^ (prefixWord ++ tailWord_6212145).sum := by decide
  have hdescent : baseEnd_6212145 < baseStart_6212145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212175 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 5, 4]
def baseStart_6212175 : Nat := 118140960795 + 6212175 * 2 ^ 59
def prefixEnd_6212175 : Nat := 4983230072969 + 3 ^ 40 * 6212175 * 2
def baseEnd_6212175 : Nat := 1063277228281445856814411

theorem tailTrace_6212175 : CollatzResearch.WordTrace tailWord_6212175 prefixEnd_6212175 1063277228281445856814411 := by
  unfold tailWord_6212175
  simp only [CollatzResearch.WordTrace]
  refine ⟨226576636269358404868165979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151051090846238936578777319 226576636269358404868165979)
  ·
    refine ⟨339864954404037607302248969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226576636269358404868165979 339864954404037607302248969)
    ·
      refine ⟨254898715803028205476686727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339864954404037607302248969 254898715803028205476686727)
      ·
        refine ⟨382348073704542308215030091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254898715803028205476686727 382348073704542308215030091)
        ·
          refine ⟨573522110556813462322545137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382348073704542308215030091 573522110556813462322545137)
          ·
            refine ⟨430141582917610096741908853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 573522110556813462322545137 430141582917610096741908853)
            ·
              refine ⟨40325773398525946569553955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 430141582917610096741908853 40325773398525946569553955)
              ·
                refine ⟨60488660097788919854330933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40325773398525946569553955 60488660097788919854330933)
                ·
                  refine ⟨5670811884167711236343525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60488660097788919854330933 5670811884167711236343525)
                  ·
                    refine ⟨1063277228281445856814411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5670811884167711236343525 1063277228281445856814411)
                    ·
                      rfl

theorem cell23_6212175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5, 4].length) (baseStart_6212175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212175 prefixEnd_6212175 := by exact prefixLift 6212175
  have htrace : WordTrace (prefixWord ++ tailWord_6212175) baseStart_6212175 baseEnd_6212175 := by
    simpa [prefixWord, tailWord_6212175, baseEnd_6212175] using wordTrace_append hprefix tailTrace_6212175
  have hstable : (prefixWord ++ tailWord_6212175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212175).length < 2 ^ (prefixWord ++ tailWord_6212175).sum := by decide
  have hdescent : baseEnd_6212175 < baseStart_6212175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212202 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 4, 2, 3]
def baseStart_6212202 : Nat := 118140960795 + 6212202 * 2 ^ 59
def prefixEnd_6212202 : Nat := 4983230072969 + 3 ^ 40 * 6212202 * 2
def baseEnd_6212202 : Nat := 3189845548822008964805609

theorem tailTrace_6212202 : CollatzResearch.WordTrace tailWord_6212202 prefixEnd_6212202 3189845548822008964805609 := by
  unfold tailWord_6212202
  simp only [CollatzResearch.WordTrace]
  refine ⟨56644405260065147119849715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151051747360173725652932573 56644405260065147119849715)
  ·
    refine ⟨84966607890097720679774573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56644405260065147119849715 84966607890097720679774573)
    ·
      refine ⟨31862477958786645254915465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84966607890097720679774573 31862477958786645254915465)
      ·
        refine ⟨23896858469089983941186599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31862477958786645254915465 23896858469089983941186599)
        ·
          refine ⟨35845287703634975911779899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23896858469089983941186599 35845287703634975911779899)
          ·
            refine ⟨53767931555452463867669849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35845287703634975911779899 53767931555452463867669849)
            ·
              refine ⟨40325948666589347900752387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53767931555452463867669849 40325948666589347900752387)
              ·
                refine ⟨60488922999884021851128581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40325948666589347900752387 60488922999884021851128581)
                ·
                  refine ⟨11341673062478254097086609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60488922999884021851128581 11341673062478254097086609)
                  ·
                    refine ⟨8506254796858690572814957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11341673062478254097086609 8506254796858690572814957)
                    ·
                      refine ⟨3189845548822008964805609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8506254796858690572814957 3189845548822008964805609)
                      ·
                        rfl

theorem cell23_6212202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_6212202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212202 prefixEnd_6212202 := by exact prefixLift 6212202
  have htrace : WordTrace (prefixWord ++ tailWord_6212202) baseStart_6212202 baseEnd_6212202 := by
    simpa [prefixWord, tailWord_6212202, baseEnd_6212202] using wordTrace_append hprefix tailTrace_6212202
  have hstable : (prefixWord ++ tailWord_6212202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212202).length < 2 ^ (prefixWord ++ tailWord_6212202).sum := by decide
  have hdescent : baseEnd_6212202 < baseStart_6212202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212225 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_6212225 : Nat := 118140960795 + 6212225 * 2 ^ 59
def prefixEnd_6212225 : Nat := 4983230072969 + 3 ^ 40 * 6212225 * 2
def baseEnd_6212225 : Nat := 3189857358877062374818003

theorem tailTrace_6212225 : CollatzResearch.WordTrace tailWord_6212225 prefixEnd_6212225 3189857358877062374818003 := by
  unfold tailWord_6212225
  simp only [CollatzResearch.WordTrace]
  refine ⟨226578459919177263407486129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151052306612784842271657419 226578459919177263407486129)
  ·
    refine ⟨169933844939382947555614597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226578459919177263407486129 169933844939382947555614597)
    ·
      refine ⟨31862595926134302666677737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169933844939382947555614597 31862595926134302666677737)
      ·
        refine ⟨23896946944600727000008303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31862595926134302666677737 23896946944600727000008303)
        ·
          refine ⟨35845420416901090500012455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23896946944600727000008303 35845420416901090500012455)
          ·
            refine ⟨53768130625351635750018683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35845420416901090500012455 53768130625351635750018683)
            ·
              refine ⟨80652195938027453625028025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53768130625351635750018683 80652195938027453625028025)
              ·
                refine ⟨60489146953520590218771019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80652195938027453625028025 60489146953520590218771019)
                ·
                  refine ⟨90733720430280885328156529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60489146953520590218771019 90733720430280885328156529)
                  ·
                    refine ⟨68050290322710663996117397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90733720430280885328156529 68050290322710663996117397)
                    ·
                      refine ⟨3189857358877062374818003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68050290322710663996117397 3189857358877062374818003)
                      ·
                        rfl

theorem cell23_6212225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_6212225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212225 prefixEnd_6212225 := by exact prefixLift 6212225
  have htrace : WordTrace (prefixWord ++ tailWord_6212225) baseStart_6212225 baseEnd_6212225 := by
    simpa [prefixWord, tailWord_6212225, baseEnd_6212225] using wordTrace_append hprefix tailTrace_6212225
  have hstable : (prefixWord ++ tailWord_6212225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212225).length < 2 ^ (prefixWord ++ tailWord_6212225).sum := by decide
  have hdescent : baseEnd_6212225 < baseStart_6212225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212273 : List Nat := [1, 2, 2, 6, 2, 1, 2, 1, 6]
def baseStart_6212273 : Nat := 118140960795 + 6212273 * 2 ^ 59
def prefixEnd_6212273 : Nat := 4983230072969 + 3 ^ 40 * 6212273 * 2
def baseEnd_6212273 : Nat := 354431333994275354113087

theorem tailTrace_6212273 : CollatzResearch.WordTrace tailWord_6212273 prefixEnd_6212273 354431333994275354113087 := by
  unfold tailWord_6212273
  simp only [CollatzResearch.WordTrace]
  refine ⟨226580210623003367605233473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151053473748668911736822315 226580210623003367605233473)
  ·
    refine ⟨169935157967252525703925105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226580210623003367605233473 169935157967252525703925105)
    ·
      refine ⟨127451368475439394277943829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169935157967252525703925105 127451368475439394277943829)
      ·
        refine ⟨5974282897286221606778617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 127451368475439394277943829 5974282897286221606778617)
        ·
          refine ⟨4480712172964666205083963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5974282897286221606778617 4480712172964666205083963)
          ·
            refine ⟨6721068259446999307625945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4480712172964666205083963 6721068259446999307625945)
            ·
              refine ⟨5040801194585249480719459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6721068259446999307625945 5040801194585249480719459)
              ·
                refine ⟨7561201791877874221079189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5040801194585249480719459 7561201791877874221079189)
                ·
                  refine ⟨354431333994275354113087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7561201791877874221079189 354431333994275354113087)
                  ·
                    rfl

theorem cell23_6212273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 6].length) (baseStart_6212273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212273 prefixEnd_6212273 := by exact prefixLift 6212273
  have htrace : WordTrace (prefixWord ++ tailWord_6212273) baseStart_6212273 baseEnd_6212273 := by
    simpa [prefixWord, tailWord_6212273, baseEnd_6212273] using wordTrace_append hprefix tailTrace_6212273
  have hstable : (prefixWord ++ tailWord_6212273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212273).length < 2 ^ (prefixWord ++ tailWord_6212273).sum := by decide
  have hdescent : baseEnd_6212273 < baseStart_6212273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212302 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4]
def baseStart_6212302 : Nat := 118140960795 + 6212302 * 2 ^ 59
def prefixEnd_6212302 : Nat := 4983230072969 + 3 ^ 40 * 6212302 * 2
def baseEnd_6212302 : Nat := 3189896896887458573555149

theorem tailTrace_6212302 : CollatzResearch.WordTrace tailWord_6212302 prefixEnd_6212302 3189896896887458573555149 := by
  unfold tailWord_6212302
  simp only [CollatzResearch.WordTrace]
  refine ⟨28322658542487288194754895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151054178893265537038692773 28322658542487288194754895)
  ·
    refine ⟨42483987813730932292132343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28322658542487288194754895 42483987813730932292132343)
    ·
      refine ⟨63725981720596398438198515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42483987813730932292132343 63725981720596398438198515)
      ·
        refine ⟨95588972580894597657297773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63725981720596398438198515 95588972580894597657297773)
        ·
          refine ⟨35845864717835474121486665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95588972580894597657297773 35845864717835474121486665)
          ·
            refine ⟨26884398538376605591114999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35845864717835474121486665 26884398538376605591114999)
            ·
              refine ⟨40326597807564908386672499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26884398538376605591114999 40326597807564908386672499)
              ·
                refine ⟨60489896711347362580008749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40326597807564908386672499 60489896711347362580008749)
                ·
                  refine ⟨22683711266755260967503281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60489896711347362580008749 22683711266755260967503281)
                  ·
                    refine ⟨17012783450066445725627461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22683711266755260967503281 17012783450066445725627461)
                    ·
                      refine ⟨3189896896887458573555149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17012783450066445725627461 3189896896887458573555149)
                      ·
                        rfl

theorem cell23_6212302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_6212302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212302 prefixEnd_6212302 := by exact prefixLift 6212302
  have htrace : WordTrace (prefixWord ++ tailWord_6212302) baseStart_6212302 baseEnd_6212302 := by
    simpa [prefixWord, tailWord_6212302, baseEnd_6212302] using wordTrace_append hprefix tailTrace_6212302
  have hstable : (prefixWord ++ tailWord_6212302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212302).length < 2 ^ (prefixWord ++ tailWord_6212302).sum := by decide
  have hdescent : baseEnd_6212302 < baseStart_6212302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212316 : List Nat := [2, 2, 5, 1, 1, 1, 1, 4, 2, 4]
def baseStart_6212316 : Nat := 118140960795 + 6212316 * 2 ^ 59
def prefixEnd_6212316 : Nat := 4983230072969 + 3 ^ 40 * 6212316 * 2
def baseEnd_6212316 : Nat := 1063301361872207172926695

theorem tailTrace_6212316 : CollatzResearch.WordTrace tailWord_6212316 prefixEnd_6212316 1063301361872207172926695 := by
  unfold tailWord_6212316
  simp only [CollatzResearch.WordTrace]
  refine ⟨113290889480923792974524401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151054519307898390632699201 113290889480923792974524401)
  ·
    refine ⟨84968167110692844730893301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113290889480923792974524401 84968167110692844730893301)
    ·
      refine ⟨7965765666627454193521247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84968167110692844730893301 7965765666627454193521247)
      ·
        refine ⟨11948648499941181290281871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7965765666627454193521247 11948648499941181290281871)
        ·
          refine ⟨17922972749911771935422807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11948648499941181290281871 17922972749911771935422807)
          ·
            refine ⟨26884459124867657903134211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17922972749911771935422807 26884459124867657903134211)
            ·
              refine ⟨40326688687301486854701317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26884459124867657903134211 40326688687301486854701317)
              ·
                refine ⟨7561254128869028785256497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40326688687301486854701317 7561254128869028785256497)
                ·
                  refine ⟨5670940596651771588942373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7561254128869028785256497 5670940596651771588942373)
                  ·
                    refine ⟨1063301361872207172926695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5670940596651771588942373 1063301361872207172926695)
                    ·
                      rfl

theorem cell23_6212316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_6212316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212316 prefixEnd_6212316 := by exact prefixLift 6212316
  have htrace : WordTrace (prefixWord ++ tailWord_6212316) baseStart_6212316 baseEnd_6212316 := by
    simpa [prefixWord, tailWord_6212316, baseEnd_6212316] using wordTrace_append hprefix tailTrace_6212316
  have hstable : (prefixWord ++ tailWord_6212316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212316).length < 2 ^ (prefixWord ++ tailWord_6212316).sum := by decide
  have hdescent : baseEnd_6212316 < baseStart_6212316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212342 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 2, 7]
def baseStart_6212342 : Nat := 118140960795 + 6212342 * 2 ^ 59
def prefixEnd_6212342 : Nat := 4983230072969 + 3 ^ 40 * 6212342 * 2
def baseEnd_6212342 : Nat := 1063305812037879472351655

theorem tailTrace_6212342 : CollatzResearch.WordTrace tailWord_6212342 prefixEnd_6212342 1063305812037879472351655 := by
  unfold tailWord_6212342
  simp only [CollatzResearch.WordTrace]
  refine ⟨14161420453734587024343455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151055151506502261592996853 14161420453734587024343455)
  ·
    refine ⟨21242130680601880536515183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14161420453734587024343455 21242130680601880536515183)
    ·
      refine ⟨31863196020902820804772775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21242130680601880536515183 31863196020902820804772775)
      ·
        refine ⟨47794794031354231207159163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31863196020902820804772775 47794794031354231207159163)
        ·
          refine ⟨71692191047031346810738745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47794794031354231207159163 71692191047031346810738745)
          ·
            refine ⟨53769143285273510108054059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71692191047031346810738745 53769143285273510108054059)
            ·
              refine ⟨80653714927910265162081089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53769143285273510108054059 80653714927910265162081089)
              ·
                refine ⟨60490286195932698871560817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80653714927910265162081089 60490286195932698871560817)
                ·
                  refine ⟨45367714646949524153670613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60490286195932698871560817 45367714646949524153670613)
                  ·
                    refine ⟨1063305812037879472351655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45367714646949524153670613 1063305812037879472351655)
                    ·
                      rfl

theorem cell23_6212342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_6212342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212342 prefixEnd_6212342 := by exact prefixLift 6212342
  have htrace : WordTrace (prefixWord ++ tailWord_6212342) baseStart_6212342 baseEnd_6212342 := by
    simpa [prefixWord, tailWord_6212342, baseEnd_6212342] using wordTrace_append hprefix tailTrace_6212342
  have hstable : (prefixWord ++ tailWord_6212342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212342).length < 2 ^ (prefixWord ++ tailWord_6212342).sum := by decide
  have hdescent : baseEnd_6212342 < baseStart_6212342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212349 : List Nat := [1, 4, 1, 1, 1, 1, 3, 3, 3, 3, 2]
def baseStart_6212349 : Nat := 118140960795 + 6212349 * 2 ^ 59
def prefixEnd_6212349 : Nat := 4983230072969 + 3 ^ 40 * 6212349 * 2
def baseEnd_6212349 : Nat := 3189921030478219889667433

theorem tailTrace_6212349 : CollatzResearch.WordTrace tailWord_6212349 prefixEnd_6212349 3189921030478219889667433 := by
  unfold tailWord_6212349
  simp only [CollatzResearch.WordTrace]
  refine ⟨226582982570728032585000101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151055321713818688390000067 226582982570728032585000101)
  ·
    refine ⟨42484309232011506109687519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226582982570728032585000101 42484309232011506109687519)
    ·
      refine ⟨63726463848017259164531279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42484309232011506109687519 63726463848017259164531279)
      ·
        refine ⟨95589695772025888746796919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63726463848017259164531279 95589695772025888746796919)
        ·
          refine ⟨143384543658038833120195379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95589695772025888746796919 143384543658038833120195379)
          ·
            refine ⟨215076815487058249680293069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143384543658038833120195379 215076815487058249680293069)
            ·
              refine ⟨80653805807646843630109901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215076815487058249680293069 80653805807646843630109901)
              ·
                refine ⟨30245177177867566361291213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80653805807646843630109901 30245177177867566361291213)
                ·
                  refine ⟨11341941441700337385484205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30245177177867566361291213 11341941441700337385484205)
                  ·
                    refine ⟨4253228040637626519556577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11341941441700337385484205 4253228040637626519556577)
                    ·
                      refine ⟨3189921030478219889667433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4253228040637626519556577 3189921030478219889667433)
                      ·
                        rfl

theorem cell23_6212349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 3, 2].length) (baseStart_6212349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212349 prefixEnd_6212349 := by exact prefixLift 6212349
  have htrace : WordTrace (prefixWord ++ tailWord_6212349) baseStart_6212349 baseEnd_6212349 := by
    simpa [prefixWord, tailWord_6212349, baseEnd_6212349] using wordTrace_append hprefix tailTrace_6212349
  have hstable : (prefixWord ++ tailWord_6212349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212349).length < 2 ^ (prefixWord ++ tailWord_6212349).sum := by decide
  have hdescent : baseEnd_6212349 < baseStart_6212349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212355 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 3, 8]
def baseStart_6212355 : Nat := 118140960795 + 6212355 * 2 ^ 59
def prefixEnd_6212355 : Nat := 4983230072969 + 3 ^ 40 * 6212355 * 2
def baseEnd_6212355 : Nat := 1063308037120715622064135

theorem tailTrace_6212355 : CollatzResearch.WordTrace tailWord_6212355 prefixEnd_6212355 1063308037120715622064135 := by
  unfold tailWord_6212355
  simp only [CollatzResearch.WordTrace]
  refine ⟨226583201408706295609718519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151055467605804197073145679 226583201408706295609718519)
  ·
    refine ⟨339874802113059443414577779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226583201408706295609718519 339874802113059443414577779)
    ·
      refine ⟨509812203169589165121866669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339874802113059443414577779 509812203169589165121866669)
      ·
        refine ⟨191179576188595936920700001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 509812203169589165121866669 191179576188595936920700001)
        ·
          refine ⟨143384682141446952690525001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191179576188595936920700001 143384682141446952690525001)
          ·
            refine ⟨107538511606085214517893751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143384682141446952690525001 107538511606085214517893751)
            ·
              refine ⟨161307767409127821776840627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107538511606085214517893751 161307767409127821776840627)
              ·
                refine ⟨241961651113691732665260941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161307767409127821776840627 241961651113691732665260941)
                ·
                  refine ⟨90735619167634399749472853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241961651113691732665260941 90735619167634399749472853)
                  ·
                    refine ⟨1063308037120715622064135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90735619167634399749472853 1063308037120715622064135)
                    ·
                      rfl

theorem cell23_6212355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 8].length) (baseStart_6212355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212355 prefixEnd_6212355 := by exact prefixLift 6212355
  have htrace : WordTrace (prefixWord ++ tailWord_6212355) baseStart_6212355 baseEnd_6212355 := by
    simpa [prefixWord, tailWord_6212355, baseEnd_6212355] using wordTrace_append hprefix tailTrace_6212355
  have hstable : (prefixWord ++ tailWord_6212355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212355).length < 2 ^ (prefixWord ++ tailWord_6212355).sum := by decide
  have hdescent : baseEnd_6212355 < baseStart_6212355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212402 : List Nat := [3, 2, 1, 1, 3, 1, 1, 4, 7]
def baseStart_6212402 : Nat := 118140960795 + 6212402 * 2 ^ 59
def prefixEnd_6212402 : Nat := 4983230072969 + 3 ^ 40 * 6212402 * 2
def baseEnd_6212402 : Nat := 354438693883656464700521

theorem tailTrace_6212402 : CollatzResearch.WordTrace tailWord_6212402 prefixEnd_6212402 354438693883656464700521 := by
  unfold tailWord_6212402
  simp only [CollatzResearch.WordTrace]
  refine ⟨56646228909884005659169865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151056610426357348424452973 56646228909884005659169865)
  ·
    refine ⟨42484671682413004244377399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56646228909884005659169865 42484671682413004244377399)
    ·
      refine ⟨63727007523619506366566099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42484671682413004244377399 63727007523619506366566099)
      ·
        refine ⟨95590511285429259549849149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63727007523619506366566099 95590511285429259549849149)
        ·
          refine ⟨35846441732035972331193431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95590511285429259549849149 35846441732035972331193431)
          ·
            refine ⟨53769662598053958496790147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35846441732035972331193431 53769662598053958496790147)
            ·
              refine ⟨80654493897080937745185221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53769662598053958496790147 80654493897080937745185221)
              ·
                refine ⟨15122717605702675827222229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80654493897080937745185221 15122717605702675827222229)
                ·
                  refine ⟨354438693883656464700521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15122717605702675827222229 354438693883656464700521)
                  ·
                    rfl

theorem cell23_6212402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_6212402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212402 prefixEnd_6212402 := by exact prefixLift 6212402
  have htrace : WordTrace (prefixWord ++ tailWord_6212402) baseStart_6212402 baseEnd_6212402 := by
    simpa [prefixWord, tailWord_6212402, baseEnd_6212402] using wordTrace_append hprefix tailTrace_6212402
  have hstable : (prefixWord ++ tailWord_6212402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212402).length < 2 ^ (prefixWord ++ tailWord_6212402).sum := by decide
  have hdescent : baseEnd_6212402 < baseStart_6212402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212432 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 4, 5]
def baseStart_6212432 : Nat := 118140960795 + 6212432 * 2 ^ 59
def prefixEnd_6212432 : Nat := 4983230072969 + 3 ^ 40 * 6212432 * 2
def baseEnd_6212432 : Nat := 1063321216457514354976517

theorem tailTrace_6212432 : CollatzResearch.WordTrace tailWord_6212432 prefixEnd_6212432 1063321216457514354976517 := by
  unfold tailWord_6212432
  simp only [CollatzResearch.WordTrace]
  refine ⟨113293004914713668880135775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151057339886284891840181033 113293004914713668880135775)
  ·
    refine ⟨169939507372070503320203663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113293004914713668880135775 169939507372070503320203663)
    ·
      refine ⟨254909261058105754980305495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169939507372070503320203663 254909261058105754980305495)
      ·
        refine ⟨382363891587158632470458243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254909261058105754980305495 382363891587158632470458243)
        ·
          refine ⟨573545837380737948705687365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382363891587158632470458243 573545837380737948705687365)
          ·
            refine ⟨107539844508888365382316381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 573545837380737948705687365 107539844508888365382316381)
            ·
              refine ⟨40327441690833137018368643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107539844508888365382316381 40327441690833137018368643)
              ·
                refine ⟨60491162536249705527552965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40327441690833137018368643 60491162536249705527552965)
                ·
                  refine ⟨11342092975546819786416181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60491162536249705527552965 11342092975546819786416181)
                  ·
                    refine ⟨1063321216457514354976517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11342092975546819786416181 1063321216457514354976517)
                    ·
                      rfl

theorem cell23_6212432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 4, 5].length) (baseStart_6212432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212432 prefixEnd_6212432 := by exact prefixLift 6212432
  have htrace : WordTrace (prefixWord ++ tailWord_6212432) baseStart_6212432 baseEnd_6212432 := by
    simpa [prefixWord, tailWord_6212432, baseEnd_6212432] using wordTrace_append hprefix tailTrace_6212432
  have hstable : (prefixWord ++ tailWord_6212432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212432).length < 2 ^ (prefixWord ++ tailWord_6212432).sum := by decide
  have hdescent : baseEnd_6212432 < baseStart_6212432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212436 : List Nat := [2, 4, 1, 1, 4, 2, 1, 1, 7]
def baseStart_6212436 : Nat := 118140960795 + 6212436 * 2 ^ 59
def prefixEnd_6212436 : Nat := 4983230072969 + 3 ^ 40 * 6212436 * 2
def baseEnd_6212436 : Nat := 354440633699462338808837

theorem tailTrace_6212436 : CollatzResearch.WordTrace tailWord_6212436 prefixEnd_6212436 354440633699462338808837 := by
  unfold tailWord_6212436
  simp only [CollatzResearch.WordTrace]
  refine ⟨113293077860706423221708581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151057437147608564295611441 113293077860706423221708581)
  ·
    refine ⟨21242452098882454354070359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113293077860706423221708581 21242452098882454354070359)
    ·
      refine ⟨31863678148323681531105539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21242452098882454354070359 31863678148323681531105539)
      ·
        refine ⟨47795517222485522296658309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31863678148323681531105539 47795517222485522296658309)
        ·
          refine ⟨8961659479216035430623433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47795517222485522296658309 8961659479216035430623433)
          ·
            refine ⟨6721244609412026572967575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8961659479216035430623433 6721244609412026572967575)
            ·
              refine ⟨10081866914118039859451363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6721244609412026572967575 10081866914118039859451363)
              ·
                refine ⟨15122800371177059789177045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10081866914118039859451363 15122800371177059789177045)
                ·
                  refine ⟨354440633699462338808837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15122800371177059789177045 354440633699462338808837)
                  ·
                    rfl

theorem cell23_6212436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_6212436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212436 prefixEnd_6212436 := by exact prefixLift 6212436
  have htrace : WordTrace (prefixWord ++ tailWord_6212436) baseStart_6212436 baseEnd_6212436 := by
    simpa [prefixWord, tailWord_6212436, baseEnd_6212436] using wordTrace_append hprefix tailTrace_6212436
  have hstable : (prefixWord ++ tailWord_6212436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212436).length < 2 ^ (prefixWord ++ tailWord_6212436).sum := by decide
  have hdescent : baseEnd_6212436 < baseStart_6212436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212442 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7]
def baseStart_6212442 : Nat := 118140960795 + 6212442 * 2 ^ 59
def prefixEnd_6212442 : Nat := 4983230072969 + 3 ^ 40 * 6212442 * 2
def baseEnd_6212442 : Nat := 3189968784179088025804505

theorem tailTrace_6212442 : CollatzResearch.WordTrace tailWord_6212442 prefixEnd_6212442 3189968784179088025804505 := by
  unfold tailWord_6212442
  simp only [CollatzResearch.WordTrace]
  refine ⟨56646593639847777367033895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151057583039594072978757053 56646593639847777367033895)
  ·
    refine ⟨84969890459771666050550843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56646593639847777367033895 84969890459771666050550843)
    ·
      refine ⟨127454835689657499075826265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84969890459771666050550843 127454835689657499075826265)
      ·
        refine ⟨95591126767243124306869699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127454835689657499075826265 95591126767243124306869699)
        ·
          refine ⟨143386690150864686460304549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95591126767243124306869699 143386690150864686460304549)
          ·
            refine ⟨26885004403287128711307103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143386690150864686460304549 26885004403287128711307103)
            ·
              refine ⟨40327506604930693066960655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26885004403287128711307103 40327506604930693066960655)
              ·
                refine ⟨60491259907396039600440983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40327506604930693066960655 60491259907396039600440983)
                ·
                  refine ⟨90736889861094059400661475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60491259907396039600440983 90736889861094059400661475)
                  ·
                    refine ⟨136105334791641089100992213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90736889861094059400661475 136105334791641089100992213)
                    ·
                      refine ⟨3189968784179088025804505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 136105334791641089100992213 3189968784179088025804505)
                      ·
                        rfl

theorem cell23_6212442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_6212442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212442 prefixEnd_6212442 := by exact prefixLift 6212442
  have htrace : WordTrace (prefixWord ++ tailWord_6212442) baseStart_6212442 baseEnd_6212442 := by
    simpa [prefixWord, tailWord_6212442, baseEnd_6212442] using wordTrace_append hprefix tailTrace_6212442
  have hstable : (prefixWord ++ tailWord_6212442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212442).length < 2 ^ (prefixWord ++ tailWord_6212442).sum := by decide
  have hdescent : baseEnd_6212442 < baseStart_6212442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212492 : List Nat := [2, 2, 1, 2, 1, 2, 2, 3, 8]
def baseStart_6212492 : Nat := 118140960795 + 6212492 * 2 ^ 59
def prefixEnd_6212492 : Nat := 4983230072969 + 3 ^ 40 * 6212492 * 2
def baseEnd_6212492 : Nat := 354443828690201425575475

theorem tailTrace_6212492 : CollatzResearch.WordTrace tailWord_6212492 prefixEnd_6212492 354443828690201425575475 := by
  unfold tailWord_6212492
  simp only [CollatzResearch.WordTrace]
  refine ⟨113294099104604984003727865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151058798806139978671637153 113294099104604984003727865)
  ·
    refine ⟨84970574328453738002795899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113294099104604984003727865 84970574328453738002795899)
    ·
      refine ⟨127455861492680607004193849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84970574328453738002795899 127455861492680607004193849)
      ·
        refine ⟨95591896119510455253145387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127455861492680607004193849 95591896119510455253145387)
        ·
          refine ⟨143387844179265682879718081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95591896119510455253145387 143387844179265682879718081)
          ·
            refine ⟨107540883134449262159788561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143387844179265682879718081 107540883134449262159788561)
            ·
              refine ⟨80655662350836946619841421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107540883134449262159788561 80655662350836946619841421)
              ·
                refine ⟨30245873381563854982440533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80655662350836946619841421 30245873381563854982440533)
                ·
                  refine ⟨354443828690201425575475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30245873381563854982440533 354443828690201425575475)
                  ·
                    rfl

theorem cell23_6212492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 8].length) (baseStart_6212492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212492 prefixEnd_6212492 := by exact prefixLift 6212492
  have htrace : WordTrace (prefixWord ++ tailWord_6212492) baseStart_6212492 baseEnd_6212492 := by
    simpa [prefixWord, tailWord_6212492, baseEnd_6212492] using wordTrace_append hprefix tailTrace_6212492
  have hstable : (prefixWord ++ tailWord_6212492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212492).length < 2 ^ (prefixWord ++ tailWord_6212492).sum := by decide
  have hdescent : baseEnd_6212492 < baseStart_6212492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212509 : List Nat := [1, 4, 2, 1, 2, 1, 1, 5, 6]
def baseStart_6212509 : Nat := 118140960795 + 6212509 * 2 ^ 59
def prefixEnd_6212509 : Nat := 4983230072969 + 3 ^ 40 * 6212509 * 2
def baseEnd_6212509 : Nat := 354444798598104362629633

theorem tailTrace_6212509 : CollatzResearch.WordTrace tailWord_6212509 prefixEnd_6212509 354444798598104362629633 := by
  unfold tailWord_6212509
  simp only [CollatzResearch.WordTrace]
  refine ⟨226588818250148379910824581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151059212166765586607216387 226588818250148379910824581)
  ·
    refine ⟨42485403421902821233279609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226588818250148379910824581 42485403421902821233279609)
    ·
      refine ⟨31864052566427115924959707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42485403421902821233279609 31864052566427115924959707)
      ·
        refine ⟨47796078849640673887439561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31864052566427115924959707 47796078849640673887439561)
        ·
          refine ⟨35847059137230505415579671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47796078849640673887439561 35847059137230505415579671)
          ·
            refine ⟨53770588705845758123369507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35847059137230505415579671 53770588705845758123369507)
            ·
              refine ⟨80655883058768637185054261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53770588705845758123369507 80655883058768637185054261)
              ·
                refine ⟨7561489036759559736098837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80655883058768637185054261 7561489036759559736098837)
                ·
                  refine ⟨354444798598104362629633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7561489036759559736098837 354444798598104362629633)
                  ·
                    rfl

theorem cell23_6212509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 6].length) (baseStart_6212509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212509 prefixEnd_6212509 := by exact prefixLift 6212509
  have htrace : WordTrace (prefixWord ++ tailWord_6212509) baseStart_6212509 baseEnd_6212509 := by
    simpa [prefixWord, tailWord_6212509, baseEnd_6212509] using wordTrace_append hprefix tailTrace_6212509
  have hstable : (prefixWord ++ tailWord_6212509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212509).length < 2 ^ (prefixWord ++ tailWord_6212509).sum := by decide
  have hdescent : baseEnd_6212509 < baseStart_6212509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212573 : List Nat := [1, 4, 3, 1, 2, 2, 2, 2, 1, 5]
def baseStart_6212573 : Nat := 118140960795 + 6212573 * 2 ^ 59
def prefixEnd_6212573 : Nat := 4983230072969 + 3 ^ 40 * 6212573 * 2
def baseEnd_6212573 : Nat := 1063345350048275671088801

theorem tailTrace_6212573 : CollatzResearch.WordTrace tailWord_6212573 prefixEnd_6212573 1063345350048275671088801 := by
  unfold tailWord_6212573
  simp only [CollatzResearch.WordTrace]
  refine ⟨226591152521916518841154373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151060768347944345894102915 226591152521916518841154373)
  ·
    refine ⟨42485841097859347282716445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226591152521916518841154373 42485841097859347282716445)
    ·
      refine ⟨15932190411697255231018667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42485841097859347282716445 15932190411697255231018667)
      ·
        refine ⟨23898285617545882846528001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15932190411697255231018667 23898285617545882846528001)
        ·
          refine ⟨17923714213159412134896001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23898285617545882846528001 17923714213159412134896001)
          ·
            refine ⟨13442785659869559101172001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17923714213159412134896001 13442785659869559101172001)
            ·
              refine ⟨10082089244902169325879001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13442785659869559101172001 10082089244902169325879001)
              ·
                refine ⟨7561566933676626994409251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10082089244902169325879001 7561566933676626994409251)
                ·
                  refine ⟨11342350400514940491613877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7561566933676626994409251 11342350400514940491613877)
                  ·
                    refine ⟨1063345350048275671088801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11342350400514940491613877 1063345350048275671088801)
                    ·
                      rfl

theorem cell23_6212573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_6212573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212573 prefixEnd_6212573 := by exact prefixLift 6212573
  have htrace : WordTrace (prefixWord ++ tailWord_6212573) baseStart_6212573 baseEnd_6212573 := by
    simpa [prefixWord, tailWord_6212573, baseEnd_6212573] using wordTrace_append hprefix tailTrace_6212573
  have hstable : (prefixWord ++ tailWord_6212573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212573).length < 2 ^ (prefixWord ++ tailWord_6212573).sum := by decide
  have hdescent : baseEnd_6212573 < baseStart_6212573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212579 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 5]
def baseStart_6212579 : Nat := 118140960795 + 6212579 * 2 ^ 59
def prefixEnd_6212579 : Nat := 4983230072969 + 3 ^ 40 * 6212579 * 2
def baseEnd_6212579 : Nat := 3190039131028753989791375

theorem tailTrace_6212579 : CollatzResearch.WordTrace tailWord_6212579 prefixEnd_6212579 3190039131028753989791375 := by
  unfold tailWord_6212579
  simp only [CollatzResearch.WordTrace]
  refine ⟨226591371359894781865872791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151060914239929854577248527 226591371359894781865872791)
  ·
    refine ⟨339887057039842172798809187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226591371359894781865872791 339887057039842172798809187)
    ·
      refine ⟨509830585559763259198213781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339887057039842172798809187 509830585559763259198213781)
      ·
        refine ⟨23898308698113902774916271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 509830585559763259198213781 23898308698113902774916271)
        ·
          refine ⟨35847463047170854162374407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23898308698113902774916271 35847463047170854162374407)
          ·
            refine ⟨53771194570756281243561611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35847463047170854162374407 53771194570756281243561611)
            ·
              refine ⟨80656791856134421865342417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53771194570756281243561611 80656791856134421865342417)
              ·
                refine ⟨60492593892100816399006813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80656791856134421865342417 60492593892100816399006813)
                ·
                  refine ⟨22684722709537806149627555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60492593892100816399006813 22684722709537806149627555)
                  ·
                    refine ⟨34027084064306709224441333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22684722709537806149627555 34027084064306709224441333)
                    ·
                      refine ⟨3190039131028753989791375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34027084064306709224441333 3190039131028753989791375)
                      ·
                        rfl

theorem cell23_6212579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_6212579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212579 prefixEnd_6212579 := by exact prefixLift 6212579
  have htrace : WordTrace (prefixWord ++ tailWord_6212579) baseStart_6212579 baseEnd_6212579 := by
    simpa [prefixWord, tailWord_6212579, baseEnd_6212579] using wordTrace_append hprefix tailTrace_6212579
  have hstable : (prefixWord ++ tailWord_6212579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212579).length < 2 ^ (prefixWord ++ tailWord_6212579).sum := by decide
  have hdescent : baseEnd_6212579 < baseStart_6212579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212586 : List Nat := [3, 1, 3, 1, 2, 2, 1, 2, 4, 4]
def baseStart_6212586 : Nat := 118140960795 + 6212586 * 2 ^ 59
def prefixEnd_6212586 : Nat := 4983230072969 + 3 ^ 40 * 6212586 * 2
def baseEnd_6212586 : Nat := 1063347575131111820801281

theorem tailTrace_6212586 : CollatzResearch.WordTrace tailWord_6212586 prefixEnd_6212586 1063347575131111820801281 := by
  unfold tailWord_6212586
  simp only [CollatzResearch.WordTrace]
  refine ⟨56647906667717355515344403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151061084447246281374251741 56647906667717355515344403)
  ·
    refine ⟨84971860001576033273016605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56647906667717355515344403 84971860001576033273016605)
    ·
      refine ⟨31864447500591012477381227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84971860001576033273016605 31864447500591012477381227)
      ·
        refine ⟨47796671250886518716071841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31864447500591012477381227 47796671250886518716071841)
        ·
          refine ⟨35847503438164889037053881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47796671250886518716071841 35847503438164889037053881)
          ·
            refine ⟨26885627578623666777790411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35847503438164889037053881 26885627578623666777790411)
            ·
              refine ⟨40328441367935500166685617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26885627578623666777790411 40328441367935500166685617)
              ·
                refine ⟨30246331025951625125014213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40328441367935500166685617 30246331025951625125014213)
                ·
                  refine ⟨5671187067365929710940165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30246331025951625125014213 5671187067365929710940165)
                  ·
                    refine ⟨1063347575131111820801281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5671187067365929710940165 1063347575131111820801281)
                    ·
                      rfl

theorem cell23_6212586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_6212586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212586 prefixEnd_6212586 := by exact prefixLift 6212586
  have htrace : WordTrace (prefixWord ++ tailWord_6212586) baseStart_6212586 baseEnd_6212586 := by
    simpa [prefixWord, tailWord_6212586, baseEnd_6212586] using wordTrace_append hprefix tailTrace_6212586
  have hstable : (prefixWord ++ tailWord_6212586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212586).length < 2 ^ (prefixWord ++ tailWord_6212586).sum := by decide
  have hdescent : baseEnd_6212586 < baseStart_6212586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212597 : List Nat := [1, 3, 5, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_6212597 : Nat := 118140960795 + 6212597 * 2 ^ 59
def prefixEnd_6212597 : Nat := 4983230072969 + 3 ^ 40 * 6212597 * 2
def baseEnd_6212597 : Nat := 3190048373680534919366293

theorem tailTrace_6212597 : CollatzResearch.WordTrace tailWord_6212597 prefixEnd_6212597 3190048373680534919366293 := by
  unfold tailWord_6212597
  simp only [CollatzResearch.WordTrace]
  refine ⟨226592027873829570940028045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151061351915886380626685363 226592027873829570940028045)
  ·
    refine ⟨84972010452686089102510517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226592027873829570940028045 84972010452686089102510517)
    ·
      refine ⟨7966125979939320853360361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84972010452686089102510517 7966125979939320853360361)
      ·
        refine ⟨5974594484954490640020271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7966125979939320853360361 5974594484954490640020271)
        ·
          refine ⟨8961891727431735960030407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5974594484954490640020271 8961891727431735960030407)
          ·
            refine ⟨13442837591147603940045611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8961891727431735960030407 13442837591147603940045611)
            ·
              refine ⟨20164256386721405910068417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13442837591147603940045611 20164256386721405910068417)
              ·
                refine ⟨15123192290041054432551313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20164256386721405910068417 15123192290041054432551313)
                ·
                  refine ⟨11342394217530790824413485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15123192290041054432551313 11342394217530790824413485)
                  ·
                    refine ⟨4253397831574046559155057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11342394217530790824413485 4253397831574046559155057)
                    ·
                      refine ⟨3190048373680534919366293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4253397831574046559155057 3190048373680534919366293)
                      ·
                        rfl

theorem cell23_6212597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_6212597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212597 prefixEnd_6212597 := by exact prefixLift 6212597
  have htrace : WordTrace (prefixWord ++ tailWord_6212597) baseStart_6212597 baseEnd_6212597 := by
    simpa [prefixWord, tailWord_6212597, baseEnd_6212597] using wordTrace_append hprefix tailTrace_6212597
  have hstable : (prefixWord ++ tailWord_6212597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212597).length < 2 ^ (prefixWord ++ tailWord_6212597).sum := by decide
  have hdescent : baseEnd_6212597 < baseStart_6212597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212620 : List Nat := [2, 2, 1, 2, 3, 4, 2, 1, 2, 4]
def baseStart_6212620 : Nat := 118140960795 + 6212620 * 2 ^ 59
def prefixEnd_6212620 : Nat := 4983230072969 + 3 ^ 40 * 6212620 * 2
def baseEnd_6212620 : Nat := 1063353394578529443126229

theorem tailTrace_6212620 : CollatzResearch.WordTrace tailWord_6212620 prefixEnd_6212620 1063353394578529443126229 := by
  unfold tailWord_6212620
  simp only [CollatzResearch.WordTrace]
  refine ⟨113296433376373122934057657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151061911168497497245410209 113296433376373122934057657)
  ·
    refine ⟨84972325032279842200543243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113296433376373122934057657 84972325032279842200543243)
    ·
      refine ⟨127458487548419763300814865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84972325032279842200543243 127458487548419763300814865)
      ·
        refine ⟨95593865661314822475611149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127458487548419763300814865 95593865661314822475611149)
        ·
          refine ⟨35847699622993058428354181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95593865661314822475611149 35847699622993058428354181)
          ·
            refine ⟨6721443679311198455316409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35847699622993058428354181 6721443679311198455316409)
            ·
              refine ⟨5041082759483398841487307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6721443679311198455316409 5041082759483398841487307)
              ·
                refine ⟨7561624139225098262230961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5041082759483398841487307 7561624139225098262230961)
                ·
                  refine ⟨5671218104418823696673221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7561624139225098262230961 5671218104418823696673221)
                  ·
                    refine ⟨1063353394578529443126229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5671218104418823696673221 1063353394578529443126229)
                    ·
                      rfl

theorem cell23_6212620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 2, 4].length) (baseStart_6212620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212620 prefixEnd_6212620 := by exact prefixLift 6212620
  have htrace : WordTrace (prefixWord ++ tailWord_6212620) baseStart_6212620 baseEnd_6212620 := by
    simpa [prefixWord, tailWord_6212620, baseEnd_6212620] using wordTrace_append hprefix tailTrace_6212620
  have hstable : (prefixWord ++ tailWord_6212620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212620).length < 2 ^ (prefixWord ++ tailWord_6212620).sum := by decide
  have hdescent : baseEnd_6212620 < baseStart_6212620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212647 : List Nat := [1, 1, 7, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_6212647 : Nat := 118140960795 + 6212647 * 2 ^ 59
def prefixEnd_6212647 : Nat := 4983230072969 + 3 ^ 40 * 6212647 * 2
def baseEnd_6212647 : Nat := 3190074047713259723741063

theorem tailTrace_6212647 : CollatzResearch.WordTrace tailWord_6212647 prefixEnd_6212647 3190074047713259723741063 := by
  unfold tailWord_6212647
  simp only [CollatzResearch.WordTrace]
  refine ⟨226593851523648429479348195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151062567682432286319565463 226593851523648429479348195)
  ·
    refine ⟨339890777285472644219022293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226593851523648429479348195 339890777285472644219022293)
    ·
      refine ⟨7966190092628265098883335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 339890777285472644219022293 7966190092628265098883335)
      ·
        refine ⟨11949285138942397648325003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7966190092628265098883335 11949285138942397648325003)
        ·
          refine ⟨17923927708413596472487505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11949285138942397648325003 17923927708413596472487505)
          ·
            refine ⟨13442945781310197354365629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17923927708413596472487505 13442945781310197354365629)
            ·
              refine ⟨5041104667991324007887111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13442945781310197354365629 5041104667991324007887111)
              ·
                refine ⟨7561657001986986011830667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5041104667991324007887111 7561657001986986011830667)
                ·
                  refine ⟨11342485502980479017746001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7561657001986986011830667 11342485502980479017746001)
                  ·
                    refine ⟨8506864127235359263309501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11342485502980479017746001 8506864127235359263309501)
                    ·
                      refine ⟨3190074047713259723741063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8506864127235359263309501 3190074047713259723741063)
                      ·
                        rfl

theorem cell23_6212647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_6212647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212647 prefixEnd_6212647 := by exact prefixLift 6212647
  have htrace : WordTrace (prefixWord ++ tailWord_6212647) baseStart_6212647 baseEnd_6212647 := by
    simpa [prefixWord, tailWord_6212647, baseEnd_6212647] using wordTrace_append hprefix tailTrace_6212647
  have hstable : (prefixWord ++ tailWord_6212647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212647).length < 2 ^ (prefixWord ++ tailWord_6212647).sum := by decide
  have hdescent : baseEnd_6212647 < baseStart_6212647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212659 : List Nat := [1, 1, 1, 2, 4, 1, 1, 4, 2, 6]
def baseStart_6212659 : Nat := 118140960795 + 6212659 * 2 ^ 59
def prefixEnd_6212659 : Nat := 4983230072969 + 3 ^ 40 * 6212659 * 2
def baseEnd_6212659 : Nat := 1063360069827037892263669

theorem tailTrace_6212659 : CollatzResearch.WordTrace tailWord_6212659 prefixEnd_6212659 1063360069827037892263669 := by
  unfold tailWord_6212659
  simp only [CollatzResearch.WordTrace]
  refine ⟨226594289199604955528785031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151062859466403303685856687 226594289199604955528785031)
  ·
    refine ⟨339891433799407433293177547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226594289199604955528785031 339891433799407433293177547)
    ·
      refine ⟨509837150699111149939766321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339891433799407433293177547 509837150699111149939766321)
      ·
        refine ⟨382377863024333362454824741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 509837150699111149939766321 382377863024333362454824741)
        ·
          refine ⟨71695849317062505460279639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 382377863024333362454824741 71695849317062505460279639)
          ·
            refine ⟨107543773975593758190419459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71695849317062505460279639 107543773975593758190419459)
            ·
              refine ⟨161315660963390637285629189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107543773975593758190419459 161315660963390637285629189)
              ·
                refine ⟨30246686430635744491055473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161315660963390637285629189 30246686430635744491055473)
                ·
                  refine ⟨22685014822976808368291605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30246686430635744491055473 22685014822976808368291605)
                  ·
                    refine ⟨1063360069827037892263669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22685014822976808368291605 1063360069827037892263669)
                    ·
                      rfl

theorem cell23_6212659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 6].length) (baseStart_6212659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212659 prefixEnd_6212659 := by exact prefixLift 6212659
  have htrace : WordTrace (prefixWord ++ tailWord_6212659) baseStart_6212659 baseEnd_6212659 := by
    simpa [prefixWord, tailWord_6212659, baseEnd_6212659] using wordTrace_append hprefix tailTrace_6212659
  have hstable : (prefixWord ++ tailWord_6212659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212659).length < 2 ^ (prefixWord ++ tailWord_6212659).sum := by decide
  have hdescent : baseEnd_6212659 < baseStart_6212659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212670 : List Nat := [4, 2, 1, 3, 1, 1, 1, 2, 3, 3, 2]
def baseStart_6212670 : Nat := 118140960795 + 6212670 * 2 ^ 59
def prefixEnd_6212670 : Nat := 4983230072969 + 3 ^ 40 * 6212670 * 2
def baseEnd_6212670 : Nat := 3190085857768313133753457

theorem tailTrace_6212670 : CollatzResearch.WordTrace tailWord_6212670 prefixEnd_6212670 3190085857768313133753457 := by
  unfold tailWord_6212670
  simp only [CollatzResearch.WordTrace]
  refine ⟨28324336300320638050929433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151063126935043402938290309 28324336300320638050929433)
  ·
    refine ⟨21243252225240478538197075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28324336300320638050929433 21243252225240478538197075)
    ·
      refine ⟨31864878337860717807295613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21243252225240478538197075 31864878337860717807295613)
      ·
        refine ⟨11949329376697769177735855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31864878337860717807295613 11949329376697769177735855)
        ·
          refine ⟨17923994065046653766603783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11949329376697769177735855 17923994065046653766603783)
          ·
            refine ⟨26885991097569980649905675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17923994065046653766603783 26885991097569980649905675)
            ·
              refine ⟨40328986646354970974858513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26885991097569980649905675 40328986646354970974858513)
              ·
                refine ⟨30246739984766228231143885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40328986646354970974858513 30246739984766228231143885)
                ·
                  refine ⟨11342527494287335586678957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30246739984766228231143885 11342527494287335586678957)
                  ·
                    refine ⟨4253447810357750845004609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11342527494287335586678957 4253447810357750845004609)
                    ·
                      refine ⟨3190085857768313133753457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4253447810357750845004609 3190085857768313133753457)
                      ·
                        rfl

theorem cell23_6212670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_6212670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212670 prefixEnd_6212670 := by exact prefixLift 6212670
  have htrace : WordTrace (prefixWord ++ tailWord_6212670) baseStart_6212670 baseEnd_6212670 := by
    simpa [prefixWord, tailWord_6212670, baseEnd_6212670] using wordTrace_append hprefix tailTrace_6212670
  have hstable : (prefixWord ++ tailWord_6212670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212670).length < 2 ^ (prefixWord ++ tailWord_6212670).sum := by decide
  have hdescent : baseEnd_6212670 < baseStart_6212670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212686 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3]
def baseStart_6212686 : Nat := 118140960795 + 6212686 * 2 ^ 59
def prefixEnd_6212686 : Nat := 4983230072969 + 3 ^ 40 * 6212686 * 2
def baseEnd_6212686 : Nat := 3190094073458785071153383

theorem tailTrace_6212686 : CollatzResearch.WordTrace tailWord_6212686 prefixEnd_6212686 3190094073458785071153383 := by
  unfold tailWord_6212686
  simp only [CollatzResearch.WordTrace]
  refine ⟨28324409246313392392502239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151063515980338092760011941 28324409246313392392502239)
  ·
    refine ⟨42486613869470088588753359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28324409246313392392502239 42486613869470088588753359)
    ·
      refine ⟨63729920804205132883130039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42486613869470088588753359 63729920804205132883130039)
      ·
        refine ⟨95594881206307699324695059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63729920804205132883130039 95594881206307699324695059)
        ·
          refine ⟨143392321809461548987042589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95594881206307699324695059 143392321809461548987042589)
          ·
            refine ⟨53772120678548080870140971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143392321809461548987042589 53772120678548080870140971)
            ·
              refine ⟨80658181017822121305211457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53772120678548080870140971 80658181017822121305211457)
              ·
                refine ⟨60493635763366590978908593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80658181017822121305211457 60493635763366590978908593)
                ·
                  refine ⟨45370226822524943234181445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60493635763366590978908593 45370226822524943234181445)
                  ·
                    refine ⟨8506917529223426856409021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45370226822524943234181445 8506917529223426856409021)
                    ·
                      refine ⟨3190094073458785071153383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8506917529223426856409021 3190094073458785071153383)
                      ·
                        rfl

theorem cell23_6212686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_6212686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212686 prefixEnd_6212686 := by exact prefixLift 6212686
  have htrace : WordTrace (prefixWord ++ tailWord_6212686) baseStart_6212686 baseEnd_6212686 := by
    simpa [prefixWord, tailWord_6212686, baseEnd_6212686] using wordTrace_append hprefix tailTrace_6212686
  have hstable : (prefixWord ++ tailWord_6212686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212686).length < 2 ^ (prefixWord ++ tailWord_6212686).sum := by decide
  have hdescent : baseEnd_6212686 < baseStart_6212686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212689 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 9]
def baseStart_6212689 : Nat := 118140960795 + 6212689 * 2 ^ 59
def prefixEnd_6212689 : Nat := 4983230072969 + 3 ^ 40 * 6212689 * 2
def baseEnd_6212689 : Nat := 354455068211194284379541

theorem tailTrace_6212689 : CollatzResearch.WordTrace tailWord_6212689 prefixEnd_6212689 354455068211194284379541 := by
  unfold tailWord_6212689
  simp only [CollatzResearch.WordTrace]
  refine ⟨226595383389496270652377121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151063588926330847101584747 226595383389496270652377121)
  ·
    refine ⟨169946537542122202989282841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226595383389496270652377121 169946537542122202989282841)
    ·
      refine ⟨127459903156591652241962131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169946537542122202989282841 127459903156591652241962131)
      ·
        refine ⟨191189854734887478362943197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127459903156591652241962131 191189854734887478362943197)
        ·
          refine ⟨71696195525582804386103699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191189854734887478362943197 71696195525582804386103699)
          ·
            refine ⟨107544293288374206579155549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71696195525582804386103699 107544293288374206579155549)
            ·
              refine ⟨40329109983140327467183331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107544293288374206579155549 40329109983140327467183331)
              ·
                refine ⟨60493664974710491200774997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40329109983140327467183331 60493664974710491200774997)
                ·
                  refine ⟨354455068211194284379541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60493664974710491200774997 354455068211194284379541)
                  ·
                    rfl

theorem cell23_6212689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 9].length) (baseStart_6212689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212689 prefixEnd_6212689 := by exact prefixLift 6212689
  have htrace : WordTrace (prefixWord ++ tailWord_6212689) baseStart_6212689 baseEnd_6212689 := by
    simpa [prefixWord, tailWord_6212689, baseEnd_6212689] using wordTrace_append hprefix tailTrace_6212689
  have hstable : (prefixWord ++ tailWord_6212689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212689).length < 2 ^ (prefixWord ++ tailWord_6212689).sum := by decide
  have hdescent : baseEnd_6212689 < baseStart_6212689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212700 : List Nat := [2, 2, 4, 1, 1, 1, 2, 2, 4, 2, 2]
def baseStart_6212700 : Nat := 118140960795 + 6212700 * 2 ^ 59
def prefixEnd_6212700 : Nat := 4983230072969 + 3 ^ 40 * 6212700 * 2
def baseEnd_6212700 : Nat := 3190101262187948016378319

theorem tailTrace_6212700 : CollatzResearch.WordTrace tailWord_6212700 prefixEnd_6212700 3190101262187948016378319 := by
  unfold tailWord_6212700
  simp only [CollatzResearch.WordTrace]
  refine ⟨113297892296228209765513777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151063856394970946354018369 113297892296228209765513777)
  ·
    refine ⟨84973419222171157324135333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113297892296228209765513777 84973419222171157324135333)
    ·
      refine ⟨15932516104157091998275375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84973419222171157324135333 15932516104157091998275375)
      ·
        refine ⟨23898774156235637997413063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15932516104157091998275375 23898774156235637997413063)
        ·
          refine ⟨35848161234353456996119595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23898774156235637997413063 35848161234353456996119595)
          ·
            refine ⟨53772241851530185494179393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35848161234353456996119595 53772241851530185494179393)
            ·
              refine ⟨40329181388647639120634545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53772241851530185494179393 40329181388647639120634545)
              ·
                refine ⟨30246886041485729340475909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40329181388647639120634545 30246886041485729340475909)
                ·
                  refine ⟨5671291132778574251339233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30246886041485729340475909 5671291132778574251339233)
                  ·
                    refine ⟨4253468349583930688504425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5671291132778574251339233 4253468349583930688504425)
                    ·
                      refine ⟨3190101262187948016378319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4253468349583930688504425 3190101262187948016378319)
                      ·
                        rfl

theorem cell23_6212700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_6212700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212700 prefixEnd_6212700 := by exact prefixLift 6212700
  have htrace : WordTrace (prefixWord ++ tailWord_6212700) baseStart_6212700 baseEnd_6212700 := by
    simpa [prefixWord, tailWord_6212700, baseEnd_6212700] using wordTrace_append hprefix tailTrace_6212700
  have hstable : (prefixWord ++ tailWord_6212700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212700).length < 2 ^ (prefixWord ++ tailWord_6212700).sum := by decide
  have hdescent : baseEnd_6212700 < baseStart_6212700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212716 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 3]
def baseStart_6212716 : Nat := 118140960795 + 6212716 * 2 ^ 59
def prefixEnd_6212716 : Nat := 4983230072969 + 3 ^ 40 * 6212716 * 2
def baseEnd_6212716 : Nat := 3190109477878419953778245

theorem tailTrace_6212716 : CollatzResearch.WordTrace tailWord_6212716 prefixEnd_6212716 3190109477878419953778245 := by
  unfold tailWord_6212716
  simp only [CollatzResearch.WordTrace]
  refine ⟨113298184080199227131805001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151064245440265636175740001 113298184080199227131805001)
  ·
    refine ⟨84973638060149420348853751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113298184080199227131805001 84973638060149420348853751)
    ·
      refine ⟨127460457090224130523280627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84973638060149420348853751 127460457090224130523280627)
      ·
        refine ⟨191190685635336195784920941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127460457090224130523280627 191190685635336195784920941)
        ·
          refine ⟨71696507113251073419345353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191190685635336195784920941 71696507113251073419345353)
          ·
            refine ⟨53772380334938305064509015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71696507113251073419345353 53772380334938305064509015)
            ·
              refine ⟨80658570502407457596763523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53772380334938305064509015 80658570502407457596763523)
              ·
                refine ⟨120987855753611186395145285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80658570502407457596763523 120987855753611186395145285)
                ·
                  refine ⟨22685222953802097449089741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120987855753611186395145285 22685222953802097449089741)
                  ·
                    refine ⟨8506958607675786543408653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22685222953802097449089741 8506958607675786543408653)
                    ·
                      refine ⟨3190109477878419953778245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8506958607675786543408653 3190109477878419953778245)
                      ·
                        rfl

theorem cell23_6212716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 3].length) (baseStart_6212716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212716 prefixEnd_6212716 := by exact prefixLift 6212716
  have htrace : WordTrace (prefixWord ++ tailWord_6212716) baseStart_6212716 baseEnd_6212716 := by
    simpa [prefixWord, tailWord_6212716, baseEnd_6212716] using wordTrace_append hprefix tailTrace_6212716
  have hstable : (prefixWord ++ tailWord_6212716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212716).length < 2 ^ (prefixWord ++ tailWord_6212716).sum := by decide
  have hdescent : baseEnd_6212716 < baseStart_6212716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212717 : List Nat := [1, 5, 1, 1, 2, 2, 3, 2, 2, 2, 2]
def baseStart_6212717 : Nat := 118140960795 + 6212717 * 2 ^ 59
def prefixEnd_6212717 : Nat := 4983230072969 + 3 ^ 40 * 6212717 * 2
def baseEnd_6212717 : Nat := 3190109991359074449865741

theorem tailTrace_6212717 : CollatzResearch.WordTrace tailWord_6212717 prefixEnd_6212717 3190109991359074449865741 := by
  unfold tailWord_6212717
  simp only [CollatzResearch.WordTrace]
  refine ⟨226596404633394831434396405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151064269755596554289597603 226596404633394831434396405)
  ·
    refine ⟨21243412934380765446974663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 226596404633394831434396405 21243412934380765446974663)
    ·
      refine ⟨31865119401571148170461995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21243412934380765446974663 31865119401571148170461995)
      ·
        refine ⟨47797679102356722255692993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31865119401571148170461995 47797679102356722255692993)
        ·
          refine ⟨35848259326767541691769745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47797679102356722255692993 35848259326767541691769745)
          ·
            refine ⟨26886194495075656268827309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35848259326767541691769745 26886194495075656268827309)
            ·
              refine ⟨10082322935653371100810241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26886194495075656268827309 10082322935653371100810241)
              ·
                refine ⟨7561742201740028325607681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10082322935653371100810241 7561742201740028325607681)
                ·
                  refine ⟨5671306651305021244205761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7561742201740028325607681 5671306651305021244205761)
                  ·
                    refine ⟨4253479988478765933154321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5671306651305021244205761 4253479988478765933154321)
                    ·
                      refine ⟨3190109991359074449865741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4253479988478765933154321 3190109991359074449865741)
                      ·
                        rfl

theorem cell23_6212717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_6212717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212717 prefixEnd_6212717 := by exact prefixLift 6212717
  have htrace : WordTrace (prefixWord ++ tailWord_6212717) baseStart_6212717 baseEnd_6212717 := by
    simpa [prefixWord, tailWord_6212717, baseEnd_6212717] using wordTrace_append hprefix tailTrace_6212717
  have hstable : (prefixWord ++ tailWord_6212717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212717).length < 2 ^ (prefixWord ++ tailWord_6212717).sum := by decide
  have hdescent : baseEnd_6212717 < baseStart_6212717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212770 : List Nat := [3, 3, 1, 3, 2, 1, 1, 2, 2, 5]
def baseStart_6212770 : Nat := 118140960795 + 6212770 * 2 ^ 59
def prefixEnd_6212770 : Nat := 4983230072969 + 3 ^ 40 * 6212770 * 2
def baseEnd_6212770 : Nat := 1063379068611254247500999

theorem tailTrace_6212770 : CollatzResearch.WordTrace tailWord_6212770 prefixEnd_6212770 1063379068611254247500999 := by
  unfold tailWord_6212770
  simp only [CollatzResearch.WordTrace]
  refine ⟨56649584425550705371518941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151065558468135214324050509 56649584425550705371518941)
  ·
    refine ⟨21243594159581514514319603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56649584425550705371518941 21243594159581514514319603)
    ·
      refine ⟨31865391239372271771479405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21243594159581514514319603 31865391239372271771479405)
      ·
        refine ⟨11949521714764601914304777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31865391239372271771479405 11949521714764601914304777)
        ·
          refine ⟨8962141286073451435728583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11949521714764601914304777 8962141286073451435728583)
          ·
            refine ⟨13443211929110177153592875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8962141286073451435728583 13443211929110177153592875)
            ·
              refine ⟨20164817893665265730389313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13443211929110177153592875 20164817893665265730389313)
              ·
                refine ⟨15123613420248949297791985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20164817893665265730389313 15123613420248949297791985)
                ·
                  refine ⟨11342710065186711973343989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15123613420248949297791985 11342710065186711973343989)
                  ·
                    refine ⟨1063379068611254247500999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11342710065186711973343989 1063379068611254247500999)
                    ·
                      rfl

theorem cell23_6212770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_6212770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212770 prefixEnd_6212770 := by exact prefixLift 6212770
  have htrace : WordTrace (prefixWord ++ tailWord_6212770) baseStart_6212770 baseEnd_6212770 := by
    simpa [prefixWord, tailWord_6212770, baseEnd_6212770] using wordTrace_append hprefix tailTrace_6212770
  have hstable : (prefixWord ++ tailWord_6212770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212770).length < 2 ^ (prefixWord ++ tailWord_6212770).sum := by decide
  have hdescent : baseEnd_6212770 < baseStart_6212770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212773 : List Nat := [1, 3, 1, 2, 1, 5, 1, 2, 2, 1, 4]
def baseStart_6212773 : Nat := 118140960795 + 6212773 * 2 ^ 59
def prefixEnd_6212773 : Nat := 4983230072969 + 3 ^ 40 * 6212773 * 2
def baseEnd_6212773 : Nat := 3190138746275726230765483

theorem tailTrace_6212773 : CollatzResearch.WordTrace tailWord_6212773 prefixEnd_6212773 3190138746275726230765483 := by
  unfold tailWord_6212773
  simp only [CollatzResearch.WordTrace]
  refine ⟨226598447121191952998434973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151065631414127968665623315 226598447121191952998434973)
  ·
    refine ⟨84974417670446982374413115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226598447121191952998434973 84974417670446982374413115)
    ·
      refine ⟨127461626505670473561619673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84974417670446982374413115 127461626505670473561619673)
      ·
        refine ⟨95596219879252855171214755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127461626505670473561619673 95596219879252855171214755)
        ·
          refine ⟨143394329818879282756822133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95596219879252855171214755 143394329818879282756822133)
          ·
            refine ⟨13443218420519932758452075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 143394329818879282756822133 13443218420519932758452075)
            ·
              refine ⟨20164827630779899137678113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13443218420519932758452075 20164827630779899137678113)
              ·
                refine ⟨15123620723084924353258585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20164827630779899137678113 15123620723084924353258585)
                ·
                  refine ⟨11342715542313693264943939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15123620723084924353258585 11342715542313693264943939)
                  ·
                    refine ⟨17014073313470539897415909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11342715542313693264943939 17014073313470539897415909)
                    ·
                      refine ⟨3190138746275726230765483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17014073313470539897415909 3190138746275726230765483)
                      ·
                        rfl

theorem cell23_6212773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_6212773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212773 prefixEnd_6212773 := by exact prefixLift 6212773
  have htrace : WordTrace (prefixWord ++ tailWord_6212773) baseStart_6212773 baseEnd_6212773 := by
    simpa [prefixWord, tailWord_6212773, baseEnd_6212773] using wordTrace_append hprefix tailTrace_6212773
  have hstable : (prefixWord ++ tailWord_6212773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212773).length < 2 ^ (prefixWord ++ tailWord_6212773).sum := by decide
  have hdescent : baseEnd_6212773 < baseStart_6212773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212783 : List Nat := [1, 1, 2, 1, 2, 3, 5, 1, 3, 4]
def baseStart_6212783 : Nat := 118140960795 + 6212783 * 2 ^ 59
def prefixEnd_6212783 : Nat := 4983230072969 + 3 ^ 40 * 6212783 * 2
def baseEnd_6212783 : Nat := 1063381293694090397213479

theorem tailTrace_6212783 : CollatzResearch.WordTrace tailWord_6212783 prefixEnd_6212783 1063381293694090397213479 := by
  unfold tailWord_6212783
  simp only [CollatzResearch.WordTrace]
  refine ⟨226598811851155724706299003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151065874567437149804199335 226598811851155724706299003)
  ·
    refine ⟨339898217776733587059448505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226598811851155724706299003 339898217776733587059448505)
    ·
      refine ⟨254923663332550190294586379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339898217776733587059448505 254923663332550190294586379)
      ·
        refine ⟨382385494998825285441879569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254923663332550190294586379 382385494998825285441879569)
        ·
          refine ⟨286789121249118964081409677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382385494998825285441879569 286789121249118964081409677)
          ·
            refine ⟨107545920468419611530528629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286789121249118964081409677 107545920468419611530528629)
            ·
              refine ⟨10082430043914338580987059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107545920468419611530528629 10082430043914338580987059)
              ·
                refine ⟨15123645065871507871480589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10082430043914338580987059 15123645065871507871480589)
                ·
                  refine ⟨5671366899701815451805221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15123645065871507871480589 5671366899701815451805221)
                  ·
                    refine ⟨1063381293694090397213479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5671366899701815451805221 1063381293694090397213479)
                    ·
                      rfl

theorem cell23_6212783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3, 4].length) (baseStart_6212783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212783 prefixEnd_6212783 := by exact prefixLift 6212783
  have htrace : WordTrace (prefixWord ++ tailWord_6212783) baseStart_6212783 baseEnd_6212783 := by
    simpa [prefixWord, tailWord_6212783, baseEnd_6212783] using wordTrace_append hprefix tailTrace_6212783
  have hstable : (prefixWord ++ tailWord_6212783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212783).length < 2 ^ (prefixWord ++ tailWord_6212783).sum := by decide
  have hdescent : baseEnd_6212783 < baseStart_6212783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212810 : List Nat := [3, 1, 2, 1, 3, 3, 2, 1, 2, 2, 3]
def baseStart_6212810 : Nat := 118140960795 + 6212810 * 2 ^ 59
def prefixEnd_6212810 : Nat := 4983230072969 + 3 ^ 40 * 6212810 * 2
def baseEnd_6212810 : Nat := 3190157745059942586002813

theorem tailTrace_6212810 : CollatzResearch.WordTrace tailWord_6212810 prefixEnd_6212810 3190157745059942586002813 := by
  unfold tailWord_6212810
  simp only [CollatzResearch.WordTrace]
  refine ⟨56649949155514477079382971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151066531081371938878354589 56649949155514477079382971)
  ·
    refine ⟨84974923733271715619074457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56649949155514477079382971 84974923733271715619074457)
    ·
      refine ⟨63731192799953786714305843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84974923733271715619074457 63731192799953786714305843)
      ·
        refine ⟨95596789199930680071458765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63731192799953786714305843 95596789199930680071458765)
        ·
          refine ⟨35848795949974005026797037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95596789199930680071458765 35848795949974005026797037)
          ·
            refine ⟨13443298481240251885048889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35848795949974005026797037 13443298481240251885048889)
            ·
              refine ⟨10082473860930188913786667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13443298481240251885048889 10082473860930188913786667)
              ·
                refine ⟨15123710791395283370680001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10082473860930188913786667 15123710791395283370680001)
                ·
                  refine ⟨11342783093546462528010001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15123710791395283370680001 11342783093546462528010001)
                  ·
                    refine ⟨8507087320159846896007501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11342783093546462528010001 8507087320159846896007501)
                    ·
                      refine ⟨3190157745059942586002813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8507087320159846896007501 3190157745059942586002813)
                      ·
                        rfl

theorem cell23_6212810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_6212810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212810 prefixEnd_6212810 := by exact prefixLift 6212810
  have htrace : WordTrace (prefixWord ++ tailWord_6212810) baseStart_6212810 baseEnd_6212810 := by
    simpa [prefixWord, tailWord_6212810, baseEnd_6212810] using wordTrace_append hprefix tailTrace_6212810
  have hstable : (prefixWord ++ tailWord_6212810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212810).length < 2 ^ (prefixWord ++ tailWord_6212810).sum := by decide
  have hdescent : baseEnd_6212810 < baseStart_6212810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212840 : List Nat := [2, 1, 4, 1, 2, 1, 2, 3, 3, 1, 3]
def baseStart_6212840 : Nat := 118140960795 + 6212840 * 2 ^ 59
def prefixEnd_6212840 : Nat := 4983230072969 + 3 ^ 40 * 6212840 * 2
def baseEnd_6212840 : Nat := 3190173149479577468627675

theorem tailTrace_6212840 : CollatzResearch.WordTrace tailWord_6212840 prefixEnd_6212840 3190173149479577468627675 := by
  unfold tailWord_6212840
  simp only [CollatzResearch.WordTrace]
  refine ⟨113300445405974611720561987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151067260541299482294082649 113300445405974611720561987)
  ·
    refine ⟨169950668108961917580842981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113300445405974611720561987 169950668108961917580842981)
    ·
      refine ⟨31865750270430359546408059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169950668108961917580842981 31865750270430359546408059)
      ·
        refine ⟨47798625405645539319612089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31865750270430359546408059 47798625405645539319612089)
        ·
          refine ⟨35848969054234154489709067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47798625405645539319612089 35848969054234154489709067)
          ·
            refine ⟨53773453581351231734563601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35848969054234154489709067 53773453581351231734563601)
            ·
              refine ⟨40330090186013423800922701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53773453581351231734563601 40330090186013423800922701)
              ·
                refine ⟨15123783819755033925346013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40330090186013423800922701 15123783819755033925346013)
                ·
                  refine ⟨5671418932408137722004755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15123783819755033925346013 5671418932408137722004755)
                  ·
                    refine ⟨8507128398612206583007133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5671418932408137722004755 8507128398612206583007133)
                    ·
                      refine ⟨3190173149479577468627675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8507128398612206583007133 3190173149479577468627675)
                      ·
                        rfl

theorem cell23_6212840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_6212840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212840 prefixEnd_6212840 := by exact prefixLift 6212840
  have htrace : WordTrace (prefixWord ++ tailWord_6212840) baseStart_6212840 baseEnd_6212840 := by
    simpa [prefixWord, tailWord_6212840, baseEnd_6212840] using wordTrace_append hprefix tailTrace_6212840
  have hstable : (prefixWord ++ tailWord_6212840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212840).length < 2 ^ (prefixWord ++ tailWord_6212840).sum := by decide
  have hdescent : baseEnd_6212840 < baseStart_6212840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212863 : List Nat := [1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 4]
def baseStart_6212863 : Nat := 118140960795 + 6212863 * 2 ^ 59
def prefixEnd_6212863 : Nat := 4983230072969 + 3 ^ 40 * 6212863 * 2
def baseEnd_6212863 : Nat := 3190184959534630878640069

theorem tailTrace_6212863 : CollatzResearch.WordTrace tailWord_6212863 prefixEnd_6212863 3190184959534630878640069 := by
  unfold tailWord_6212863
  simp only [CollatzResearch.WordTrace]
  refine ⟨226601729690865898369211243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151067819793910598912807495 226601729690865898369211243)
  ·
    refine ⟨339902594536298847553816865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226601729690865898369211243 339902594536298847553816865)
    ·
      refine ⟨254926945902224135665362649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339902594536298847553816865 254926945902224135665362649)
      ·
        refine ⟨191195209426668101749021987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254926945902224135665362649 191195209426668101749021987)
        ·
          refine ⟨286792814140002152623532981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191195209426668101749021987 286792814140002152623532981)
          ·
            refine ⟨26886826325625201808456217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 286792814140002152623532981 26886826325625201808456217)
            ·
              refine ⟨20165119744218901356342163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26886826325625201808456217 20165119744218901356342163)
              ·
                refine ⟨30247679616328352034513245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20165119744218901356342163 30247679616328352034513245)
                ·
                  refine ⟨11342879856123132012942467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30247679616328352034513245 11342879856123132012942467)
                  ·
                    refine ⟨17014319784184698019413701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11342879856123132012942467 17014319784184698019413701)
                    ·
                      refine ⟨3190184959534630878640069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17014319784184698019413701 3190184959534630878640069)
                      ·
                        rfl

theorem cell23_6212863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_6212863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212863 prefixEnd_6212863 := by exact prefixLift 6212863
  have htrace : WordTrace (prefixWord ++ tailWord_6212863) baseStart_6212863 baseEnd_6212863 := by
    simpa [prefixWord, tailWord_6212863, baseEnd_6212863] using wordTrace_append hprefix tailTrace_6212863
  have hstable : (prefixWord ++ tailWord_6212863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212863).length < 2 ^ (prefixWord ++ tailWord_6212863).sum := by decide
  have hdescent : baseEnd_6212863 < baseStart_6212863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212867 : List Nat := [1, 1, 1, 3, 2, 6, 1, 1, 2, 3, 2]
def baseStart_6212867 : Nat := 118140960795 + 6212867 * 2 ^ 59
def prefixEnd_6212867 : Nat := 4983230072969 + 3 ^ 40 * 6212867 * 2
def baseEnd_6212867 : Nat := 3190187013457248862990051

theorem tailTrace_6212867 : CollatzResearch.WordTrace tailWord_6212867 prefixEnd_6212867 3190187013457248862990051 := by
  unfold tailWord_6212867
  simp only [CollatzResearch.WordTrace]
  refine ⟨226601875582851407052356855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151067917055234271368237903 226601875582851407052356855)
  ·
    refine ⟨339902813374277110578535283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226601875582851407052356855 339902813374277110578535283)
    ·
      refine ⟨509854220061415665867802925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339902813374277110578535283 509854220061415665867802925)
      ·
        refine ⟨191195332523030874700426097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 509854220061415665867802925 191195332523030874700426097)
        ·
          refine ⟨143396499392273156025319573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191195332523030874700426097 143396499392273156025319573)
          ·
            refine ⟨6721710909012804188686855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 143396499392273156025319573 6721710909012804188686855)
            ·
              refine ⟨10082566363519206283030283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6721710909012804188686855 10082566363519206283030283)
              ·
                refine ⟨15123849545278809424545425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10082566363519206283030283 15123849545278809424545425)
                ·
                  refine ⟨11342887158959107068409069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15123849545278809424545425 11342887158959107068409069)
                  ·
                    refine ⟨4253582684609665150653401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11342887158959107068409069 4253582684609665150653401)
                    ·
                      refine ⟨3190187013457248862990051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4253582684609665150653401 3190187013457248862990051)
                      ·
                        rfl

theorem cell23_6212867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 3, 2].length) (baseStart_6212867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212867 prefixEnd_6212867 := by exact prefixLift 6212867
  have htrace : WordTrace (prefixWord ++ tailWord_6212867) baseStart_6212867 baseEnd_6212867 := by
    simpa [prefixWord, tailWord_6212867, baseEnd_6212867] using wordTrace_append hprefix tailTrace_6212867
  have hstable : (prefixWord ++ tailWord_6212867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212867).length < 2 ^ (prefixWord ++ tailWord_6212867).sum := by decide
  have hdescent : baseEnd_6212867 < baseStart_6212867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212873 : List Nat := [1, 2, 1, 1, 3, 3, 2, 2, 4, 4]
def baseStart_6212873 : Nat := 118140960795 + 6212873 * 2 ^ 59
def prefixEnd_6212873 : Nat := 4983230072969 + 3 ^ 40 * 6212873 * 2
def baseEnd_6212873 : Nat := 1063396698113725279838341

theorem tailTrace_6212873 : CollatzResearch.WordTrace tailWord_6212873 prefixEnd_6212873 1063396698113725279838341 := by
  unfold tailWord_6212873
  simp only [CollatzResearch.WordTrace]
  refine ⟨226602094420829670077075273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151068062947219780051383515 226602094420829670077075273)
  ·
    refine ⟨169951570815622252557806455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226602094420829670077075273 169951570815622252557806455)
    ·
      refine ⟨254927356223433378836709683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169951570815622252557806455 254927356223433378836709683)
      ·
        refine ⟨382391034335150068255064525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254927356223433378836709683 382391034335150068255064525)
        ·
          refine ⟨143396637875681275595649197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 382391034335150068255064525 143396637875681275595649197)
          ·
            refine ⟨53773739203380478348368449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143396637875681275595649197 53773739203380478348368449)
            ·
              refine ⟨40330304402535358761276337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53773739203380478348368449 40330304402535358761276337)
              ·
                refine ⟨30247728301901519070957253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40330304402535358761276337 30247728301901519070957253)
                ·
                  refine ⟨5671449056606534825804485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30247728301901519070957253 5671449056606534825804485)
                  ·
                    refine ⟨1063396698113725279838341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5671449056606534825804485 1063396698113725279838341)
                    ·
                      rfl

theorem cell23_6212873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4, 4].length) (baseStart_6212873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212873 prefixEnd_6212873 := by exact prefixLift 6212873
  have htrace : WordTrace (prefixWord ++ tailWord_6212873) baseStart_6212873 baseEnd_6212873 := by
    simpa [prefixWord, tailWord_6212873, baseEnd_6212873] using wordTrace_append hprefix tailTrace_6212873
  have hstable : (prefixWord ++ tailWord_6212873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212873).length < 2 ^ (prefixWord ++ tailWord_6212873).sum := by decide
  have hdescent : baseEnd_6212873 < baseStart_6212873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212890 : List Nat := [3, 1, 1, 3, 3, 2, 1, 1, 4, 4]
def baseStart_6212890 : Nat := 118140960795 + 6212890 * 2 ^ 59
def prefixEnd_6212890 : Nat := 4983230072969 + 3 ^ 40 * 6212890 * 2
def baseEnd_6212890 : Nat := 1063399607837434091000815

theorem tailTrace_6212890 : CollatzResearch.WordTrace tailWord_6212890 prefixEnd_6212890 1063399607837434091000815 := by
  unfold tailWord_6212890
  simp only [CollatzResearch.WordTrace]
  refine ⟨56650678615442020495111031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151068476307845387986962749 56650678615442020495111031)
  ·
    refine ⟨84976017923163030742666547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56650678615442020495111031 84976017923163030742666547)
    ·
      refine ⟨127464026884744546113999821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84976017923163030742666547 127464026884744546113999821)
      ·
        refine ⟨47799010081779204792749933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127464026884744546113999821 47799010081779204792749933)
        ·
          refine ⟨17924628780667201797281225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47799010081779204792749933 17924628780667201797281225)
          ·
            refine ⟨13443471585500401347960919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17924628780667201797281225 13443471585500401347960919)
            ·
              refine ⟨20165207378250602021941379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13443471585500401347960919 20165207378250602021941379)
              ·
                refine ⟨30247811067375903032912069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20165207378250602021941379 30247811067375903032912069)
                ·
                  refine ⟨5671464575132981818671013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30247811067375903032912069 5671464575132981818671013)
                  ·
                    refine ⟨1063399607837434091000815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5671464575132981818671013 1063399607837434091000815)
                    ·
                      rfl

theorem cell23_6212890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 4, 4].length) (baseStart_6212890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212890 prefixEnd_6212890 := by exact prefixLift 6212890
  have htrace : WordTrace (prefixWord ++ tailWord_6212890) baseStart_6212890 baseEnd_6212890 := by
    simpa [prefixWord, tailWord_6212890, baseEnd_6212890] using wordTrace_append hprefix tailTrace_6212890
  have hstable : (prefixWord ++ tailWord_6212890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212890).length < 2 ^ (prefixWord ++ tailWord_6212890).sum := by decide
  have hdescent : baseEnd_6212890 < baseStart_6212890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212917 : List Nat := [1, 3, 3, 1, 2, 3, 2, 2, 1, 2, 3]
def baseStart_6212917 : Nat := 118140960795 + 6212917 * 2 ^ 59
def prefixEnd_6212917 : Nat := 4983230072969 + 3 ^ 40 * 6212917 * 2
def baseEnd_6212917 : Nat := 3190212687489973667364821

theorem tailTrace_6212917 : CollatzResearch.WordTrace tailWord_6212917 prefixEnd_6212917 3190212687489973667364821 := by
  unfold tailWord_6212917
  simp only [CollatzResearch.WordTrace]
  refine ⟨226603699232670265591677005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151069132821780177061118003 226603699232670265591677005)
  ·
    refine ⟨84976387212251349596878877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226603699232670265591677005 84976387212251349596878877)
    ·
      refine ⟨31866145204594256098829579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84976387212251349596878877 31866145204594256098829579)
      ·
        refine ⟨47799217806891384148244369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31866145204594256098829579 47799217806891384148244369)
        ·
          refine ⟨35849413355168538111183277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47799217806891384148244369 35849413355168538111183277)
          ·
            refine ⟨13443530008188201791693729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35849413355168538111183277 13443530008188201791693729)
            ·
              refine ⟨10082647506141151343770297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13443530008188201791693729 10082647506141151343770297)
              ·
                refine ⟨7561985629605863507827723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10082647506141151343770297 7561985629605863507827723)
                ·
                  refine ⟨11342978444408795261741585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7561985629605863507827723 11342978444408795261741585)
                  ·
                    refine ⟨8507233833306596446306189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11342978444408795261741585 8507233833306596446306189)
                    ·
                      refine ⟨3190212687489973667364821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8507233833306596446306189 3190212687489973667364821)
                      ·
                        rfl

theorem cell23_6212917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_6212917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212917 prefixEnd_6212917 := by exact prefixLift 6212917
  have htrace : WordTrace (prefixWord ++ tailWord_6212917) baseStart_6212917 baseEnd_6212917 := by
    simpa [prefixWord, tailWord_6212917, baseEnd_6212917] using wordTrace_append hprefix tailTrace_6212917
  have hstable : (prefixWord ++ tailWord_6212917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212917).length < 2 ^ (prefixWord ++ tailWord_6212917).sum := by decide
  have hdescent : baseEnd_6212917 < baseStart_6212917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6212964 : List Nat := [2, 3, 1, 1, 3, 2, 4, 1, 2, 1, 3]
def baseStart_6212964 : Nat := 118140960795 + 6212964 * 2 ^ 59
def prefixEnd_6212964 : Nat := 4983230072969 + 3 ^ 40 * 6212964 * 2
def baseEnd_6212964 : Nat := 3190236821080734983477105

theorem tailTrace_6212964 : CollatzResearch.WordTrace tailWord_6212964 prefixEnd_6212964 3190236821080734983477105 := by
  unfold tailWord_6212964
  simp only [CollatzResearch.WordTrace]
  refine ⟨113302706731749996309318973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151070275642333328412425297 113302706731749996309318973)
  ·
    refine ⟨42488515024406248615994615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113302706731749996309318973 42488515024406248615994615)
    ·
      refine ⟨63732772536609372923991923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42488515024406248615994615 63732772536609372923991923)
      ·
        refine ⟨95599158804914059385987885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63732772536609372923991923 95599158804914059385987885)
        ·
          refine ⟨35849684551842772269745457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95599158804914059385987885 35849684551842772269745457)
          ·
            refine ⟨26887263413882079202309093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35849684551842772269745457 26887263413882079202309093)
            ·
              refine ⟨5041361890102889850432955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26887263413882079202309093 5041361890102889850432955)
              ·
                refine ⟨7562042835154334775649433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5041361890102889850432955 7562042835154334775649433)
                ·
                  refine ⟨5671532126365751081737075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7562042835154334775649433 5671532126365751081737075)
                  ·
                    refine ⟨8507298189548626622605613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5671532126365751081737075 8507298189548626622605613)
                    ·
                      refine ⟨3190236821080734983477105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8507298189548626622605613 3190236821080734983477105)
                      ·
                        rfl

theorem cell23_6212964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 2, 1, 3].length) (baseStart_6212964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6212964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6212964 prefixEnd_6212964 := by exact prefixLift 6212964
  have htrace : WordTrace (prefixWord ++ tailWord_6212964) baseStart_6212964 baseEnd_6212964 := by
    simpa [prefixWord, tailWord_6212964, baseEnd_6212964] using wordTrace_append hprefix tailTrace_6212964
  have hstable : (prefixWord ++ tailWord_6212964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6212964).length < 2 ^ (prefixWord ++ tailWord_6212964).sum := by decide
  have hdescent : baseEnd_6212964 < baseStart_6212964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6212964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213004 : List Nat := [2, 2, 1, 2, 1, 3, 4, 2, 2, 2, 2]
def baseStart_6213004 : Nat := 118140960795 + 6213004 * 2 ^ 59
def prefixEnd_6213004 : Nat := 4983230072969 + 3 ^ 40 * 6213004 * 2
def baseEnd_6213004 : Nat := 3190257360306914826976921

theorem tailTrace_6213004 : CollatzResearch.WordTrace tailWord_6213004 prefixEnd_6213004 3190257360306914826976921 := by
  unfold tailWord_6213004
  simp only [CollatzResearch.WordTrace]
  refine ⟨113303436191677539725047033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151071248255570052966729377 113303436191677539725047033)
  ·
    refine ⟨84977577143758154793785275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113303436191677539725047033 84977577143758154793785275)
    ·
      refine ⟨127466365715637232190677913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84977577143758154793785275 127466365715637232190677913)
      ·
        refine ⟨95599774286727924143008435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127466365715637232190677913 95599774286727924143008435)
        ·
          refine ⟨143399661430091886214512653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95599774286727924143008435 143399661430091886214512653)
          ·
            refine ⟨53774873036284457330442245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143399661430091886214512653 53774873036284457330442245)
            ·
              refine ⟨10082788694303335749457921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53774873036284457330442245 10082788694303335749457921)
              ·
                refine ⟨7562091520727501812093441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10082788694303335749457921 7562091520727501812093441)
                ·
                  refine ⟨5671568640545626359070081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7562091520727501812093441 5671568640545626359070081)
                  ·
                    refine ⟨4253676480409219769302561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5671568640545626359070081 4253676480409219769302561)
                    ·
                      refine ⟨3190257360306914826976921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4253676480409219769302561 3190257360306914826976921)
                      ·
                        rfl

theorem cell23_6213004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 2, 2, 2].length) (baseStart_6213004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213004 prefixEnd_6213004 := by exact prefixLift 6213004
  have htrace : WordTrace (prefixWord ++ tailWord_6213004) baseStart_6213004 baseEnd_6213004 := by
    simpa [prefixWord, tailWord_6213004, baseEnd_6213004] using wordTrace_append hprefix tailTrace_6213004
  have hstable : (prefixWord ++ tailWord_6213004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213004).length < 2 ^ (prefixWord ++ tailWord_6213004).sum := by decide
  have hdescent : baseEnd_6213004 < baseStart_6213004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213077 : List Nat := [1, 3, 2, 3, 1, 1, 1, 3, 2, 4, 2]
def baseStart_6213077 : Nat := 118140960795 + 6213077 * 2 ^ 59
def prefixEnd_6213077 : Nat := 4983230072969 + 3 ^ 40 * 6213077 * 2
def baseEnd_6213077 : Nat := 3190294844394693041364085

theorem tailTrace_6213077 : CollatzResearch.WordTrace tailWord_6213077 prefixEnd_6213077 3190294844394693041364085 := by
  unfold tailWord_6213077
  simp only [CollatzResearch.WordTrace]
  refine ⟨226609534912090612917501485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151073023274727075278334323 226609534912090612917501485)
  ·
    refine ⟨84978575592033979844063057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226609534912090612917501485 84978575592033979844063057)
    ·
      refine ⟨63733931694025484883047293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84978575592033979844063057 63733931694025484883047293)
      ·
        refine ⟨23900224385259556831142735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63733931694025484883047293 23900224385259556831142735)
        ·
          refine ⟨35850336577889335246714103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23900224385259556831142735 35850336577889335246714103)
          ·
            refine ⟨53775504866834002870071155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35850336577889335246714103 53775504866834002870071155)
            ·
              refine ⟨80663257300251004305106733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53775504866834002870071155 80663257300251004305106733)
              ·
                refine ⟨30248721487594126614415025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80663257300251004305106733 30248721487594126614415025)
                ·
                  refine ⟨22686541115695594960811269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30248721487594126614415025 22686541115695594960811269)
                  ·
                    refine ⟨4253726459192924055152113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22686541115695594960811269 4253726459192924055152113)
                    ·
                      refine ⟨3190294844394693041364085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4253726459192924055152113 3190294844394693041364085)
                      ·
                        rfl

theorem cell23_6213077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_6213077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213077 prefixEnd_6213077 := by exact prefixLift 6213077
  have htrace : WordTrace (prefixWord ++ tailWord_6213077) baseStart_6213077 baseEnd_6213077 := by
    simpa [prefixWord, tailWord_6213077, baseEnd_6213077] using wordTrace_append hprefix tailTrace_6213077
  have hstable : (prefixWord ++ tailWord_6213077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213077).length < 2 ^ (prefixWord ++ tailWord_6213077).sum := by decide
  have hdescent : baseEnd_6213077 < baseStart_6213077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213080 : List Nat := [2, 1, 2, 2, 2, 1, 3, 2, 1, 4, 3]
def baseStart_6213080 : Nat := 118140960795 + 6213080 * 2 ^ 59
def prefixEnd_6213080 : Nat := 4983230072969 + 3 ^ 40 * 6213080 * 2
def baseEnd_6213080 : Nat := 3190296384836656529626571

theorem tailTrace_6213080 : CollatzResearch.WordTrace tailWord_6213080 prefixEnd_6213080 3190296384836656529626571 := by
  unfold tailWord_6213080
  simp only [CollatzResearch.WordTrace]
  refine ⟨113304822165539872214930347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151073096220719829619907129 113304822165539872214930347)
  ·
    refine ⟨169957233248309808322395521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113304822165539872214930347 169957233248309808322395521)
    ·
      refine ⟨127467924936232356241796641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169957233248309808322395521 127467924936232356241796641)
      ·
        refine ⟨95600943702174267181347481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127467924936232356241796641 95600943702174267181347481)
        ·
          refine ⟨71700707776630700386010611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95600943702174267181347481 71700707776630700386010611)
          ·
            refine ⟨107551061664946050579015917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71700707776630700386010611 107551061664946050579015917)
            ·
              refine ⟨40331648124354768967130969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107551061664946050579015917 40331648124354768967130969)
              ·
                refine ⟨30248736093266076725348227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40331648124354768967130969 30248736093266076725348227)
                ·
                  refine ⟨45373104139899115088022341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30248736093266076725348227 45373104139899115088022341)
                  ·
                    refine ⟨8507457026231084079004189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45373104139899115088022341 8507457026231084079004189)
                    ·
                      refine ⟨3190296384836656529626571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8507457026231084079004189 3190296384836656529626571)
                      ·
                        rfl

theorem cell23_6213080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_6213080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213080 prefixEnd_6213080 := by exact prefixLift 6213080
  have htrace : WordTrace (prefixWord ++ tailWord_6213080) baseStart_6213080 baseEnd_6213080 := by
    simpa [prefixWord, tailWord_6213080, baseEnd_6213080] using wordTrace_append hprefix tailTrace_6213080
  have hstable : (prefixWord ++ tailWord_6213080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213080).length < 2 ^ (prefixWord ++ tailWord_6213080).sum := by decide
  have hdescent : baseEnd_6213080 < baseStart_6213080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213104 : List Nat := [2, 1, 1, 1, 3, 4, 3, 3, 1, 4]
def baseStart_6213104 : Nat := 118140960795 + 6213104 * 2 ^ 59
def prefixEnd_6213104 : Nat := 4983230072969 + 3 ^ 40 * 6213104 * 2
def baseEnd_6213104 : Nat := 1063436236124121478575487

theorem tailTrace_6213104 : CollatzResearch.WordTrace tailWord_6213104 prefixEnd_6213104 1063436236124121478575487 := by
  unfold tailWord_6213104
  simp only [CollatzResearch.WordTrace]
  refine ⟨113305259841496398264367183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151073679788661864352489577 113305259841496398264367183)
  ·
    refine ⟨169957889762244597396550775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113305259841496398264367183 169957889762244597396550775)
    ·
      refine ⟨254936834643366896094826163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169957889762244597396550775 254936834643366896094826163)
      ·
        refine ⟨382405251965050344142239245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254936834643366896094826163 382405251965050344142239245)
        ·
          refine ⟨143401969486893879053339717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 382405251965050344142239245 143401969486893879053339717)
          ·
            refine ⟨26887869278792602322501197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143401969486893879053339717 26887869278792602322501197)
            ·
              refine ⟨10082950979547225870937949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26887869278792602322501197 10082950979547225870937949)
              ·
                refine ⟨3781106617330209701601731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10082950979547225870937949 3781106617330209701601731)
                ·
                  refine ⟨5671659925995314552402597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3781106617330209701601731 5671659925995314552402597)
                  ·
                    refine ⟨1063436236124121478575487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5671659925995314552402597 1063436236124121478575487)
                    ·
                      rfl

theorem cell23_6213104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3, 1, 4].length) (baseStart_6213104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213104 prefixEnd_6213104 := by exact prefixLift 6213104
  have htrace : WordTrace (prefixWord ++ tailWord_6213104) baseStart_6213104 baseEnd_6213104 := by
    simpa [prefixWord, tailWord_6213104, baseEnd_6213104] using wordTrace_append hprefix tailTrace_6213104
  have hstable : (prefixWord ++ tailWord_6213104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213104).length < 2 ^ (prefixWord ++ tailWord_6213104).sum := by decide
  have hdescent : baseEnd_6213104 < baseStart_6213104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213121 : List Nat := [1, 2, 4, 1, 5, 1, 1, 1, 3, 4]
def baseStart_6213121 : Nat := 118140960795 + 6213121 * 2 ^ 59
def prefixEnd_6213121 : Nat := 4983230072969 + 3 ^ 40 * 6213121 * 2
def baseEnd_6213121 : Nat := 1063439145847830289737961

theorem tailTrace_6213121 : CollatzResearch.WordTrace tailWord_6213121 prefixEnd_6213121 1063439145847830289737961 := by
  unfold tailWord_6213121
  simp only [CollatzResearch.WordTrace]
  refine ⟨226611139723931208432103217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151074093149287472288068811 226611139723931208432103217)
  ·
    refine ⟨169958354792948406324077413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226611139723931208432103217 169958354792948406324077413)
    ·
      refine ⟨31867191523677826185764515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169958354792948406324077413 31867191523677826185764515)
      ·
        refine ⟨47800787285516739278646773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31867191523677826185764515 47800787285516739278646773)
        ·
          refine ⟨4481323808017194307373135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47800787285516739278646773 4481323808017194307373135)
          ·
            refine ⟨6721985712025791461059703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4481323808017194307373135 6721985712025791461059703)
            ·
              refine ⟨10082978568038687191589555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6721985712025791461059703 10082978568038687191589555)
              ·
                refine ⟨15124467852058030787384333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10082978568038687191589555 15124467852058030787384333)
                ·
                  refine ⟨5671675444521761545269125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15124467852058030787384333 5671675444521761545269125)
                  ·
                    refine ⟨1063439145847830289737961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5671675444521761545269125 1063439145847830289737961)
                    ·
                      rfl

theorem cell23_6213121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_6213121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213121 prefixEnd_6213121 := by exact prefixLift 6213121
  have htrace : WordTrace (prefixWord ++ tailWord_6213121) baseStart_6213121 baseEnd_6213121 := by
    simpa [prefixWord, tailWord_6213121, baseEnd_6213121] using wordTrace_append hprefix tailTrace_6213121
  have hstable : (prefixWord ++ tailWord_6213121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213121).length < 2 ^ (prefixWord ++ tailWord_6213121).sum := by decide
  have hdescent : baseEnd_6213121 < baseStart_6213121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213137 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 4, 3, 2]
def baseStart_6213137 : Nat := 118140960795 + 6213137 * 2 ^ 59
def prefixEnd_6213137 : Nat := 4983230072969 + 3 ^ 40 * 6213137 * 2
def baseEnd_6213137 : Nat := 3190325653233962806613809

theorem tailTrace_6213137 : CollatzResearch.WordTrace tailWord_6213137 prefixEnd_6213137 3190325653233962806613809 := by
  unfold tailWord_6213137
  simp only [CollatzResearch.WordTrace]
  refine ⟨226611723291873243164685665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151074482194582162109790443 226611723291873243164685665)
  ·
    refine ⟨169958792468904932373514249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226611723291873243164685665 169958792468904932373514249)
    ·
      refine ⟨127469094351678699280135687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169958792468904932373514249 127469094351678699280135687)
      ·
        refine ⟨191203641527518048920203531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127469094351678699280135687 191203641527518048920203531)
        ·
          refine ⟨286805462291277073380305297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191203641527518048920203531 286805462291277073380305297)
          ·
            refine ⟨215104096718457805035228973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286805462291277073380305297 215104096718457805035228973)
            ·
              refine ⟨80664036269421676888210865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215104096718457805035228973 80664036269421676888210865)
              ·
                refine ⟨60498027202066257666158149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80664036269421676888210865 60498027202066257666158149)
                ·
                  refine ⟨11343380100387423312404653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60498027202066257666158149 11343380100387423312404653)
                  ·
                    refine ⟨4253767537645283742151745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11343380100387423312404653 4253767537645283742151745)
                    ·
                      refine ⟨3190325653233962806613809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4253767537645283742151745 3190325653233962806613809)
                      ·
                        rfl

theorem cell23_6213137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 3, 2].length) (baseStart_6213137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213137 prefixEnd_6213137 := by exact prefixLift 6213137
  have htrace : WordTrace (prefixWord ++ tailWord_6213137) baseStart_6213137 baseEnd_6213137 := by
    simpa [prefixWord, tailWord_6213137, baseEnd_6213137] using wordTrace_append hprefix tailTrace_6213137
  have hstable : (prefixWord ++ tailWord_6213137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213137).length < 2 ^ (prefixWord ++ tailWord_6213137).sum := by decide
  have hdescent : baseEnd_6213137 < baseStart_6213137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213154 : List Nat := [3, 3, 1, 1, 1, 1, 3, 3, 2, 3, 2]
def baseStart_6213154 : Nat := 118140960795 + 6213154 * 2 ^ 59
def prefixEnd_6213154 : Nat := 4983230072969 + 3 ^ 40 * 6213154 * 2
def baseEnd_6213154 : Nat := 3190334382405089240101231

theorem tailTrace_6213154 : CollatzResearch.WordTrace tailWord_6213154 prefixEnd_6213154 3190334382405089240101231 := by
  unfold tailWord_6213154
  simp only [CollatzResearch.WordTrace]
  refine ⟨56653085833202913767013629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151074895555207770045369677 56653085833202913767013629)
  ·
    refine ⟨21244907187451092662630111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56653085833202913767013629 21244907187451092662630111)
    ·
      refine ⟨31867360781176638993945167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21244907187451092662630111 31867360781176638993945167)
      ·
        refine ⟨47801041171764958490917751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31867360781176638993945167 47801041171764958490917751)
        ·
          refine ⟨71701561757647437736376627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47801041171764958490917751 71701561757647437736376627)
          ·
            refine ⟨107552342636471156604564941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71701561757647437736376627 107552342636471156604564941)
            ·
              refine ⟨40332128488676683726711853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107552342636471156604564941 40332128488676683726711853)
              ·
                refine ⟨15124548183253756397516945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40332128488676683726711853 15124548183253756397516945)
                ·
                  refine ⟨11343411137440317298137709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15124548183253756397516945 11343411137440317298137709)
                  ·
                    refine ⟨4253779176540118986801641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11343411137440317298137709 4253779176540118986801641)
                    ·
                      refine ⟨3190334382405089240101231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4253779176540118986801641 3190334382405089240101231)
                      ·
                        rfl

theorem cell23_6213154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_6213154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213154 prefixEnd_6213154 := by exact prefixLift 6213154
  have htrace : WordTrace (prefixWord ++ tailWord_6213154) baseStart_6213154 baseEnd_6213154 := by
    simpa [prefixWord, tailWord_6213154, baseEnd_6213154] using wordTrace_append hprefix tailTrace_6213154
  have hstable : (prefixWord ++ tailWord_6213154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213154).length < 2 ^ (prefixWord ++ tailWord_6213154).sum := by decide
  have hdescent : baseEnd_6213154 < baseStart_6213154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213184 : List Nat := [2, 1, 1, 2, 2, 2, 1, 5, 3, 2, 2]
def baseStart_6213184 : Nat := 118140960795 + 6213184 * 2 ^ 59
def prefixEnd_6213184 : Nat := 4983230072969 + 3 ^ 40 * 6213184 * 2
def baseEnd_6213184 : Nat := 3190349786824724122726093

theorem tailTrace_6213184 : CollatzResearch.WordTrace tailWord_6213184 prefixEnd_6213184 3190349786824724122726093 := by
  unfold tailWord_6213184
  simp only [CollatzResearch.WordTrace]
  refine ⟨113306718761351485095823303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151075625015135313461097737 113306718761351485095823303)
  ·
    refine ⟨169960078142027227643734955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113306718761351485095823303 169960078142027227643734955)
    ·
      refine ⟨254940117213040841465602433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169960078142027227643734955 254940117213040841465602433)
      ·
        refine ⟨191205087909780631099201825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254940117213040841465602433 191205087909780631099201825)
        ·
          refine ⟨143403815932335473324401369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191205087909780631099201825 143403815932335473324401369)
          ·
            refine ⟨107552861949251604993301027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143403815932335473324401369 107552861949251604993301027)
            ·
              refine ⟨161329292923877407489951541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107552861949251604993301027 161329292923877407489951541)
              ·
                refine ⟨15124621211613506952182957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 161329292923877407489951541 15124621211613506952182957)
                ·
                  refine ⟨5671732954355065107068609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15124621211613506952182957 5671732954355065107068609)
                  ·
                    refine ⟨4253799715766298830301457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5671732954355065107068609 4253799715766298830301457)
                    ·
                      refine ⟨3190349786824724122726093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4253799715766298830301457 3190349786824724122726093)
                      ·
                        rfl

theorem cell23_6213184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 3, 2, 2].length) (baseStart_6213184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213184 prefixEnd_6213184 := by exact prefixLift 6213184
  have htrace : WordTrace (prefixWord ++ tailWord_6213184) baseStart_6213184 baseEnd_6213184 := by
    simpa [prefixWord, tailWord_6213184, baseEnd_6213184] using wordTrace_append hprefix tailTrace_6213184
  have hstable : (prefixWord ++ tailWord_6213184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213184).length < 2 ^ (prefixWord ++ tailWord_6213184).sum := by decide
  have hdescent : baseEnd_6213184 < baseStart_6213184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213204 : List Nat := [2, 4, 1, 1, 1, 2, 2, 4, 1, 2, 3]
def baseStart_6213204 : Nat := 118140960795 + 6213204 * 2 ^ 59
def prefixEnd_6213204 : Nat := 4983230072969 + 3 ^ 40 * 6213204 * 2
def baseEnd_6213204 : Nat := 3190360056437814044476001

theorem tailTrace_6213204 : CollatzResearch.WordTrace tailWord_6213204 prefixEnd_6213204 3190360056437814044476001 := by
  unfold tailWord_6213204
  simp only [CollatzResearch.WordTrace]
  refine ⟨113307083491315256803687333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151076111321753675738249777 113307083491315256803687333)
  ·
    refine ⟨21245078154621610650691375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113307083491315256803687333 21245078154621610650691375)
    ·
      refine ⟨31867617231932415976037063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21245078154621610650691375 31867617231932415976037063)
      ·
        refine ⟨47801425847898623964055595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31867617231932415976037063 47801425847898623964055595)
        ·
          refine ⟨71702138771847935946083393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47801425847898623964055595 71702138771847935946083393)
          ·
            refine ⟨53776604078885951959562545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71702138771847935946083393 53776604078885951959562545)
            ·
              refine ⟨40332453059164463969671909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53776604078885951959562545 40332453059164463969671909)
              ·
                refine ⟨7562334948593336994313483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40332453059164463969671909 7562334948593336994313483)
                ·
                  refine ⟨11343502422890005491470225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7562334948593336994313483 11343502422890005491470225)
                  ·
                    refine ⟨8507626817167504118602669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11343502422890005491470225 8507626817167504118602669)
                    ·
                      refine ⟨3190360056437814044476001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8507626817167504118602669 3190360056437814044476001)
                      ·
                        rfl

theorem cell23_6213204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_6213204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213204 prefixEnd_6213204 := by exact prefixLift 6213204
  have htrace : WordTrace (prefixWord ++ tailWord_6213204) baseStart_6213204 baseEnd_6213204 := by
    simpa [prefixWord, tailWord_6213204, baseEnd_6213204] using wordTrace_append hprefix tailTrace_6213204
  have hstable : (prefixWord ++ tailWord_6213204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213204).length < 2 ^ (prefixWord ++ tailWord_6213204).sum := by decide
  have hdescent : baseEnd_6213204 < baseStart_6213204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213207 : List Nat := [1, 1, 3, 2, 2, 4, 3, 7]
def baseStart_6213207 : Nat := 118140960795 + 6213207 * 2 ^ 59
def prefixEnd_6213207 : Nat := 4983230072969 + 3 ^ 40 * 6213207 * 2
def baseEnd_6213207 : Nat := 118161540625176945656981

theorem tailTrace_6213207 : CollatzResearch.WordTrace tailWord_6213207 prefixEnd_6213207 118161540625176945656981 := by
  unfold tailWord_6213207
  simp only [CollatzResearch.WordTrace]
  refine ⟨226614276401619645119733875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151076184267746430079822583 226614276401619645119733875)
  ·
    refine ⟨339921414602429467679600813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226614276401619645119733875 339921414602429467679600813)
    ·
      refine ⟨127470530475911050379850305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 339921414602429467679600813 127470530475911050379850305)
      ·
        refine ⟨95602897856933287784887729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127470530475911050379850305 95602897856933287784887729)
        ·
          refine ⟨71702173392699965838665797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95602897856933287784887729 71702173392699965838665797)
          ·
            refine ⟨13444157511131243594749837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71702173392699965838665797 13444157511131243594749837)
            ·
              refine ⟨5041559066674216348031189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13444157511131243594749837 5041559066674216348031189)
              ·
                refine ⟨118161540625176945656981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5041559066674216348031189 118161540625176945656981)
                ·
                  rfl

theorem cell23_6213207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 7].length) (baseStart_6213207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213207 prefixEnd_6213207 := by exact prefixLift 6213207
  have htrace : WordTrace (prefixWord ++ tailWord_6213207) baseStart_6213207 baseEnd_6213207 := by
    simpa [prefixWord, tailWord_6213207, baseEnd_6213207] using wordTrace_append hprefix tailTrace_6213207
  have hstable : (prefixWord ++ tailWord_6213207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213207).length < 2 ^ (prefixWord ++ tailWord_6213207).sum := by decide
  have hdescent : baseEnd_6213207 < baseStart_6213207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213217 : List Nat := [1, 2, 3, 1, 1, 3, 1, 4, 1, 3, 3]
def baseStart_6213217 : Nat := 118140960795 + 6213217 * 2 ^ 59
def prefixEnd_6213217 : Nat := 4983230072969 + 3 ^ 40 * 6213217 * 2
def baseEnd_6213217 : Nat := 3190366731686322493613441

theorem tailTrace_6213217 : CollatzResearch.WordTrace tailWord_6213217 prefixEnd_6213217 3190366731686322493613441 := by
  unfold tailWord_6213217
  simp only [CollatzResearch.WordTrace]
  refine ⟨226614641131583416827597905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151076427421055611218398603 226614641131583416827597905)
  ·
    refine ⟨169960980848687562620698429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226614641131583416827597905 169960980848687562620698429)
    ·
      refine ⟨63735367818257835982761911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169960980848687562620698429 63735367818257835982761911)
      ·
        refine ⟨95603051727386753974142867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63735367818257835982761911 95603051727386753974142867)
        ·
          refine ⟨143404577591080130961214301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95603051727386753974142867 143404577591080130961214301)
          ·
            refine ⟨53776716596655049110455363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143404577591080130961214301 53776716596655049110455363)
            ·
              refine ⟨80665074894982573665683045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53776716596655049110455363 80665074894982573665683045)
              ·
                refine ⟨15124701542809232562315571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80665074894982573665683045 15124701542809232562315571)
                ·
                  refine ⟨22687052314213848843473357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15124701542809232562315571 22687052314213848843473357)
                  ·
                    refine ⟨8507644617830193316302509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22687052314213848843473357 8507644617830193316302509)
                    ·
                      refine ⟨3190366731686322493613441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8507644617830193316302509 3190366731686322493613441)
                      ·
                        rfl

theorem cell23_6213217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_6213217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213217 prefixEnd_6213217 := by exact prefixLift 6213217
  have htrace : WordTrace (prefixWord ++ tailWord_6213217) baseStart_6213217 baseEnd_6213217 := by
    simpa [prefixWord, tailWord_6213217, baseEnd_6213217] using wordTrace_append hprefix tailTrace_6213217
  have hstable : (prefixWord ++ tailWord_6213217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213217).length < 2 ^ (prefixWord ++ tailWord_6213217).sum := by decide
  have hdescent : baseEnd_6213217 < baseStart_6213217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213221 : List Nat := [1, 3, 1, 3, 3, 1, 4, 1, 1, 2, 3]
def baseStart_6213221 : Nat := 118140960795 + 6213221 * 2 ^ 59
def prefixEnd_6213221 : Nat := 4983230072969 + 3 ^ 40 * 6213221 * 2
def baseEnd_6213221 : Nat := 3190368785608940477963423

theorem tailTrace_6213221 : CollatzResearch.WordTrace tailWord_6213221 prefixEnd_6213221 3190368785608940477963423 := by
  unfold tailWord_6213221
  simp only [CollatzResearch.WordTrace]
  refine ⟨226614787023568925510743517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151076524682379283673829011 226614787023568925510743517)
  ·
    refine ⟨84980545133838347066528819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226614787023568925510743517 84980545133838347066528819)
    ·
      refine ⟨127470817700757520599793229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84980545133838347066528819 127470817700757520599793229)
      ·
        refine ⟨47801556637784070224922461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127470817700757520599793229 47801556637784070224922461)
        ·
          refine ⟨17925583739169026334345923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47801556637784070224922461 17925583739169026334345923)
          ·
            refine ⟨26888375608753539501518885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17925583739169026334345923 26888375608753539501518885)
            ·
              refine ⟨5041570426641288656534791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26888375608753539501518885 5041570426641288656534791)
              ·
                refine ⟨7562355639961932984802187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5041570426641288656534791 7562355639961932984802187)
                ·
                  refine ⟨11343533459942899477203281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7562355639961932984802187 11343533459942899477203281)
                  ·
                    refine ⟨8507650094957174607902461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11343533459942899477203281 8507650094957174607902461)
                    ·
                      refine ⟨3190368785608940477963423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8507650094957174607902461 3190368785608940477963423)
                      ·
                        rfl

theorem cell23_6213221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_6213221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213221 prefixEnd_6213221 := by exact prefixLift 6213221
  have htrace : WordTrace (prefixWord ++ tailWord_6213221) baseStart_6213221 baseEnd_6213221 := by
    simpa [prefixWord, tailWord_6213221, baseEnd_6213221] using wordTrace_append hprefix tailTrace_6213221
  have hstable : (prefixWord ++ tailWord_6213221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213221).length < 2 ^ (prefixWord ++ tailWord_6213221).sum := by decide
  have hdescent : baseEnd_6213221 < baseStart_6213221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213277 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 1, 6, 3]
def baseStart_6213277 : Nat := 118140960795 + 6213277 * 2 ^ 59
def prefixEnd_6213277 : Nat := 4983230072969 + 3 ^ 40 * 6213277 * 2
def baseEnd_6213277 : Nat := 3190397540525592258863165

theorem tailTrace_6213277 : CollatzResearch.WordTrace tailWord_6213277 prefixEnd_6213277 3190397540525592258863165 := by
  unfold tailWord_6213277
  simp only [CollatzResearch.WordTrace]
  refine ⟨226616829511366047074782085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151077886340910698049854723 226616829511366047074782085)
  ·
    refine ⟨42490655533381133826521641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226616829511366047074782085 42490655533381133826521641)
    ·
      refine ⟨31867991650035850369891231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42490655533381133826521641 31867991650035850369891231)
      ·
        refine ⟨47801987475053775554836847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31867991650035850369891231 47801987475053775554836847)
        ·
          refine ⟨71702981212580663332255271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47801987475053775554836847 71702981212580663332255271)
          ·
            refine ⟨107554471818870994998382907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71702981212580663332255271 107554471818870994998382907)
            ·
              refine ⟨161331707728306492497574361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107554471818870994998382907 161331707728306492497574361)
              ·
                refine ⟨120998780796229869373180771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161331707728306492497574361 120998780796229869373180771)
                ·
                  refine ⟨181498171194344804059771157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120998780796229869373180771 181498171194344804059771157)
                  ·
                    refine ⟨8507726774734912690301773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 181498171194344804059771157 8507726774734912690301773)
                    ·
                      refine ⟨3190397540525592258863165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8507726774734912690301773 3190397540525592258863165)
                      ·
                        rfl

theorem cell23_6213277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_6213277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213277 prefixEnd_6213277 := by exact prefixLift 6213277
  have htrace : WordTrace (prefixWord ++ tailWord_6213277) baseStart_6213277 baseEnd_6213277 := by
    simpa [prefixWord, tailWord_6213277, baseEnd_6213277] using wordTrace_append hprefix tailTrace_6213277
  have hstable : (prefixWord ++ tailWord_6213277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213277).length < 2 ^ (prefixWord ++ tailWord_6213277).sum := by decide
  have hdescent : baseEnd_6213277 < baseStart_6213277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213278 : List Nat := [4, 3, 1, 1, 1, 2, 2, 3, 1, 3, 2]
def baseStart_6213278 : Nat := 118140960795 + 6213278 * 2 ^ 59
def prefixEnd_6213278 : Nat := 4983230072969 + 3 ^ 40 * 6213278 * 2
def baseEnd_6213278 : Nat := 3190398054006246754950661

theorem tailTrace_6213278 : CollatzResearch.WordTrace tailWord_6213278 prefixEnd_6213278 3190398054006246754950661 := by
  unfold tailWord_6213278
  simp only [CollatzResearch.WordTrace]
  refine ⟨28327108248045303030696061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151077910656241616163712325 28327108248045303030696061)
  ·
    refine ⟨10622665593016988636511023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28327108248045303030696061 10622665593016988636511023)
    ·
      refine ⟨15933998389525482954766535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10622665593016988636511023 15933998389525482954766535)
      ·
        refine ⟨23900997584288224432149803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15933998389525482954766535 23900997584288224432149803)
        ·
          refine ⟨35851496376432336648224705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23900997584288224432149803 35851496376432336648224705)
          ·
            refine ⟨26888622282324252486168529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35851496376432336648224705 26888622282324252486168529)
            ·
              refine ⟨20166466711743189364626397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26888622282324252486168529 20166466711743189364626397)
              ·
                refine ⟨7562425016903696011734899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20166466711743189364626397 7562425016903696011734899)
                ·
                  refine ⟨11343637525355544017602349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7562425016903696011734899 11343637525355544017602349)
                  ·
                    refine ⟨4253864072008329006600881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11343637525355544017602349 4253864072008329006600881)
                    ·
                      refine ⟨3190398054006246754950661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4253864072008329006600881 3190398054006246754950661)
                      ·
                        rfl

theorem cell23_6213278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_6213278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213278 prefixEnd_6213278 := by exact prefixLift 6213278
  have htrace : WordTrace (prefixWord ++ tailWord_6213278) baseStart_6213278 baseEnd_6213278 := by
    simpa [prefixWord, tailWord_6213278, baseEnd_6213278] using wordTrace_append hprefix tailTrace_6213278
  have hstable : (prefixWord ++ tailWord_6213278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213278).length < 2 ^ (prefixWord ++ tailWord_6213278).sum := by decide
  have hdescent : baseEnd_6213278 < baseStart_6213278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213302 : List Nat := [5, 1, 3, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_6213302 : Nat := 118140960795 + 6213302 * 2 ^ 59
def prefixEnd_6213302 : Nat := 4983230072969 + 3 ^ 40 * 6213302 * 2
def baseEnd_6213302 : Nat := 3190410377541954661050551

theorem tailTrace_6213302 : CollatzResearch.WordTrace tailWord_6213302 prefixEnd_6213302 3190410377541954661050551 := by
  unfold tailWord_6213302
  simp only [CollatzResearch.WordTrace]
  refine ⟨14163608833517217271527635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151078494224183650896294773 14163608833517217271527635)
  ·
    refine ⟨21245413250275825907291453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14163608833517217271527635 21245413250275825907291453)
    ·
      refine ⟨7967029968853434715234295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21245413250275825907291453 7967029968853434715234295)
      ·
        refine ⟨11950544953280152072851443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7967029968853434715234295 11950544953280152072851443)
        ·
          refine ⟨17925817429920228109277165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11950544953280152072851443 17925817429920228109277165)
          ·
            refine ⟨6722181536220085540978937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17925817429920228109277165 6722181536220085540978937)
            ·
              refine ⟨5041636152165064155734203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6722181536220085540978937 5041636152165064155734203)
              ·
                refine ⟨7562454228247596233601305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5041636152165064155734203 7562454228247596233601305)
                ·
                  refine ⟨5671840671185697175200979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7562454228247596233601305 5671840671185697175200979)
                  ·
                    refine ⟨8507761006778545762801469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5671840671185697175200979 8507761006778545762801469)
                    ·
                      refine ⟨3190410377541954661050551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8507761006778545762801469 3190410377541954661050551)
                      ·
                        rfl

theorem cell23_6213302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_6213302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213302 prefixEnd_6213302 := by exact prefixLift 6213302
  have htrace : WordTrace (prefixWord ++ tailWord_6213302) baseStart_6213302 baseEnd_6213302 := by
    simpa [prefixWord, tailWord_6213302, baseEnd_6213302] using wordTrace_append hprefix tailTrace_6213302
  have hstable : (prefixWord ++ tailWord_6213302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213302).length < 2 ^ (prefixWord ++ tailWord_6213302).sum := by decide
  have hdescent : baseEnd_6213302 < baseStart_6213302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213307 : List Nat := [1, 1, 1, 1, 1, 2, 3, 5, 2, 3, 3]
def baseStart_6213307 : Nat := 118140960795 + 6213307 * 2 ^ 59
def prefixEnd_6213307 : Nat := 4983230072969 + 3 ^ 40 * 6213307 * 2
def baseEnd_6213307 : Nat := 3190412944945227141488027

theorem tailTrace_6213307 : CollatzResearch.WordTrace tailWord_6213307 prefixEnd_6213307 3190412944945227141488027 := by
  unfold tailWord_6213307
  simp only [CollatzResearch.WordTrace]
  refine ⟨226617923701257362198374175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151078615800838241465582783 226617923701257362198374175)
  ·
    refine ⟨339926885551886043297561263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226617923701257362198374175 339926885551886043297561263)
    ·
      refine ⟨509890328327829064946341895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339926885551886043297561263 509890328327829064946341895)
      ·
        refine ⟨764835492491743597419512843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509890328327829064946341895 764835492491743597419512843)
        ·
          refine ⟨1147253238737615396129269265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 764835492491743597419512843 1147253238737615396129269265)
          ·
            refine ⟨860439929053211547096951949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1147253238737615396129269265 860439929053211547096951949)
            ·
              refine ⟨322664973394954330161356981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 860439929053211547096951949 322664973394954330161356981)
              ·
                refine ⟨30249841255776968452627217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 322664973394954330161356981 30249841255776968452627217)
                ·
                  refine ⟨22687380941832726339470413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30249841255776968452627217 22687380941832726339470413)
                  ·
                    refine ⟨8507767853187272377301405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22687380941832726339470413 8507767853187272377301405)
                    ·
                      refine ⟨3190412944945227141488027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8507767853187272377301405 3190412944945227141488027)
                      ·
                        rfl

theorem cell23_6213307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3, 3].length) (baseStart_6213307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213307 prefixEnd_6213307 := by exact prefixLift 6213307
  have htrace : WordTrace (prefixWord ++ tailWord_6213307) baseStart_6213307 baseEnd_6213307 := by
    simpa [prefixWord, tailWord_6213307, baseEnd_6213307] using wordTrace_append hprefix tailTrace_6213307
  have hstable : (prefixWord ++ tailWord_6213307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213307).length < 2 ^ (prefixWord ++ tailWord_6213307).sum := by decide
  have hdescent : baseEnd_6213307 < baseStart_6213307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213308 : List Nat := [2, 2, 2, 3, 1, 3, 1, 3, 2, 2, 2]
def baseStart_6213308 : Nat := 118140960795 + 6213308 * 2 ^ 59
def prefixEnd_6213308 : Nat := 4983230072969 + 3 ^ 40 * 6213308 * 2
def baseEnd_6213308 : Nat := 3190413458425881637575523

theorem tailTrace_6213308 : CollatzResearch.WordTrace tailWord_6213308 prefixEnd_6213308 3190413458425881637575523 := by
  unfold tailWord_6213308
  simp only [CollatzResearch.WordTrace]
  refine ⟨113308980087126869684580289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151078640116169159579440385 113308980087126869684580289)
  ·
    refine ⟨84981735065345152263435217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113308980087126869684580289 84981735065345152263435217)
    ·
      refine ⟨63736301299008864197576413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84981735065345152263435217 63736301299008864197576413)
      ·
        refine ⟨23901112987128324074091155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63736301299008864197576413 23901112987128324074091155)
        ·
          refine ⟨35851669480692486111136733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23901112987128324074091155 35851669480692486111136733)
          ·
            refine ⟨13444376055259682291676275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35851669480692486111136733 13444376055259682291676275)
            ·
              refine ⟨20166564082889523437514413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13444376055259682291676275 20166564082889523437514413)
              ·
                refine ⟨7562461531083571289067905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20166564082889523437514413 7562461531083571289067905)
                ·
                  refine ⟨5671846148312678466800929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7562461531083571289067905 5671846148312678466800929)
                  ·
                    refine ⟨4253884611234508850100697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5671846148312678466800929 4253884611234508850100697)
                    ·
                      refine ⟨3190413458425881637575523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4253884611234508850100697 3190413458425881637575523)
                      ·
                        rfl

theorem cell23_6213308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_6213308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213308 prefixEnd_6213308 := by exact prefixLift 6213308
  have htrace : WordTrace (prefixWord ++ tailWord_6213308) baseStart_6213308 baseEnd_6213308 := by
    simpa [prefixWord, tailWord_6213308, baseEnd_6213308] using wordTrace_append hprefix tailTrace_6213308
  have hstable : (prefixWord ++ tailWord_6213308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213308).length < 2 ^ (prefixWord ++ tailWord_6213308).sum := by decide
  have hdescent : baseEnd_6213308 < baseStart_6213308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213337 : List Nat := [1, 2, 1, 2, 3, 3, 1, 2, 1, 2, 5]
def baseStart_6213337 : Nat := 118140960795 + 6213337 * 2 ^ 59
def prefixEnd_6213337 : Nat := 4983230072969 + 3 ^ 40 * 6213337 * 2
def baseEnd_6213337 : Nat := 3190428349364862024112889

theorem tailTrace_6213337 : CollatzResearch.WordTrace tailWord_6213337 prefixEnd_6213337 3190428349364862024112889 := by
  unfold tailWord_6213337
  simp only [CollatzResearch.WordTrace]
  refine ⟨226619017891148677321966265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151079345260765784881310843 226619017891148677321966265)
  ·
    refine ⟨169964263418361507991474699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226619017891148677321966265 169964263418361507991474699)
    ·
      refine ⟨254946395127542261987212049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169964263418361507991474699 254946395127542261987212049)
      ·
        refine ⟨191209796345656696490409037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254946395127542261987212049 191209796345656696490409037)
        ·
          refine ⟨71703673629621261183903389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191209796345656696490409037 71703673629621261183903389)
          ·
            refine ⟨26888877611107972943963771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71703673629621261183903389 26888877611107972943963771)
            ·
              refine ⟨40333316416661959415945657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26888877611107972943963771 40333316416661959415945657)
              ·
                refine ⟨30249987312496469561959243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40333316416661959415945657 30249987312496469561959243)
                ·
                  refine ⟨45374980968744704342938865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30249987312496469561959243 45374980968744704342938865)
                  ·
                    refine ⟨34031235726558528257204149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45374980968744704342938865 34031235726558528257204149)
                    ·
                      refine ⟨3190428349364862024112889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34031235726558528257204149 3190428349364862024112889)
                      ·
                        rfl

theorem cell23_6213337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_6213337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213337 prefixEnd_6213337 := by exact prefixLift 6213337
  have htrace : WordTrace (prefixWord ++ tailWord_6213337) baseStart_6213337 baseEnd_6213337 := by
    simpa [prefixWord, tailWord_6213337, baseEnd_6213337] using wordTrace_append hprefix tailTrace_6213337
  have hstable : (prefixWord ++ tailWord_6213337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213337).length < 2 ^ (prefixWord ++ tailWord_6213337).sum := by decide
  have hdescent : baseEnd_6213337 < baseStart_6213337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213384 : List Nat := [2, 1, 3, 2, 2, 1, 3, 1, 1, 4, 3]
def baseStart_6213384 : Nat := 118140960795 + 6213384 * 2 ^ 59
def prefixEnd_6213384 : Nat := 4983230072969 + 3 ^ 40 * 6213384 * 2
def baseEnd_6213384 : Nat := 3190452482955623340225173

theorem tailTrace_6213384 : CollatzResearch.WordTrace tailWord_6213384 prefixEnd_6213384 3190452482955623340225173 := by
  unfold tailWord_6213384
  simp only [CollatzResearch.WordTrace]
  refine ⟨113310366060989202174463603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151080488081318936232618137 113310366060989202174463603)
  ·
    refine ⟨169965549091483803261695405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113310366060989202174463603 169965549091483803261695405)
    ·
      refine ⟨63737080909306426223135777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169965549091483803261695405 63737080909306426223135777)
      ·
        refine ⟨47802810681979819667351833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63737080909306426223135777 47802810681979819667351833)
        ·
          refine ⟨35852108011484864750513875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47802810681979819667351833 35852108011484864750513875)
          ·
            refine ⟨53778162017227297125770813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35852108011484864750513875 53778162017227297125770813)
            ·
              refine ⟨20166810756460236422164055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53778162017227297125770813 20166810756460236422164055)
              ·
                refine ⟨30250216134690354633246083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20166810756460236422164055 30250216134690354633246083)
                ·
                  refine ⟨45375324202035531949869125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30250216134690354633246083 45375324202035531949869125)
                  ·
                    refine ⟨8507873287881662240600461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45375324202035531949869125 8507873287881662240600461)
                    ·
                      refine ⟨3190452482955623340225173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8507873287881662240600461 3190452482955623340225173)
                      ·
                        rfl

theorem cell23_6213384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_6213384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213384 prefixEnd_6213384 := by exact prefixLift 6213384
  have htrace : WordTrace (prefixWord ++ tailWord_6213384) baseStart_6213384 baseEnd_6213384 := by
    simpa [prefixWord, tailWord_6213384, baseEnd_6213384] using wordTrace_append hprefix tailTrace_6213384
  have hstable : (prefixWord ++ tailWord_6213384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213384).length < 2 ^ (prefixWord ++ tailWord_6213384).sum := by decide
  have hdescent : baseEnd_6213384 < baseStart_6213384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213407 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 8]
def baseStart_6213407 : Nat := 118140960795 + 6213407 * 2 ^ 59
def prefixEnd_6213407 : Nat := 4983230072969 + 3 ^ 40 * 6213407 * 2
def baseEnd_6213407 : Nat := 3190464293010676750237567

theorem tailTrace_6213407 : CollatzResearch.WordTrace tailWord_6213407 prefixEnd_6213407 3190464293010676750237567 := by
  unfold tailWord_6213407
  simp only [CollatzResearch.WordTrace]
  refine ⟨226621571000895079277014475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151081047333930052851342983 226621571000895079277014475)
  ·
    refine ⟨339932356501342618915521713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226621571000895079277014475 339932356501342618915521713)
    ·
      refine ⟨254949267376006964186641285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339932356501342618915521713 254949267376006964186641285)
      ·
        refine ⟨47802987633001305784995241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254949267376006964186641285 47802987633001305784995241)
        ·
          refine ⟨35852240724750979338746431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47802987633001305784995241 35852240724750979338746431)
          ·
            refine ⟨53778361087126469008119647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35852240724750979338746431 53778361087126469008119647)
            ·
              refine ⟨80667541630689703512179471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53778361087126469008119647 80667541630689703512179471)
              ·
                refine ⟨121001312446034555268269207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80667541630689703512179471 121001312446034555268269207)
                ·
                  refine ⟨181501968669051832902403811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121001312446034555268269207 181501968669051832902403811)
                  ·
                    refine ⟨272252953003577749353605717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 181501968669051832902403811 272252953003577749353605717)
                    ·
                      refine ⟨3190464293010676750237567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 272252953003577749353605717 3190464293010676750237567)
                      ·
                        rfl

theorem cell23_6213407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_6213407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213407 prefixEnd_6213407 := by exact prefixLift 6213407
  have htrace : WordTrace (prefixWord ++ tailWord_6213407) baseStart_6213407 baseEnd_6213407 := by
    simpa [prefixWord, tailWord_6213407, baseEnd_6213407] using wordTrace_append hprefix tailTrace_6213407
  have hstable : (prefixWord ++ tailWord_6213407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213407).length < 2 ^ (prefixWord ++ tailWord_6213407).sum := by decide
  have hdescent : baseEnd_6213407 < baseStart_6213407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213454 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4]
def baseStart_6213454 : Nat := 118140960795 + 6213454 * 2 ^ 59
def prefixEnd_6213454 : Nat := 4983230072969 + 3 ^ 40 * 6213454 * 2
def baseEnd_6213454 : Nat := 3190488426601438066349851

theorem tailTrace_6213454 : CollatzResearch.WordTrace tailWord_6213454 prefixEnd_6213454 3190488426601438066349851 := by
  unfold tailWord_6213454
  simp only [CollatzResearch.WordTrace]
  refine ⟨28327910653965600787996927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151082190154483204202650277 28327910653965600787996927)
  ·
    refine ⟨42491865980948401181995391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28327910653965600787996927 42491865980948401181995391)
    ·
      refine ⟨63737798971422601772993087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42491865980948401181995391 63737798971422601772993087)
      ·
        refine ⟨95606698457133902659489631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63737798971422601772993087 95606698457133902659489631)
        ·
          refine ⟨143410047685700853989234447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95606698457133902659489631 143410047685700853989234447)
          ·
            refine ⟨215115071528551280983851671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143410047685700853989234447 215115071528551280983851671)
            ·
              refine ⟨322672607292826921475777507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215115071528551280983851671 322672607292826921475777507)
              ·
                refine ⟨484008910939240382213666261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322672607292826921475777507 484008910939240382213666261)
                ·
                  refine ⟨11343958850138446458132803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 484008910939240382213666261 11343958850138446458132803)
                  ·
                    refine ⟨17015938275207669687199205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11343958850138446458132803 17015938275207669687199205)
                    ·
                      refine ⟨3190488426601438066349851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17015938275207669687199205 3190488426601438066349851)
                      ·
                        rfl

theorem cell23_6213454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_6213454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213454 prefixEnd_6213454 := by exact prefixLift 6213454
  have htrace : WordTrace (prefixWord ++ tailWord_6213454) baseStart_6213454 baseEnd_6213454 := by
    simpa [prefixWord, tailWord_6213454, baseEnd_6213454] using wordTrace_append hprefix tailTrace_6213454
  have hstable : (prefixWord ++ tailWord_6213454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213454).length < 2 ^ (prefixWord ++ tailWord_6213454).sum := by decide
  have hdescent : baseEnd_6213454 < baseStart_6213454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213458 : List Nat := [3, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2]
def baseStart_6213458 : Nat := 118140960795 + 6213458 * 2 ^ 59
def prefixEnd_6213458 : Nat := 4983230072969 + 3 ^ 40 * 6213458 * 2
def baseEnd_6213458 : Nat := 3190490480524056050699833

theorem tailTrace_6213458 : CollatzResearch.WordTrace tailWord_6213458 prefixEnd_6213458 3190490480524056050699833 := by
  unfold tailWord_6213458
  simp only [CollatzResearch.WordTrace]
  refine ⟨56655857780927578746780257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151082287415806876658080685 56655857780927578746780257)
  ·
    refine ⟨42491893335695684060085193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56655857780927578746780257 42491893335695684060085193)
    ·
      refine ⟨31868920001771763045063895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42491893335695684060085193 31868920001771763045063895)
      ·
        refine ⟨47803380002657644567595843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31868920001771763045063895 47803380002657644567595843)
        ·
          refine ⟨71705070003986466851393765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47803380002657644567595843 71705070003986466851393765)
          ·
            refine ⟨13444700625747462534636331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71705070003986466851393765 13444700625747462534636331)
            ·
              refine ⟨20167050938621193801954497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13444700625747462534636331 20167050938621193801954497)
              ·
                refine ⟨15125288203965895351465873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20167050938621193801954497 15125288203965895351465873)
                ·
                  refine ⟨11343966152974421513599405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15125288203965895351465873 11343966152974421513599405)
                  ·
                    refine ⟨4253987307365408067599777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11343966152974421513599405 4253987307365408067599777)
                    ·
                      refine ⟨3190490480524056050699833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4253987307365408067599777 3190490480524056050699833)
                      ·
                        rfl

theorem cell23_6213458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_6213458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213458 prefixEnd_6213458 := by exact prefixLift 6213458
  have htrace : WordTrace (prefixWord ++ tailWord_6213458) baseStart_6213458 baseEnd_6213458 := by
    simpa [prefixWord, tailWord_6213458, baseEnd_6213458] using wordTrace_append hprefix tailTrace_6213458
  have hstable : (prefixWord ++ tailWord_6213458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213458).length < 2 ^ (prefixWord ++ tailWord_6213458).sum := by decide
  have hdescent : baseEnd_6213458 < baseStart_6213458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213465 : List Nat := [1, 2, 1, 2, 2, 3, 5, 2, 1, 1, 3]
def baseStart_6213465 : Nat := 118140960795 + 6213465 * 2 ^ 59
def prefixEnd_6213465 : Nat := 4983230072969 + 3 ^ 40 * 6213465 * 2
def baseEnd_6213465 : Nat := 3190494074888637523312301

theorem tailTrace_6213465 : CollatzResearch.WordTrace tailWord_6213465 prefixEnd_6213465 3190494074888637523312301 := by
  unfold tailWord_6213465
  simp only [CollatzResearch.WordTrace]
  refine ⟨226623686434684955182625849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151082457623123303455083899 226623686434684955182625849)
  ·
    refine ⟨169967764826013716386969387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226623686434684955182625849 169967764826013716386969387)
    ·
      refine ⟨254951647239020574580454081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169967764826013716386969387 254951647239020574580454081)
      ·
        refine ⟨191213735429265430935340561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254951647239020574580454081 191213735429265430935340561)
        ·
          refine ⟨143410301571949073201505421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191213735429265430935340561 143410301571949073201505421)
          ·
            refine ⟨53778863089480902450564533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143410301571949073201505421 53778863089480902450564533)
            ·
              refine ⟨5041768414638834604740425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53778863089480902450564533 5041768414638834604740425)
              ·
                refine ⟨3781326310979125953555319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5041768414638834604740425 3781326310979125953555319)
                ·
                  refine ⟨5671989466468688930332979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3781326310979125953555319 5671989466468688930332979)
                  ·
                    refine ⟨8507984199703033395499469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5671989466468688930332979 8507984199703033395499469)
                    ·
                      refine ⟨3190494074888637523312301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8507984199703033395499469 3190494074888637523312301)
                      ·
                        rfl

theorem cell23_6213465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2, 1, 1, 3].length) (baseStart_6213465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213465 prefixEnd_6213465 := by exact prefixLift 6213465
  have htrace : WordTrace (prefixWord ++ tailWord_6213465) baseStart_6213465 baseEnd_6213465 := by
    simpa [prefixWord, tailWord_6213465, baseEnd_6213465] using wordTrace_append hprefix tailTrace_6213465
  have hstable : (prefixWord ++ tailWord_6213465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213465).length < 2 ^ (prefixWord ++ tailWord_6213465).sum := by decide
  have hdescent : baseEnd_6213465 < baseStart_6213465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213484 : List Nat := [2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 6]
def baseStart_6213484 : Nat := 118140960795 + 6213484 * 2 ^ 59
def prefixEnd_6213484 : Nat := 4983230072969 + 3 ^ 40 * 6213484 * 2
def baseEnd_6213484 : Nat := 3190503831021072948974713

theorem tailTrace_6213484 : CollatzResearch.WordTrace tailWord_6213484 prefixEnd_6213484 3190503831021072948974713 := by
  unfold tailWord_6213484
  simp only [CollatzResearch.WordTrace]
  refine ⟨113312189710808060713783753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151082919614410747618378337 113312189710808060713783753)
  ·
    refine ⟨84984142283106045535337815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113312189710808060713783753 84984142283106045535337815)
    ·
      refine ⟨127476213424659068303006723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84984142283106045535337815 127476213424659068303006723)
      ·
        refine ⟨191214320136988602454510085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127476213424659068303006723 191214320136988602454510085)
        ·
          refine ⟨35852685025685362960220641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191214320136988602454510085 35852685025685362960220641)
          ·
            refine ⟨26889513769264022220165481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35852685025685362960220641 26889513769264022220165481)
            ·
              refine ⟨20167135326948016665124111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26889513769264022220165481 20167135326948016665124111)
              ·
                refine ⟨30250702990422024997686167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20167135326948016665124111 30250702990422024997686167)
                ·
                  refine ⟨45376054485633037496529251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30250702990422024997686167 45376054485633037496529251)
                  ·
                    refine ⟨68064081728449556244793877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45376054485633037496529251 68064081728449556244793877)
                    ·
                      refine ⟨3190503831021072948974713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68064081728449556244793877 3190503831021072948974713)
                      ·
                        rfl

theorem cell23_6213484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_6213484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213484 prefixEnd_6213484 := by exact prefixLift 6213484
  have htrace : WordTrace (prefixWord ++ tailWord_6213484) baseStart_6213484 baseEnd_6213484 := by
    simpa [prefixWord, tailWord_6213484, baseEnd_6213484] using wordTrace_append hprefix tailTrace_6213484
  have hstable : (prefixWord ++ tailWord_6213484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213484).length < 2 ^ (prefixWord ++ tailWord_6213484).sum := by decide
  have hdescent : baseEnd_6213484 < baseStart_6213484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213521 : List Nat := [1, 2, 2, 1, 1, 1, 4, 3, 4, 1, 3]
def baseStart_6213521 : Nat := 118140960795 + 6213521 * 2 ^ 59
def prefixEnd_6213521 : Nat := 4983230072969 + 3 ^ 40 * 6213521 * 2
def baseEnd_6213521 : Nat := 3190522829805289304212043

theorem tailTrace_6213521 : CollatzResearch.WordTrace tailWord_6213521 prefixEnd_6213521 3190522829805289304212043 := by
  unfold tailWord_6213521
  simp only [CollatzResearch.WordTrace]
  refine ⟨226625728922482076746664417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151083819281654717831109611 226625728922482076746664417)
  ·
    refine ⟨169969296691861557559998313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226625728922482076746664417 169969296691861557559998313)
    ·
      refine ⟨127476972518896168169998735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169969296691861557559998313 127476972518896168169998735)
      ·
        refine ⟨191215458778344252254998103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127476972518896168169998735 191215458778344252254998103)
        ·
          refine ⟨286823188167516378382497155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191215458778344252254998103 286823188167516378382497155)
          ·
            refine ⟨430234782251274567573745733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286823188167516378382497155 430234782251274567573745733)
            ·
              refine ⟨80669021672113981420077325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 430234782251274567573745733 80669021672113981420077325)
              ·
                refine ⟨30250883127042743032528997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80669021672113981420077325 30250883127042743032528997)
                ·
                  refine ⟨5672040586320514318599187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30250883127042743032528997 5672040586320514318599187)
                  ·
                    refine ⟨8508060879480771477898781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5672040586320514318599187 8508060879480771477898781)
                    ·
                      refine ⟨3190522829805289304212043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8508060879480771477898781 3190522829805289304212043)
                      ·
                        rfl

theorem cell23_6213521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4, 1, 3].length) (baseStart_6213521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213521 prefixEnd_6213521 := by exact prefixLift 6213521
  have htrace : WordTrace (prefixWord ++ tailWord_6213521) baseStart_6213521 baseEnd_6213521 := by
    simpa [prefixWord, tailWord_6213521, baseEnd_6213521] using wordTrace_append hprefix tailTrace_6213521
  have hstable : (prefixWord ++ tailWord_6213521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213521).length < 2 ^ (prefixWord ++ tailWord_6213521).sum := by decide
  have hdescent : baseEnd_6213521 < baseStart_6213521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213528 : List Nat := [2, 1, 2, 6, 1, 2, 1, 8]
def baseStart_6213528 : Nat := 118140960795 + 6213528 * 2 ^ 59
def prefixEnd_6213528 : Nat := 4983230072969 + 3 ^ 40 * 6213528 * 2
def baseEnd_6213528 : Nat := 118167645339624843586093

theorem tailTrace_6213528 : CollatzResearch.WordTrace tailWord_6213528 prefixEnd_6213528 118167645339624843586093 := by
  unfold tailWord_6213528
  simp only [CollatzResearch.WordTrace]
  refine ⟨113312992116728358471084619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151083989488971144628112825 113312992116728358471084619)
  ·
    refine ⟨169969488175092537706626929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113312992116728358471084619 169969488175092537706626929)
    ·
      refine ⟨127477116131319403279970197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169969488175092537706626929 127477116131319403279970197)
      ·
        refine ⟨5975489818655597028748603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 127477116131319403279970197 5975489818655597028748603)
        ·
          refine ⟨8963234727983395543122905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5975489818655597028748603 8963234727983395543122905)
          ·
            refine ⟨6722426045987546657342179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8963234727983395543122905 6722426045987546657342179)
            ·
              refine ⟨10083639068981319986013269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6722426045987546657342179 10083639068981319986013269)
              ·
                refine ⟨118167645339624843586093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10083639068981319986013269 118167645339624843586093)
                ·
                  rfl

theorem cell23_6213528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 8].length) (baseStart_6213528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213528 prefixEnd_6213528 := by exact prefixLift 6213528
  have htrace : WordTrace (prefixWord ++ tailWord_6213528) baseStart_6213528 baseEnd_6213528 := by
    simpa [prefixWord, tailWord_6213528, baseEnd_6213528] using wordTrace_append hprefix tailTrace_6213528
  have hstable : (prefixWord ++ tailWord_6213528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213528).length < 2 ^ (prefixWord ++ tailWord_6213528).sum := by decide
  have hdescent : baseEnd_6213528 < baseStart_6213528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213556 : List Nat := [2, 5, 2, 1, 2, 1, 2, 3, 1, 2, 2]
def baseStart_6213556 : Nat := 118140960795 + 6213556 * 2 ^ 59
def prefixEnd_6213556 : Nat := 4983230072969 + 3 ^ 40 * 6213556 * 2
def baseEnd_6213556 : Nat := 3190540801628196667274383

theorem tailTrace_6213556 : CollatzResearch.WordTrace tailWord_6213556 prefixEnd_6213556 3190540801628196667274383 := by
  unfold tailWord_6213556
  simp only [CollatzResearch.WordTrace]
  refine ⟨113313502738677638862094261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151084670318236851816125681 113313502738677638862094261)
  ·
    refine ⟨10623140881751028643321337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113313502738677638862094261 10623140881751028643321337)
    ·
      refine ⟨7967355661313271482491003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10623140881751028643321337 7967355661313271482491003)
      ·
        refine ⟨11951033491969907223736505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7967355661313271482491003 11951033491969907223736505)
        ·
          refine ⟨8963275118977430417802379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11951033491969907223736505 8963275118977430417802379)
          ·
            refine ⟨13444912678466145626703569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8963275118977430417802379 13444912678466145626703569)
            ·
              refine ⟨10083684508849609220027677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13444912678466145626703569 10083684508849609220027677)
              ·
                refine ⟨3781381690818603457510379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10083684508849609220027677 3781381690818603457510379)
                ·
                  refine ⟨5672072536227905186265569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3781381690818603457510379 5672072536227905186265569)
                  ·
                    refine ⟨4254054402170928889699177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5672072536227905186265569 4254054402170928889699177)
                    ·
                      refine ⟨3190540801628196667274383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4254054402170928889699177 3190540801628196667274383)
                      ·
                        rfl

theorem cell23_6213556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_6213556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213556 prefixEnd_6213556 := by exact prefixLift 6213556
  have htrace : WordTrace (prefixWord ++ tailWord_6213556) baseStart_6213556 baseEnd_6213556 := by
    simpa [prefixWord, tailWord_6213556, baseEnd_6213556] using wordTrace_append hprefix tailTrace_6213556
  have hstable : (prefixWord ++ tailWord_6213556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213556).length < 2 ^ (prefixWord ++ tailWord_6213556).sum := by decide
  have hdescent : baseEnd_6213556 < baseStart_6213556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213565 : List Nat := [1, 4, 1, 2, 3, 2, 1, 3, 1, 3, 2]
def baseStart_6213565 : Nat := 118140960795 + 6213565 * 2 ^ 59
def prefixEnd_6213565 : Nat := 4983230072969 + 3 ^ 40 * 6213565 * 2
def baseEnd_6213565 : Nat := 3190545422954087132061841

theorem tailTrace_6213565 : CollatzResearch.WordTrace tailWord_6213565 prefixEnd_6213565 3190545422954087132061841 := by
  unfold tailWord_6213565
  simp only [CollatzResearch.WordTrace]
  refine ⟨226627333734322672261266149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151084889156215114840844099 226627333734322672261266149)
  ·
    refine ⟨42492625075185501048987403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226627333734322672261266149 42492625075185501048987403)
    ·
      refine ⟨63738937612778251573481105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42492625075185501048987403 63738937612778251573481105)
      ·
        refine ⟨47804203209583688680110829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63738937612778251573481105 47804203209583688680110829)
        ·
          refine ⟨17926576203593883255041561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47804203209583688680110829 17926576203593883255041561)
          ·
            refine ⟨13444932152695412441281171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17926576203593883255041561 13444932152695412441281171)
            ·
              refine ⟨20167398229043118661921757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13444932152695412441281171 20167398229043118661921757)
              ·
                refine ⟨7562774335891169498220659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20167398229043118661921757 7562774335891169498220659)
                ·
                  refine ⟨11344161503836754247330989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7562774335891169498220659 11344161503836754247330989)
                  ·
                    refine ⟨4254060563938782842749121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11344161503836754247330989 4254060563938782842749121)
                    ·
                      refine ⟨3190545422954087132061841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4254060563938782842749121 3190545422954087132061841)
                      ·
                        rfl

theorem cell23_6213565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_6213565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213565 prefixEnd_6213565 := by exact prefixLift 6213565
  have htrace : WordTrace (prefixWord ++ tailWord_6213565) baseStart_6213565 baseEnd_6213565 := by
    simpa [prefixWord, tailWord_6213565, baseEnd_6213565] using wordTrace_append hprefix tailTrace_6213565
  have hstable : (prefixWord ++ tailWord_6213565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213565).length < 2 ^ (prefixWord ++ tailWord_6213565).sum := by decide
  have hdescent : baseEnd_6213565 < baseStart_6213565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213584 : List Nat := [2, 1, 1, 1, 1, 2, 5, 3, 7]
def baseStart_6213584 : Nat := 118140960795 + 6213584 * 2 ^ 59
def prefixEnd_6213584 : Nat := 4983230072969 + 3 ^ 40 * 6213584 * 2
def baseEnd_6213584 : Nat := 354506131009613617524917

theorem tailTrace_6213584 : CollatzResearch.WordTrace tailWord_6213584 prefixEnd_6213584 354506131009613617524917 := by
  unfold tailWord_6213584
  simp only [CollatzResearch.WordTrace]
  refine ⟨113314013360626919253103903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151085351147502559004138537 113314013360626919253103903)
  ·
    refine ⟨169971020040940378879655855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113314013360626919253103903 169971020040940378879655855)
    ·
      refine ⟨254956530061410568319483783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169971020040940378879655855 254956530061410568319483783)
      ·
        refine ⟨382434795092115852479225675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254956530061410568319483783 382434795092115852479225675)
        ·
          refine ⟨573652192638173778718838513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382434795092115852479225675 573652192638173778718838513)
          ·
            refine ⟨430239144478630334039128885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 573652192638173778718838513 430239144478630334039128885)
            ·
              refine ⟨40334919794871593816168333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 430239144478630334039128885 40334919794871593816168333)
              ·
                refine ⟨15125594923076847681063125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40334919794871593816168333 15125594923076847681063125)
                ·
                  refine ⟨354506131009613617524917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15125594923076847681063125 354506131009613617524917)
                  ·
                    rfl

theorem cell23_6213584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 7].length) (baseStart_6213584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213584 prefixEnd_6213584 := by exact prefixLift 6213584
  have htrace : WordTrace (prefixWord ++ tailWord_6213584) baseStart_6213584 baseEnd_6213584 := by
    simpa [prefixWord, tailWord_6213584, baseEnd_6213584] using wordTrace_append hprefix tailTrace_6213584
  have hstable : (prefixWord ++ tailWord_6213584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213584).length < 2 ^ (prefixWord ++ tailWord_6213584).sum := by decide
  have hdescent : baseEnd_6213584 < baseStart_6213584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213701 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 2, 5, 3]
def baseStart_6213701 : Nat := 118140960795 + 6213701 * 2 ^ 59
def prefixEnd_6213701 : Nat := 4983230072969 + 3 ^ 40 * 6213701 * 2
def baseEnd_6213701 : Nat := 3190615256323098599961215

theorem tailTrace_6213701 : CollatzResearch.WordTrace tailWord_6213701 prefixEnd_6213701 3190615256323098599961215 := by
  unfold tailWord_6213701
  simp only [CollatzResearch.WordTrace]
  refine ⟨226632294061829967488216957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151088196041219978325477971 226632294061829967488216957)
  ·
    refine ⟨84987110273186237808081359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226632294061829967488216957 84987110273186237808081359)
    ·
      refine ⟨127480665409779356712122039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84987110273186237808081359 127480665409779356712122039)
      ·
        refine ⟨191220998114669035068183059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127480665409779356712122039 191220998114669035068183059)
        ·
          refine ⟨286831497172003552602274589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191220998114669035068183059 286831497172003552602274589)
          ·
            refine ⟨107561811439501332225852971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286831497172003552602274589 107561811439501332225852971)
            ·
              refine ⟨161342717159251998338779457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107561811439501332225852971 161342717159251998338779457)
              ·
                refine ⟨121007037869438998754084593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161342717159251998338779457 121007037869438998754084593)
                ·
                  refine ⟨90755278402079249065563445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121007037869438998754084593 90755278402079249065563445)
                  ·
                    refine ⟨8508307350194929599896573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90755278402079249065563445 8508307350194929599896573)
                    ·
                      refine ⟨3190615256323098599961215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8508307350194929599896573 3190615256323098599961215)
                      ·
                        rfl

theorem cell23_6213701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 5, 3].length) (baseStart_6213701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213701 prefixEnd_6213701 := by exact prefixLift 6213701
  have htrace : WordTrace (prefixWord ++ tailWord_6213701) baseStart_6213701 baseEnd_6213701 := by
    simpa [prefixWord, tailWord_6213701, baseEnd_6213701] using wordTrace_append hprefix tailTrace_6213701
  have hstable : (prefixWord ++ tailWord_6213701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213701).length < 2 ^ (prefixWord ++ tailWord_6213701).sum := by decide
  have hdescent : baseEnd_6213701 < baseStart_6213701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213702 : List Nat := [6, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2]
def baseStart_6213702 : Nat := 118140960795 + 6213702 * 2 ^ 59
def prefixEnd_6213702 : Nat := 4983230072969 + 3 ^ 40 * 6213702 * 2
def baseEnd_6213702 : Nat := 3190615769803753096048711

theorem tailTrace_6213702 : CollatzResearch.WordTrace tailWord_6213702 prefixEnd_6213702 3190615769803753096048711 := by
  unfold tailWord_6213702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7082260329213323270593855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 151088220356550896439335573 7082260329213323270593855)
  ·
    refine ⟨10623390493819984905890783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7082260329213323270593855 10623390493819984905890783)
    ·
      refine ⟨15935085740729977358836175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10623390493819984905890783 15935085740729977358836175)
      ·
        refine ⟨23902628611094966038254263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15935085740729977358836175 23902628611094966038254263)
        ·
          refine ⟨35853942916642449057381395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23902628611094966038254263 35853942916642449057381395)
          ·
            refine ⟨53780914374963673586072093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35853942916642449057381395 53780914374963673586072093)
            ·
              refine ⟨20167842890611377594777035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53780914374963673586072093 20167842890611377594777035)
              ·
                refine ⟨30251764335917066392165553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20167842890611377594777035 30251764335917066392165553)
                ·
                  refine ⟨22688823251937799794124165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30251764335917066392165553 22688823251937799794124165)
                  ·
                    refine ⟨4254154359738337461398281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22688823251937799794124165 4254154359738337461398281)
                    ·
                      refine ⟨3190615769803753096048711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4254154359738337461398281 3190615769803753096048711)
                      ·
                        rfl

theorem cell23_6213702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_6213702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213702 prefixEnd_6213702 := by exact prefixLift 6213702
  have htrace : WordTrace (prefixWord ++ tailWord_6213702) baseStart_6213702 baseEnd_6213702 := by
    simpa [prefixWord, tailWord_6213702, baseEnd_6213702] using wordTrace_append hprefix tailTrace_6213702
  have hstable : (prefixWord ++ tailWord_6213702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213702).length < 2 ^ (prefixWord ++ tailWord_6213702).sum := by decide
  have hdescent : baseEnd_6213702 < baseStart_6213702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213721 : List Nat := [1, 2, 1, 2, 2, 1, 3, 3, 3, 5]
def baseStart_6213721 : Nat := 118140960795 + 6213721 * 2 ^ 59
def prefixEnd_6213721 : Nat := 4983230072969 + 3 ^ 40 * 6213721 * 2
def baseEnd_6213721 : Nat := 1063541841978729507237041

theorem tailTrace_6213721 : CollatzResearch.WordTrace tailWord_6213721 prefixEnd_6213721 1063541841978729507237041 := by
  unfold tailWord_6213721
  simp only [CollatzResearch.WordTrace]
  refine ⟨226633023521757510903945017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151088682347838340602630011 226633023521757510903945017)
  ·
    refine ⟨169974767641318133177958763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226633023521757510903945017 169974767641318133177958763)
    ·
      refine ⟨254962151461977199766938145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169974767641318133177958763 254962151461977199766938145)
      ·
        refine ⟨191221613596482899825203609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254962151461977199766938145 191221613596482899825203609)
        ·
          refine ⟨143416210197362174868902707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191221613596482899825203609 143416210197362174868902707)
          ·
            refine ⟨215124315296043262303354061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143416210197362174868902707 215124315296043262303354061)
            ·
              refine ⟨80671618236016223363757773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215124315296043262303354061 80671618236016223363757773)
              ·
                refine ⟨30251856838506083761409165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80671618236016223363757773 30251856838506083761409165)
                ·
                  refine ⟨11344446314439781410528437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30251856838506083761409165 11344446314439781410528437)
                  ·
                    refine ⟨1063541841978729507237041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11344446314439781410528437 1063541841978729507237041)
                    ·
                      rfl

theorem cell23_6213721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 5].length) (baseStart_6213721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213721 prefixEnd_6213721 := by exact prefixLift 6213721
  have htrace : WordTrace (prefixWord ++ tailWord_6213721) baseStart_6213721 baseEnd_6213721 := by
    simpa [prefixWord, tailWord_6213721, baseEnd_6213721] using wordTrace_append hprefix tailTrace_6213721
  have hstable : (prefixWord ++ tailWord_6213721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213721).length < 2 ^ (prefixWord ++ tailWord_6213721).sum := by decide
  have hdescent : baseEnd_6213721 < baseStart_6213721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213778 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_6213778 : Nat := 118140960795 + 6213778 * 2 ^ 59
def prefixEnd_6213778 : Nat := 4983230072969 + 3 ^ 40 * 6213778 * 2
def baseEnd_6213778 : Nat := 3190654794333494798698361

theorem tailTrace_6213778 : CollatzResearch.WordTrace tailWord_6213778 prefixEnd_6213778 3190654794333494798698361 := by
  unfold tailWord_6213778
  simp only [CollatzResearch.WordTrace]
  refine ⟨56658775620637752409692497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151090068321700673092513325 56658775620637752409692497)
  ·
    refine ⟨42494081715478314307269373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56658775620637752409692497 42494081715478314307269373)
    ·
      refine ⟨15935280643304367865226015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42494081715478314307269373 15935280643304367865226015)
      ·
        refine ⟨23902920964956551797839023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15935280643304367865226015 23902920964956551797839023)
        ·
          refine ⟨35854381447434827696758535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23902920964956551797839023 35854381447434827696758535)
          ·
            refine ⟨53781572171152241545137803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35854381447434827696758535 53781572171152241545137803)
            ·
              refine ⟨80672358256728362317706705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53781572171152241545137803 80672358256728362317706705)
              ·
                refine ⟨60504268692546271738280029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80672358256728362317706705 60504268692546271738280029)
                ·
                  refine ⟨22689100759704851901855011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60504268692546271738280029 22689100759704851901855011)
                  ·
                    refine ⟨34033651139557277852782517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22689100759704851901855011 34033651139557277852782517)
                    ·
                      refine ⟨3190654794333494798698361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34033651139557277852782517 3190654794333494798698361)
                      ·
                        rfl

theorem cell23_6213778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_6213778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213778 prefixEnd_6213778 := by exact prefixLift 6213778
  have htrace : WordTrace (prefixWord ++ tailWord_6213778) baseStart_6213778 baseEnd_6213778 := by
    simpa [prefixWord, tailWord_6213778, baseEnd_6213778] using wordTrace_append hprefix tailTrace_6213778
  have hstable : (prefixWord ++ tailWord_6213778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213778).length < 2 ^ (prefixWord ++ tailWord_6213778).sum := by decide
  have hdescent : baseEnd_6213778 < baseStart_6213778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213781 : List Nat := [1, 3, 2, 1, 1, 1, 5, 9]
def baseStart_6213781 : Nat := 118140960795 + 6213781 * 2 ^ 59
def prefixEnd_6213781 : Nat := 4983230072969 + 3 ^ 40 * 6213781 * 2
def baseEnd_6213781 : Nat := 118172456843535492109661

theorem tailTrace_6213781 : CollatzResearch.WordTrace tailWord_6213781 prefixEnd_6213781 118172456843535492109661 := by
  unfold tailWord_6213781
  simp only [CollatzResearch.WordTrace]
  refine ⟨226635211901540141151129197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151090141267693427434086131 226635211901540141151129197)
  ·
    refine ⟨84988204463077552931673449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226635211901540141151129197 84988204463077552931673449)
    ·
      refine ⟨63741153347308164698755087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84988204463077552931673449 63741153347308164698755087)
      ·
        refine ⟨95611730020962247048132631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63741153347308164698755087 95611730020962247048132631)
        ·
          refine ⟨143417595031443370572198947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95611730020962247048132631 143417595031443370572198947)
          ·
            refine ⟨215126392547165055858298421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143417595031443370572198947 215126392547165055858298421)
            ·
              refine ⟨20168099301296723986715477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 215126392547165055858298421 20168099301296723986715477)
              ·
                refine ⟨118172456843535492109661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20168099301296723986715477 118172456843535492109661)
                ·
                  rfl

theorem cell23_6213781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 9].length) (baseStart_6213781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213781 prefixEnd_6213781 := by exact prefixLift 6213781
  have htrace : WordTrace (prefixWord ++ tailWord_6213781) baseStart_6213781 baseEnd_6213781 := by
    simpa [prefixWord, tailWord_6213781, baseEnd_6213781] using wordTrace_append hprefix tailTrace_6213781
  have hstable : (prefixWord ++ tailWord_6213781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213781).length < 2 ^ (prefixWord ++ tailWord_6213781).sum := by decide
  have hdescent : baseEnd_6213781 < baseStart_6213781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213786 : List Nat := [3, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3]
def baseStart_6213786 : Nat := 118140960795 + 6213786 * 2 ^ 59
def prefixEnd_6213786 : Nat := 4983230072969 + 3 ^ 40 * 6213786 * 2
def baseEnd_6213786 : Nat := 3190658902178730767398325

theorem tailTrace_6213786 : CollatzResearch.WordTrace tailWord_6213786 prefixEnd_6213786 3190658902178730767398325 := by
  unfold tailWord_6213786
  simp only [CollatzResearch.WordTrace]
  refine ⟨56658848566630506751265303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151090262844348018003374141 56658848566630506751265303)
  ·
    refine ⟨84988272849945760126897955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56658848566630506751265303 84988272849945760126897955)
    ·
      refine ⟨127482409274918640190346933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84988272849945760126897955 127482409274918640190346933)
      ·
        refine ⟨11951475869523622517845025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127482409274918640190346933 11951475869523622517845025)
        ·
          refine ⟨8963606902142716888383769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11951475869523622517845025 8963606902142716888383769)
          ·
            refine ⟨6722705176607037666287827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8963606902142716888383769 6722705176607037666287827)
            ·
              refine ⟨10084057764910556499431741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6722705176607037666287827 10084057764910556499431741)
              ·
                refine ⟨3781521661841458687286903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10084057764910556499431741 3781521661841458687286903)
                ·
                  refine ⟨5672282492762188030930355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3781521661841458687286903 5672282492762188030930355)
                  ·
                    refine ⟨8508423739143282046395533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5672282492762188030930355 8508423739143282046395533)
                    ·
                      refine ⟨3190658902178730767398325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8508423739143282046395533 3190658902178730767398325)
                      ·
                        rfl

theorem cell23_6213786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_6213786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213786 prefixEnd_6213786 := by exact prefixLift 6213786
  have htrace : WordTrace (prefixWord ++ tailWord_6213786) baseStart_6213786 baseEnd_6213786 := by
    simpa [prefixWord, tailWord_6213786, baseEnd_6213786] using wordTrace_append hprefix tailTrace_6213786
  have hstable : (prefixWord ++ tailWord_6213786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213786).length < 2 ^ (prefixWord ++ tailWord_6213786).sum := by decide
  have hdescent : baseEnd_6213786 < baseStart_6213786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213788 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_6213788 : Nat := 118140960795 + 6213788 * 2 ^ 59
def prefixEnd_6213788 : Nat := 4983230072969 + 3 ^ 40 * 6213788 * 2
def baseEnd_6213788 : Nat := 3190659929140039759573315

theorem tailTrace_6213788 : CollatzResearch.WordTrace tailWord_6213788 prefixEnd_6213788 3190659929140039759573315 := by
  unfold tailWord_6213788
  simp only [CollatzResearch.WordTrace]
  refine ⟨113317733606257390673317009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151090311475009854231089345 113317733606257390673317009)
  ·
    refine ⟨84988300204693043004987757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113317733606257390673317009 84988300204693043004987757)
    ·
      refine ⟨31870612576759891126870409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84988300204693043004987757 31870612576759891126870409)
      ·
        refine ⟨23902959432569918345152807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31870612576759891126870409 23902959432569918345152807)
        ·
          refine ⟨35854439148854877517729211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23902959432569918345152807 35854439148854877517729211)
          ·
            refine ⟨53781658723282316276593817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35854439148854877517729211 53781658723282316276593817)
            ·
              refine ⟨40336244042461737207445363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53781658723282316276593817 40336244042461737207445363)
              ·
                refine ⟨60504366063692605811168045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40336244042461737207445363 60504366063692605811168045)
                ·
                  refine ⟨22689137273884727179188017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60504366063692605811168045 22689137273884727179188017)
                  ·
                    refine ⟨17016852955413545384391013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22689137273884727179188017 17016852955413545384391013)
                    ·
                      refine ⟨3190659929140039759573315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17016852955413545384391013 3190659929140039759573315)
                      ·
                        rfl

theorem cell23_6213788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_6213788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213788 prefixEnd_6213788 := by exact prefixLift 6213788
  have htrace : WordTrace (prefixWord ++ tailWord_6213788) baseStart_6213788 baseEnd_6213788 := by
    simpa [prefixWord, tailWord_6213788, baseEnd_6213788] using wordTrace_append hprefix tailTrace_6213788
  have hstable : (prefixWord ++ tailWord_6213788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213788).length < 2 ^ (prefixWord ++ tailWord_6213788).sum := by decide
  have hdescent : baseEnd_6213788 < baseStart_6213788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213811 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 2, 7]
def baseStart_6213811 : Nat := 118140960795 + 6213811 * 2 ^ 59
def prefixEnd_6213811 : Nat := 4983230072969 + 3 ^ 40 * 6213811 * 2
def baseEnd_6213811 : Nat := 1063557246398364389861903

theorem tailTrace_6213811 : CollatzResearch.WordTrace tailWord_6213811 prefixEnd_6213811 1063557246398364389861903 := by
  unfold tailWord_6213811
  simp only [CollatzResearch.WordTrace]
  refine ⟨226636306091431456274721287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151090870727620970849814191 226636306091431456274721287)
  ·
    refine ⟨339954459137147184412081931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226636306091431456274721287 339954459137147184412081931)
    ·
      refine ⟨509931688705720776618122897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339954459137147184412081931 509931688705720776618122897)
      ·
        refine ⟨382448766529290582463592173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 509931688705720776618122897 382448766529290582463592173)
        ·
          refine ⟨143418287448483968423847065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 382448766529290582463592173 143418287448483968423847065)
          ·
            refine ⟨107563715586362976317885299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143418287448483968423847065 107563715586362976317885299)
            ·
              refine ⟨161345573379544464476827949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107563715586362976317885299 161345573379544464476827949)
              ·
                refine ⟨60504590017329174178810481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161345573379544464476827949 60504590017329174178810481)
                ·
                  refine ⟨45378442512996880634107861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60504590017329174178810481 45378442512996880634107861)
                  ·
                    refine ⟨1063557246398364389861903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45378442512996880634107861 1063557246398364389861903)
                    ·
                      rfl

theorem cell23_6213811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 7].length) (baseStart_6213811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213811 prefixEnd_6213811 := by exact prefixLift 6213811
  have htrace : WordTrace (prefixWord ++ tailWord_6213811) baseStart_6213811 baseEnd_6213811 := by
    simpa [prefixWord, tailWord_6213811, baseEnd_6213811] using wordTrace_append hprefix tailTrace_6213811
  have hstable : (prefixWord ++ tailWord_6213811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213811).length < 2 ^ (prefixWord ++ tailWord_6213811).sum := by decide
  have hdescent : baseEnd_6213811 < baseStart_6213811 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213826 : List Nat := [3, 5, 1, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_6213826 : Nat := 118140960795 + 6213826 * 2 ^ 59
def prefixEnd_6213826 : Nat := 4983230072969 + 3 ^ 40 * 6213826 * 2
def baseEnd_6213826 : Nat := 3190679441404910610898141

theorem tailTrace_6213826 : CollatzResearch.WordTrace tailWord_6213826 prefixEnd_6213826 3190679441404910610898141 := by
  unfold tailWord_6213826
  simp only [CollatzResearch.WordTrace]
  refine ⟨56659213296594278459129333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151091235457584742557678221 56659213296594278459129333)
  ·
    refine ⟨5311801246555713605543375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56659213296594278459129333 5311801246555713605543375)
    ·
      refine ⟨7967701869833570408315063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5311801246555713605543375 7967701869833570408315063)
      ·
        refine ⟨11951552804750355612472595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7967701869833570408315063 11951552804750355612472595)
        ·
          refine ⟨17927329207125533418708893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11951552804750355612472595 17927329207125533418708893)
          ·
            refine ⟨6722748452672075032015835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17927329207125533418708893 6722748452672075032015835)
            ·
              refine ⟨10084122679008112548023753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6722748452672075032015835 10084122679008112548023753)
              ·
                refine ⟨7563092009256084411017815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10084122679008112548023753 7563092009256084411017815)
                ·
                  refine ⟨11344638013884126616526723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7563092009256084411017815 11344638013884126616526723)
                  ·
                    refine ⟨17016957020826189924790085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11344638013884126616526723 17016957020826189924790085)
                    ·
                      refine ⟨3190679441404910610898141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17016957020826189924790085 3190679441404910610898141)
                      ·
                        rfl

theorem cell23_6213826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_6213826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213826 prefixEnd_6213826 := by exact prefixLift 6213826
  have htrace : WordTrace (prefixWord ++ tailWord_6213826) baseStart_6213826 baseEnd_6213826 := by
    simpa [prefixWord, tailWord_6213826, baseEnd_6213826] using wordTrace_append hprefix tailTrace_6213826
  have hstable : (prefixWord ++ tailWord_6213826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213826).length < 2 ^ (prefixWord ++ tailWord_6213826).sum := by decide
  have hdescent : baseEnd_6213826 < baseStart_6213826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213831 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 10]
def baseStart_6213831 : Nat := 118140960795 + 6213831 * 2 ^ 59
def prefixEnd_6213831 : Nat := 4983230072969 + 3 ^ 40 * 6213831 * 2
def baseEnd_6213831 : Nat := 3190682008808183091335617

theorem tailTrace_6213831 : CollatzResearch.WordTrace tailWord_6213831 prefixEnd_6213831 3190682008808183091335617 := by
  unfold tailWord_6213831
  simp only [CollatzResearch.WordTrace]
  refine ⟨226637035551358999690449347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151091357034239333126966231 226637035551358999690449347)
  ·
    refine ⟨339955553327038499535674021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226637035551358999690449347 339955553327038499535674021)
    ·
      refine ⟨63741666248819718662938879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 339955553327038499535674021 63741666248819718662938879)
      ·
        refine ⟨95612499373229577994408319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63741666248819718662938879 95612499373229577994408319)
        ·
          refine ⟨143418749059844366991612479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95612499373229577994408319 143418749059844366991612479)
          ·
            refine ⟨215128123589766550487418719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143418749059844366991612479 215128123589766550487418719)
            ·
              refine ⟨322692185384649825731128079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215128123589766550487418719 322692185384649825731128079)
              ·
                refine ⟨484038278076974738596692119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322692185384649825731128079 484038278076974738596692119)
                ·
                  refine ⟨726057417115462107895038179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 484038278076974738596692119 726057417115462107895038179)
                  ·
                    refine ⟨1089086125673193161842557269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 726057417115462107895038179 1089086125673193161842557269)
                    ·
                      refine ⟨3190682008808183091335617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1089086125673193161842557269 3190682008808183091335617)
                      ·
                        rfl

theorem cell23_6213831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_6213831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213831 prefixEnd_6213831 := by exact prefixLift 6213831
  have htrace : WordTrace (prefixWord ++ tailWord_6213831) baseStart_6213831 baseEnd_6213831 := by
    simpa [prefixWord, tailWord_6213831, baseEnd_6213831] using wordTrace_append hprefix tailTrace_6213831
  have hstable : (prefixWord ++ tailWord_6213831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213831).length < 2 ^ (prefixWord ++ tailWord_6213831).sum := by decide
  have hdescent : baseEnd_6213831 < baseStart_6213831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213835 : List Nat := [1, 1, 1, 1, 3, 2, 5, 1, 3, 3, 2]
def baseStart_6213835 : Nat := 118140960795 + 6213835 * 2 ^ 59
def prefixEnd_6213835 : Nat := 4983230072969 + 3 ^ 40 * 6213835 * 2
def baseEnd_6213835 : Nat := 3190684062730801075685599

theorem tailTrace_6213835 : CollatzResearch.WordTrace tailWord_6213835 prefixEnd_6213835 3190684062730801075685599 := by
  unfold tailWord_6213835
  simp only [CollatzResearch.WordTrace]
  refine ⟨226637181443344508373594959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151091454295563005582396639 226637181443344508373594959)
  ·
    refine ⟨339955772165016762560392439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226637181443344508373594959 339955772165016762560392439)
    ·
      refine ⟨509933658247525143840588659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339955772165016762560392439 509933658247525143840588659)
      ·
        refine ⟨764900487371287715760882989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509933658247525143840588659 764900487371287715760882989)
        ·
          refine ⟨286837682764232893410331121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 764900487371287715760882989 286837682764232893410331121)
          ·
            refine ⟨215128262073174670057748341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286837682764232893410331121 215128262073174670057748341)
            ·
              refine ⟨20168274569360125317913907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 215128262073174670057748341 20168274569360125317913907)
              ·
                refine ⟨30252411854040187976870861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20168274569360125317913907 30252411854040187976870861)
                ·
                  refine ⟨11344654445265070491326573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30252411854040187976870861 11344654445265070491326573)
                  ·
                    refine ⟨4254245416974401434247465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11344654445265070491326573 4254245416974401434247465)
                    ·
                      refine ⟨3190684062730801075685599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4254245416974401434247465 3190684062730801075685599)
                      ·
                        rfl

theorem cell23_6213835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 3, 2].length) (baseStart_6213835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213835 prefixEnd_6213835 := by exact prefixLift 6213835
  have htrace : WordTrace (prefixWord ++ tailWord_6213835) baseStart_6213835 baseEnd_6213835 := by
    simpa [prefixWord, tailWord_6213835, baseEnd_6213835] using wordTrace_append hprefix tailTrace_6213835
  have hstable : (prefixWord ++ tailWord_6213835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213835).length < 2 ^ (prefixWord ++ tailWord_6213835).sum := by decide
  have hdescent : baseEnd_6213835 < baseStart_6213835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213846 : List Nat := [5, 2, 1, 2, 1, 2, 3, 1, 1, 2, 3]
def baseStart_6213846 : Nat := 118140960795 + 6213846 * 2 ^ 59
def prefixEnd_6213846 : Nat := 4983230072969 + 3 ^ 40 * 6213846 * 2
def baseEnd_6213846 : Nat := 3190689711018000532648049

theorem tailTrace_6213846 : CollatzResearch.WordTrace tailWord_6213846 prefixEnd_6213846 3190689711018000532648049 := by
  unfold tailWord_6213846
  simp only [CollatzResearch.WordTrace]
  refine ⟨14164848915394041078265337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151091721764203104834830261 14164848915394041078265337)
  ·
    refine ⟨10623636686545530808699003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14164848915394041078265337 10623636686545530808699003)
    ·
      refine ⟨15935455029818296213048505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10623636686545530808699003 15935455029818296213048505)
      ·
        refine ⟨11951591272363722159786379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15935455029818296213048505 11951591272363722159786379)
        ·
          refine ⟨17927386908545583239679569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11951591272363722159786379 17927386908545583239679569)
          ·
            refine ⟨13445540181409187429759677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17927386908545583239679569 13445540181409187429759677)
            ·
              refine ⟨5042077568028445286159879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13445540181409187429759677 5042077568028445286159879)
              ·
                refine ⟨7563116352042667929239819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5042077568028445286159879 7563116352042667929239819)
                ·
                  refine ⟨11344674528064001893859729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7563116352042667929239819 11344674528064001893859729)
                  ·
                    refine ⟨8508505896048001420394797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11344674528064001893859729 8508505896048001420394797)
                    ·
                      refine ⟨3190689711018000532648049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8508505896048001420394797 3190689711018000532648049)
                      ·
                        rfl

theorem cell23_6213846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_6213846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213846 prefixEnd_6213846 := by exact prefixLift 6213846
  have htrace : WordTrace (prefixWord ++ tailWord_6213846) baseStart_6213846 baseEnd_6213846 := by
    simpa [prefixWord, tailWord_6213846, baseEnd_6213846] using wordTrace_append hprefix tailTrace_6213846
  have hstable : (prefixWord ++ tailWord_6213846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213846).length < 2 ^ (prefixWord ++ tailWord_6213846).sum := by decide
  have hdescent : baseEnd_6213846 < baseStart_6213846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213868 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 3]
def baseStart_6213868 : Nat := 118140960795 + 6213868 * 2 ^ 59
def prefixEnd_6213868 : Nat := 4983230072969 + 3 ^ 40 * 6213868 * 2
def baseEnd_6213868 : Nat := 3190701007592399446572947

theorem tailTrace_6213868 : CollatzResearch.WordTrace tailWord_6213868 prefixEnd_6213868 3190701007592399446572947 := by
  unfold tailWord_6213868
  simp only [CollatzResearch.WordTrace]
  refine ⟨113319192526112477504773129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151092256701483303339697505 113319192526112477504773129)
  ·
    refine ⟨84989394394584358128579847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113319192526112477504773129 84989394394584358128579847)
    ·
      refine ⟨127484091591876537192869771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84989394394584358128579847 127484091591876537192869771)
      ·
        refine ⟨191226137387814805789304657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127484091591876537192869771 191226137387814805789304657)
        ·
          refine ⟨143419603040861104341978493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191226137387814805789304657 143419603040861104341978493)
          ·
            refine ⟨53782351140322914128241935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143419603040861104341978493 53782351140322914128241935)
            ·
              refine ⟨80673526710484371192362903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53782351140322914128241935 80673526710484371192362903)
              ·
                refine ⟨121010290065726556788544355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80673526710484371192362903 121010290065726556788544355)
                ·
                  refine ⟨181515435098589835182816533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121010290065726556788544355 181515435098589835182816533)
                  ·
                    refine ⟨8508536020246398524194525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 181515435098589835182816533 8508536020246398524194525)
                    ·
                      refine ⟨3190701007592399446572947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8508536020246398524194525 3190701007592399446572947)
                      ·
                        rfl

theorem cell23_6213868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 3].length) (baseStart_6213868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213868 prefixEnd_6213868 := by exact prefixLift 6213868
  have htrace : WordTrace (prefixWord ++ tailWord_6213868) baseStart_6213868 baseEnd_6213868 := by
    simpa [prefixWord, tailWord_6213868, baseEnd_6213868] using wordTrace_append hprefix tailTrace_6213868
  have hstable : (prefixWord ++ tailWord_6213868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213868).length < 2 ^ (prefixWord ++ tailWord_6213868).sum := by decide
  have hdescent : baseEnd_6213868 < baseStart_6213868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213882 : List Nat := [3, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2]
def baseStart_6213882 : Nat := 118140960795 + 6213882 * 2 ^ 59
def prefixEnd_6213882 : Nat := 4983230072969 + 3 ^ 40 * 6213882 * 2
def baseEnd_6213882 : Nat := 3190708196321562391797883

theorem tailTrace_6213882 : CollatzResearch.WordTrace tailWord_6213882 prefixEnd_6213882 3190708196321562391797883 := by
  unfold tailWord_6213882
  simp only [CollatzResearch.WordTrace]
  refine ⟨56659723918543558850138975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151092597116116156933703933 56659723918543558850138975)
  ·
    refine ⟨84989585877815338275208463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56659723918543558850138975 84989585877815338275208463)
    ·
      refine ⟨127484378816723007412812695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84989585877815338275208463 127484378816723007412812695)
      ·
        refine ⟨191226568225084511119219043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127484378816723007412812695 191226568225084511119219043)
        ·
          refine ⟨286839852337626766678828565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191226568225084511119219043 286839852337626766678828565)
          ·
            refine ⟨13445618078326254688070089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 286839852337626766678828565 13445618078326254688070089)
            ·
              refine ⟨10084213558744691016052567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13445618078326254688070089 10084213558744691016052567)
              ·
                refine ⟨15126320338117036524078851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10084213558744691016052567 15126320338117036524078851)
                ·
                  refine ⟨22689480507175554786118277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15126320338117036524078851 22689480507175554786118277)
                  ·
                    refine ⟨4254277595095416522397177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22689480507175554786118277 4254277595095416522397177)
                    ·
                      refine ⟨3190708196321562391797883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4254277595095416522397177 3190708196321562391797883)
                      ·
                        rfl

theorem cell23_6213882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2].length) (baseStart_6213882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213882 prefixEnd_6213882 := by exact prefixLift 6213882
  have htrace : WordTrace (prefixWord ++ tailWord_6213882) baseStart_6213882 baseEnd_6213882 := by
    simpa [prefixWord, tailWord_6213882, baseEnd_6213882] using wordTrace_append hprefix tailTrace_6213882
  have hstable : (prefixWord ++ tailWord_6213882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213882).length < 2 ^ (prefixWord ++ tailWord_6213882).sum := by decide
  have hdescent : baseEnd_6213882 < baseStart_6213882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213905 : List Nat := [1, 2, 2, 1, 1, 5, 1, 5, 5]
def baseStart_6213905 : Nat := 118140960795 + 6213905 * 2 ^ 59
def prefixEnd_6213905 : Nat := 4983230072969 + 3 ^ 40 * 6213905 * 2
def baseEnd_6213905 : Nat := 354524445152957311312253

theorem tailTrace_6213905 : CollatzResearch.WordTrace tailWord_6213905 prefixEnd_6213905 354524445152957311312253 := by
  unfold tailWord_6213905
  simp only [CollatzResearch.WordTrace]
  refine ⟨226639734553090910328643169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151093156368727273552428779 226639734553090910328643169)
  ·
    refine ⟨169979800914818182746482377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226639734553090910328643169 169979800914818182746482377)
    ·
      refine ⟨127484850686113637059861783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169979800914818182746482377 127484850686113637059861783)
      ·
        refine ⟨191227276029170455589792675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127484850686113637059861783 191227276029170455589792675)
        ·
          refine ⟨286840914043755683384689013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191227276029170455589792675 286840914043755683384689013)
          ·
            refine ⟨26891335691602095317314595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 286840914043755683384689013 26891335691602095317314595)
            ·
              refine ⟨40337003537403142975971893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26891335691602095317314595 40337003537403142975971893)
              ·
                refine ⟨3781594081631544653997365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40337003537403142975971893 3781594081631544653997365)
                ·
                  refine ⟨354524445152957311312253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3781594081631544653997365 354524445152957311312253)
                  ·
                    rfl

theorem cell23_6213905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5, 5].length) (baseStart_6213905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213905 prefixEnd_6213905 := by exact prefixLift 6213905
  have htrace : WordTrace (prefixWord ++ tailWord_6213905) baseStart_6213905 baseEnd_6213905 := by
    simpa [prefixWord, tailWord_6213905, baseEnd_6213905] using wordTrace_append hprefix tailTrace_6213905
  have hstable : (prefixWord ++ tailWord_6213905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213905).length < 2 ^ (prefixWord ++ tailWord_6213905).sum := by decide
  have hdescent : baseEnd_6213905 < baseStart_6213905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213922 : List Nat := [3, 3, 1, 1, 3, 1, 2, 4, 5]
def baseStart_6213922 : Nat := 118140960795 + 6213922 * 2 ^ 59
def prefixEnd_6213922 : Nat := 4983230072969 + 3 ^ 40 * 6213922 * 2
def baseEnd_6213922 : Nat := 354525415060860248366411

theorem tailTrace_6213922 : CollatzResearch.WordTrace tailWord_6213922 prefixEnd_6213922 354525415060860248366411 := by
  unfold tailWord_6213922
  simp only [CollatzResearch.WordTrace]
  refine ⟨56660088648507330558003005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151093569729352881488008013 56660088648507330558003005)
  ·
    refine ⟨21247533243190248959251127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56660088648507330558003005 21247533243190248959251127)
    ·
      refine ⟨31871299864785373438876691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21247533243190248959251127 31871299864785373438876691)
      ·
        refine ⟨47806949797178060158315037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31871299864785373438876691 47806949797178060158315037)
        ·
          refine ⟨17927606173941772559368139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47806949797178060158315037 17927606173941772559368139)
          ·
            refine ⟨26891409260912658839052209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17927606173941772559368139 26891409260912658839052209)
            ·
              refine ⟨20168556945684494129289157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26891409260912658839052209 20168556945684494129289157)
              ·
                refine ⟨3781604427315842649241717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20168556945684494129289157 3781604427315842649241717)
                ·
                  refine ⟨354525415060860248366411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3781604427315842649241717 354525415060860248366411)
                  ·
                    rfl

theorem cell23_6213922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_6213922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213922 prefixEnd_6213922 := by exact prefixLift 6213922
  have htrace : WordTrace (prefixWord ++ tailWord_6213922) baseStart_6213922 baseEnd_6213922 := by
    simpa [prefixWord, tailWord_6213922, baseEnd_6213922] using wordTrace_append hprefix tailTrace_6213922
  have hstable : (prefixWord ++ tailWord_6213922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213922).length < 2 ^ (prefixWord ++ tailWord_6213922).sum := by decide
  have hdescent : baseEnd_6213922 < baseStart_6213922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213933 : List Nat := [1, 5, 3, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_6213933 : Nat := 118140960795 + 6213933 * 2 ^ 59
def prefixEnd_6213933 : Nat := 4983230072969 + 3 ^ 40 * 6213933 * 2
def baseEnd_6213933 : Nat := 3190734383834941692260149

theorem tailTrace_6213933 : CollatzResearch.WordTrace tailWord_6213933 prefixEnd_6213933 3190734383834941692260149 := by
  unfold tailWord_6213933
  simp only [CollatzResearch.WordTrace]
  refine ⟨226640755796989471110662453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151093837197992980740441635 226640755796989471110662453)
  ·
    refine ⟨21247570855967762916624605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 226640755796989471110662453 21247570855967762916624605)
    ·
      refine ⟨7967839070987911093734227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21247570855967762916624605 7967839070987911093734227)
      ·
        refine ⟨11951758606481866640601341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7967839070987911093734227 11951758606481866640601341)
        ·
          refine ⟨4481909477430699990225503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11951758606481866640601341 4481909477430699990225503)
          ·
            refine ⟨6722864216146049985338255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4481909477430699990225503 6722864216146049985338255)
            ·
              refine ⟨10084296324219074978007383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6722864216146049985338255 10084296324219074978007383)
              ·
                refine ⟨15126444486328612467011075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10084296324219074978007383 15126444486328612467011075)
                ·
                  refine ⟨22689666729492918700516613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15126444486328612467011075 22689666729492918700516613)
                  ·
                    refine ⟨4254312511779922256346865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22689666729492918700516613 4254312511779922256346865)
                    ·
                      refine ⟨3190734383834941692260149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4254312511779922256346865 3190734383834941692260149)
                      ·
                        rfl

theorem cell23_6213933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_6213933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213933 prefixEnd_6213933 := by exact prefixLift 6213933
  have htrace : WordTrace (prefixWord ++ tailWord_6213933) baseStart_6213933 baseEnd_6213933 := by
    simpa [prefixWord, tailWord_6213933, baseEnd_6213933] using wordTrace_append hprefix tailTrace_6213933
  have hstable : (prefixWord ++ tailWord_6213933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213933).length < 2 ^ (prefixWord ++ tailWord_6213933).sum := by decide
  have hdescent : baseEnd_6213933 < baseStart_6213933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213948 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 2, 8]
def baseStart_6213948 : Nat := 118140960795 + 6213948 * 2 ^ 59
def prefixEnd_6213948 : Nat := 4983230072969 + 3 ^ 40 * 6213948 * 2
def baseEnd_6213948 : Nat := 1063580695348253044524193

theorem tailTrace_6213948 : CollatzResearch.WordTrace tailWord_6213948 prefixEnd_6213948 1063580695348253044524193 := by
  unfold tailWord_6213948
  simp only [CollatzResearch.WordTrace]
  refine ⟨113320651445967564336229249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151094201927956752448305665 113320651445967564336229249)
  ·
    refine ⟨84990488584475673252171937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113320651445967564336229249 84990488584475673252171937)
    ·
      refine ⟨63742866438356754939128953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84990488584475673252171937 63742866438356754939128953)
      ·
        refine ⟨47807149828767566204346715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63742866438356754939128953 47807149828767566204346715)
        ·
          refine ⟨71710724743151349306520073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47807149828767566204346715 71710724743151349306520073)
          ·
            refine ⟨53783043557363511979890055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71710724743151349306520073 53783043557363511979890055)
            ·
              refine ⟨80674565336045267969835083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53783043557363511979890055 80674565336045267969835083)
              ·
                refine ⟨121011848004067901954752625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80674565336045267969835083 121011848004067901954752625)
                ·
                  refine ⟨90758886003050926466064469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121011848004067901954752625 90758886003050926466064469)
                  ·
                    refine ⟨1063580695348253044524193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90758886003050926466064469 1063580695348253044524193)
                    ·
                      rfl

theorem cell23_6213948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_6213948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213948 prefixEnd_6213948 := by exact prefixLift 6213948
  have htrace : WordTrace (prefixWord ++ tailWord_6213948) baseStart_6213948 baseEnd_6213948 := by
    simpa [prefixWord, tailWord_6213948, baseEnd_6213948] using wordTrace_append hprefix tailTrace_6213948
  have hstable : (prefixWord ++ tailWord_6213948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213948).length < 2 ^ (prefixWord ++ tailWord_6213948).sum := by decide
  have hdescent : baseEnd_6213948 < baseStart_6213948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213955 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 1, 6, 2]
def baseStart_6213955 : Nat := 118140960795 + 6213955 * 2 ^ 59
def prefixEnd_6213955 : Nat := 4983230072969 + 3 ^ 40 * 6213955 * 2
def baseEnd_6213955 : Nat := 3190745680409340606185047

theorem tailTrace_6213955 : CollatzResearch.WordTrace tailWord_6213955 prefixEnd_6213955 3190745680409340606185047 := by
  unfold tailWord_6213955
  simp only [CollatzResearch.WordTrace]
  refine ⟨226641558202909768867963319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151094372135273179245308879 226641558202909768867963319)
  ·
    refine ⟨339962337304364653301944979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226641558202909768867963319 339962337304364653301944979)
    ·
      refine ⟨509943505956546979952917469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339962337304364653301944979 509943505956546979952917469)
      ·
        refine ⟨191228814733705117482344051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 509943505956546979952917469 191228814733705117482344051)
        ·
          refine ⟨286843222100557676223516077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191228814733705117482344051 286843222100557676223516077)
          ·
            refine ⟨107566208287709128583818529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286843222100557676223516077 107566208287709128583818529)
            ·
              refine ⟨80674656215781846437863897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107566208287709128583818529 80674656215781846437863897)
              ·
                refine ⟨60505992161836384828397923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80674656215781846437863897 60505992161836384828397923)
                ·
                  refine ⟨90758988242754577242596885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60505992161836384828397923 90758988242754577242596885)
                  ·
                    refine ⟨4254327573879120808246729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90758988242754577242596885 4254327573879120808246729)
                    ·
                      refine ⟨3190745680409340606185047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4254327573879120808246729 3190745680409340606185047)
                      ·
                        rfl

theorem cell23_6213955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 6, 2].length) (baseStart_6213955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213955 prefixEnd_6213955 := by exact prefixLift 6213955
  have htrace : WordTrace (prefixWord ++ tailWord_6213955) baseStart_6213955 baseEnd_6213955 := by
    simpa [prefixWord, tailWord_6213955, baseEnd_6213955] using wordTrace_append hprefix tailTrace_6213955
  have hstable : (prefixWord ++ tailWord_6213955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213955).length < 2 ^ (prefixWord ++ tailWord_6213955).sum := by decide
  have hdescent : baseEnd_6213955 < baseStart_6213955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213956 : List Nat := [2, 3, 4, 1, 2, 2, 1, 3, 5]
def baseStart_6213956 : Nat := 118140960795 + 6213956 * 2 ^ 59
def prefixEnd_6213956 : Nat := 4983230072969 + 3 ^ 40 * 6213956 * 2
def baseEnd_6213956 : Nat := 354527354876666122474727

theorem tailTrace_6213956 : CollatzResearch.WordTrace tailWord_6213956 prefixEnd_6213956 354527354876666122474727 := by
  unfold tailWord_6213956
  simp only [CollatzResearch.WordTrace]
  refine ⟨113320797337953073019374861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151094396450604097359166481 113320797337953073019374861)
  ·
    refine ⟨42495299001732402382265573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113320797337953073019374861 42495299001732402382265573)
    ·
      refine ⟨7967868562824825446674795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42495299001732402382265573 7967868562824825446674795)
      ·
        refine ⟨11951802844237238170012193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7967868562824825446674795 11951802844237238170012193)
        ·
          refine ⟨8963852133177928627509145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11951802844237238170012193 8963852133177928627509145)
          ·
            refine ⟨6722889099883446470631859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8963852133177928627509145 6722889099883446470631859)
            ·
              refine ⟨10084333649825169705947789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6722889099883446470631859 10084333649825169705947789)
              ·
                refine ⟨3781625118684438639730421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10084333649825169705947789 3781625118684438639730421)
                ·
                  refine ⟨354527354876666122474727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3781625118684438639730421 354527354876666122474727)
                  ·
                    rfl

theorem cell23_6213956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3, 5].length) (baseStart_6213956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213956 prefixEnd_6213956 := by exact prefixLift 6213956
  have htrace : WordTrace (prefixWord ++ tailWord_6213956) baseStart_6213956 baseEnd_6213956 := by
    simpa [prefixWord, tailWord_6213956, baseEnd_6213956] using wordTrace_append hprefix tailTrace_6213956
  have hstable : (prefixWord ++ tailWord_6213956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213956).length < 2 ^ (prefixWord ++ tailWord_6213956).sum := by decide
  have hdescent : baseEnd_6213956 < baseStart_6213956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6213972 : List Nat := [2, 4, 1, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_6213972 : Nat := 118140960795 + 6213972 * 2 ^ 59
def prefixEnd_6213972 : Nat := 4983230072969 + 3 ^ 40 * 6213972 * 2
def baseEnd_6213972 : Nat := 3190754409580467039672469

theorem tailTrace_6213972 : CollatzResearch.WordTrace tailWord_6213972 prefixEnd_6213972 3190754409580467039672469 := by
  unfold tailWord_6213972
  simp only [CollatzResearch.WordTrace]
  refine ⟨113321089121924090385666085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151094785495898787180888113 113321089121924090385666085)
  ·
    refine ⟨21247704210360766947312391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113321089121924090385666085 21247704210360766947312391)
    ·
      refine ⟨31871556315541150420968587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21247704210360766947312391 31871556315541150420968587)
      ·
        refine ⟨47807334473311725631452881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31871556315541150420968587 47807334473311725631452881)
        ·
          refine ⟨35855500854983794223589661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47807334473311725631452881 35855500854983794223589661)
          ·
            refine ⟨13445812820618922833846123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35855500854983794223589661 13445812820618922833846123)
            ·
              refine ⟨20168719230928384250769185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13445812820618922833846123 20168719230928384250769185)
              ·
                refine ⟨15126539423196288188076889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20168719230928384250769185 15126539423196288188076889)
                ·
                  refine ⟨11344904567397216141057667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15126539423196288188076889 11344904567397216141057667)
                  ·
                    refine ⟨17017356851095824211586501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11344904567397216141057667 17017356851095824211586501)
                    ·
                      refine ⟨3190754409580467039672469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17017356851095824211586501 3190754409580467039672469)
                      ·
                        rfl

theorem cell23_6213972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_6213972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6213972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6213972 prefixEnd_6213972 := by exact prefixLift 6213972
  have htrace : WordTrace (prefixWord ++ tailWord_6213972) baseStart_6213972 baseEnd_6213972 := by
    simpa [prefixWord, tailWord_6213972, baseEnd_6213972] using wordTrace_append hprefix tailTrace_6213972
  have hstable : (prefixWord ++ tailWord_6213972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6213972).length < 2 ^ (prefixWord ++ tailWord_6213972).sum := by decide
  have hdescent : baseEnd_6213972 < baseStart_6213972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6213972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214006 : List Nat := [5, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4]
def baseStart_6214006 : Nat := 118140960795 + 6214006 * 2 ^ 59
def prefixEnd_6214006 : Nat := 4983230072969 + 3 ^ 40 * 6214006 * 2
def baseEnd_6214006 : Nat := 3190771867922719906647313

theorem tailTrace_6214006 : CollatzResearch.WordTrace tailWord_6214006 prefixEnd_6214006 3190771867922719906647313 := by
  unfold tailWord_6214006
  simp only [CollatzResearch.WordTrace]
  refine ⟨14165213645357812786129367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151095612217150003052046581 14165213645357812786129367)
  ·
    refine ⟨21247820468036719179194051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14165213645357812786129367 21247820468036719179194051)
    ·
      refine ⟨31871730702055078768791077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21247820468036719179194051 31871730702055078768791077)
      ·
        refine ⟨5975949506635327269148327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31871730702055078768791077 5975949506635327269148327)
        ·
          refine ⟨8963924259952990903722491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5975949506635327269148327 8963924259952990903722491)
          ·
            refine ⟨13445886389929486355583737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8963924259952990903722491 13445886389929486355583737)
            ·
              refine ⟨10084414792447114766687803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13445886389929486355583737 10084414792447114766687803)
              ·
                refine ⟨15126622188670672150031705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10084414792447114766687803 15126622188670672150031705)
                ·
                  refine ⟨11344966641503004112523779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15126622188670672150031705 11344966641503004112523779)
                  ·
                    refine ⟨17017449962254506168785669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11344966641503004112523779 17017449962254506168785669)
                    ·
                      refine ⟨3190771867922719906647313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17017449962254506168785669 3190771867922719906647313)
                      ·
                        rfl

theorem cell23_6214006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_6214006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214006 prefixEnd_6214006 := by exact prefixLift 6214006
  have htrace : WordTrace (prefixWord ++ tailWord_6214006) baseStart_6214006 baseEnd_6214006 := by
    simpa [prefixWord, tailWord_6214006, baseEnd_6214006] using wordTrace_append hprefix tailTrace_6214006
  have hstable : (prefixWord ++ tailWord_6214006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214006).length < 2 ^ (prefixWord ++ tailWord_6214006).sum := by decide
  have hdescent : baseEnd_6214006 < baseStart_6214006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214056 : List Nat := [2, 1, 6, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_6214056 : Nat := 118140960795 + 6214056 * 2 ^ 59
def prefixEnd_6214056 : Nat := 4983230072969 + 3 ^ 40 * 6214056 * 2
def baseEnd_6214056 : Nat := 3190797541955444711022083

theorem tailTrace_6214056 : CollatzResearch.WordTrace tailWord_6214056 prefixEnd_6214056 3190797541955444711022083 := by
  unfold tailWord_6214056
  simp only [CollatzResearch.WordTrace]
  refine ⟨113322620987771931558695011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151096827983695908744926681 113322620987771931558695011)
  ·
    refine ⟨169983931481657897338042517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113322620987771931558695011 169983931481657897338042517)
    ·
      refine ⟨7967996788202713937720743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 169983931481657897338042517 7967996788202713937720743)
      ·
        refine ⟨11951995182304070906581115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7967996788202713937720743 11951995182304070906581115)
        ·
          refine ⟨17927992773456106359871673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11951995182304070906581115 17927992773456106359871673)
          ·
            refine ⟨13445994580092079769903755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17927992773456106359871673 13445994580092079769903755)
            ·
              refine ⟨20168991870138119654855633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13445994580092079769903755 20168991870138119654855633)
              ·
                refine ⟨15126743902603589741141725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20168991870138119654855633 15126743902603589741141725)
                ·
                  refine ⟨5672528963476346152928147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15126743902603589741141725 5672528963476346152928147)
                  ·
                    refine ⟨8508793445214519229392221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5672528963476346152928147 8508793445214519229392221)
                    ·
                      refine ⟨3190797541955444711022083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8508793445214519229392221 3190797541955444711022083)
                      ·
                        rfl

theorem cell23_6214056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_6214056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214056 prefixEnd_6214056 := by exact prefixLift 6214056
  have htrace : WordTrace (prefixWord ++ tailWord_6214056) baseStart_6214056 baseEnd_6214056 := by
    simpa [prefixWord, tailWord_6214056, baseEnd_6214056] using wordTrace_append hprefix tailTrace_6214056
  have hstable : (prefixWord ++ tailWord_6214056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214056).length < 2 ^ (prefixWord ++ tailWord_6214056).sum := by decide
  have hdescent : baseEnd_6214056 < baseStart_6214056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214076 : List Nat := [2, 2, 2, 4, 1, 3, 2, 1, 1, 5]
def baseStart_6214076 : Nat := 118140960795 + 6214076 * 2 ^ 59
def prefixEnd_6214076 : Nat := 4983230072969 + 3 ^ 40 * 6214076 * 2
def baseEnd_6214076 : Nat := 1063602603856178210923997

theorem tailTrace_6214076 : CollatzResearch.WordTrace tailWord_6214076 prefixEnd_6214076 1063602603856178210923997 := by
  unfold tailWord_6214076
  simp only [CollatzResearch.WordTrace]
  refine ⟨113322985717735703266559041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151097314290314271022078721 113322985717735703266559041)
  ·
    refine ⟨84992239288301777449919281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113322985717735703266559041 84992239288301777449919281)
    ·
      refine ⟨63744179466226333087439461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84992239288301777449919281 63744179466226333087439461)
      ·
        refine ⟨11952033649917437453894899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63744179466226333087439461 11952033649917437453894899)
        ·
          refine ⟨17928050474876156180842349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11952033649917437453894899 17928050474876156180842349)
          ·
            refine ⟨6723018928078558567815881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17928050474876156180842349 6723018928078558567815881)
            ·
              refine ⟨5042264196058918925861911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6723018928078558567815881 5042264196058918925861911)
              ·
                refine ⟨7563396294088378388792867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5042264196058918925861911 7563396294088378388792867)
                ·
                  refine ⟨11345094441132567583189301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7563396294088378388792867 11345094441132567583189301)
                  ·
                    refine ⟨1063602603856178210923997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11345094441132567583189301 1063602603856178210923997)
                    ·
                      rfl

theorem cell23_6214076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_6214076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214076 prefixEnd_6214076 := by exact prefixLift 6214076
  have htrace : WordTrace (prefixWord ++ tailWord_6214076) baseStart_6214076 baseEnd_6214076 := by
    simpa [prefixWord, tailWord_6214076, baseEnd_6214076] using wordTrace_append hprefix tailTrace_6214076
  have hstable : (prefixWord ++ tailWord_6214076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214076).length < 2 ^ (prefixWord ++ tailWord_6214076).sum := by decide
  have hdescent : baseEnd_6214076 < baseStart_6214076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214102 : List Nat := [5, 2, 1, 1, 1, 1, 2, 10]
def baseStart_6214102 : Nat := 118140960795 + 6214102 * 2 ^ 59
def prefixEnd_6214102 : Nat := 4983230072969 + 3 ^ 40 * 6214102 * 2
def baseEnd_6214102 : Nat := 118178561557983390038773

theorem tailTrace_6214102 : CollatzResearch.WordTrace tailWord_6214102 prefixEnd_6214102 118178561557983390038773 := by
  unfold tailWord_6214102
  simp only [CollatzResearch.WordTrace]
  refine ⟨14165432483336075810847785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151097946488918141982376373 14165432483336075810847785)
  ·
    refine ⟨10624074362502056858135839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14165432483336075810847785 10624074362502056858135839)
    ·
      refine ⟨15936111543753085287203759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10624074362502056858135839 15936111543753085287203759)
      ·
        refine ⟨23904167315629627930805639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15936111543753085287203759 23904167315629627930805639)
        ·
          refine ⟨35856250973444441896208459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23904167315629627930805639 35856250973444441896208459)
          ·
            refine ⟨53784376460166662844312689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35856250973444441896208459 53784376460166662844312689)
            ·
              refine ⟨40338282345124997133234517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53784376460166662844312689 40338282345124997133234517)
              ·
                refine ⟨118178561557983390038773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40338282345124997133234517 118178561557983390038773)
                ·
                  rfl

theorem cell23_6214102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_6214102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214102 prefixEnd_6214102 := by exact prefixLift 6214102
  have htrace : WordTrace (prefixWord ++ tailWord_6214102) baseStart_6214102 baseEnd_6214102 := by
    simpa [prefixWord, tailWord_6214102, baseEnd_6214102] using wordTrace_append hprefix tailTrace_6214102
  have hstable : (prefixWord ++ tailWord_6214102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214102).length < 2 ^ (prefixWord ++ tailWord_6214102).sum := by decide
  have hdescent : baseEnd_6214102 < baseStart_6214102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214172 : List Nat := [2, 2, 3, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_6214172 : Nat := 118140960795 + 6214172 * 2 ^ 59
def prefixEnd_6214172 : Nat := 4983230072969 + 3 ^ 40 * 6214172 * 2
def baseEnd_6214172 : Nat := 3190857105711366257171549

theorem tailTrace_6214172 : CollatzResearch.WordTrace tailWord_6214172 prefixEnd_6214172 3190857105711366257171549 := by
  unfold tailWord_6214172
  simp only [CollatzResearch.WordTrace]
  refine ⟨113324736421561807464306385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151099648562082409952408513 113324736421561807464306385)
  ·
    refine ⟨84993552316171355598229789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113324736421561807464306385 84993552316171355598229789)
    ·
      refine ⟨31872582118564258349336171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84993552316171355598229789 31872582118564258349336171)
      ·
        refine ⟨47808873177846387524004257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31872582118564258349336171 47808873177846387524004257)
        ·
          refine ⟨35856654883384790643003193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47808873177846387524004257 35856654883384790643003193)
          ·
            refine ⟨26892491162538592982252395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35856654883384790643003193 26892491162538592982252395)
            ·
              refine ⟨40338736743807889473378593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26892491162538592982252395 40338736743807889473378593)
              ·
                refine ⟨30254052557855917105033945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40338736743807889473378593 30254052557855917105033945)
                ·
                  refine ⟨22690539418391937828775459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30254052557855917105033945 22690539418391937828775459)
                  ·
                    refine ⟨34035809127587906743163189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22690539418391937828775459 34035809127587906743163189)
                    ·
                      refine ⟨3190857105711366257171549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34035809127587906743163189 3190857105711366257171549)
                      ·
                        rfl

theorem cell23_6214172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_6214172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214172 prefixEnd_6214172 := by exact prefixLift 6214172
  have htrace : WordTrace (prefixWord ++ tailWord_6214172) baseStart_6214172 baseEnd_6214172 := by
    simpa [prefixWord, tailWord_6214172, baseEnd_6214172] using wordTrace_append hprefix tailTrace_6214172
  have hstable : (prefixWord ++ tailWord_6214172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214172).length < 2 ^ (prefixWord ++ tailWord_6214172).sum := by decide
  have hdescent : baseEnd_6214172 < baseStart_6214172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214173 : List Nat := [1, 4, 2, 2, 1, 4, 1, 2, 1, 3, 2]
def baseStart_6214173 : Nat := 118140960795 + 6214173 * 2 ^ 59
def prefixEnd_6214173 : Nat := 4983230072969 + 3 ^ 40 * 6214173 * 2
def baseEnd_6214173 : Nat := 3190857619192020753259045

theorem tailTrace_6214173 : CollatzResearch.WordTrace tailWord_6214173 prefixEnd_6214173 3190857619192020753259045 := by
  unfold tailWord_6214173
  simp only [CollatzResearch.WordTrace]
  refine ⟨226649509316119992099399173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151099672877413328066266115 226649509316119992099399173)
  ·
    refine ⟨42496782996772498518637345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226649509316119992099399173 42496782996772498518637345)
    ·
      refine ⟨31872587247579373888978009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42496782996772498518637345 31872587247579373888978009)
      ·
        refine ⟨23904440435684530416733507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31872587247579373888978009 23904440435684530416733507)
        ·
          refine ⟨35856660653526795625100261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23904440435684530416733507 35856660653526795625100261)
          ·
            refine ⟨6723123872536274179706299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35856660653526795625100261 6723123872536274179706299)
            ·
              refine ⟨10084685808804411269559449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6723123872536274179706299 10084685808804411269559449)
              ·
                refine ⟨7563514356603308452169587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10084685808804411269559449 7563514356603308452169587)
                ·
                  refine ⟨11345271534904962678254381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7563514356603308452169587 11345271534904962678254381)
                  ·
                    refine ⟨4254476825589361004345393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11345271534904962678254381 4254476825589361004345393)
                    ·
                      refine ⟨3190857619192020753259045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4254476825589361004345393 3190857619192020753259045)
                      ·
                        rfl

theorem cell23_6214173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_6214173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214173 prefixEnd_6214173 := by exact prefixLift 6214173
  have htrace : WordTrace (prefixWord ++ tailWord_6214173) baseStart_6214173 baseEnd_6214173 := by
    simpa [prefixWord, tailWord_6214173, baseEnd_6214173] using wordTrace_append hprefix tailTrace_6214173
  have hstable : (prefixWord ++ tailWord_6214173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214173).length < 2 ^ (prefixWord ++ tailWord_6214173).sum := by decide
  have hdescent : baseEnd_6214173 < baseStart_6214173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214175 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 9]
def baseStart_6214175 : Nat := 118140960795 + 6214175 * 2 ^ 59
def prefixEnd_6214175 : Nat := 4983230072969 + 3 ^ 40 * 6214175 * 2
def baseEnd_6214175 : Nat := 354539849572592193937115

theorem tailTrace_6214175 : CollatzResearch.WordTrace tailWord_6214175 prefixEnd_6214175 354539849572592193937115 := by
  unfold tailWord_6214175
  simp only [CollatzResearch.WordTrace]
  refine ⟨226649582262112746440971979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151099721508075164293981319 226649582262112746440971979)
  ·
    refine ⟨339974373393169119661457969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226649582262112746440971979 339974373393169119661457969)
    ·
      refine ⟨254980780044876839746093477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339974373393169119661457969 254980780044876839746093477)
      ·
        refine ⟨47808896258414407452392527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254980780044876839746093477 47808896258414407452392527)
        ·
          refine ⟨71713344387621611178588791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47808896258414407452392527 71713344387621611178588791)
          ·
            refine ⟨107570016581432416767883187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71713344387621611178588791 107570016581432416767883187)
            ·
              refine ⟨161355024872148625151824781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107570016581432416767883187 161355024872148625151824781)
              ·
                refine ⟨60508134327055734431934293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161355024872148625151824781 60508134327055734431934293)
                ·
                  refine ⟨354539849572592193937115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60508134327055734431934293 354539849572592193937115)
                  ·
                    rfl

theorem cell23_6214175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 9].length) (baseStart_6214175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214175 prefixEnd_6214175 := by exact prefixLift 6214175
  have htrace : WordTrace (prefixWord ++ tailWord_6214175) baseStart_6214175 baseEnd_6214175 := by
    simpa [prefixWord, tailWord_6214175, baseEnd_6214175] using wordTrace_append hprefix tailTrace_6214175
  have hstable : (prefixWord ++ tailWord_6214175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214175).length < 2 ^ (prefixWord ++ tailWord_6214175).sum := by decide
  have hdescent : baseEnd_6214175 < baseStart_6214175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214186 : List Nat := [3, 1, 4, 1, 1, 3, 1, 2, 1, 4, 2]
def baseStart_6214186 : Nat := 118140960795 + 6214186 * 2 ^ 59
def prefixEnd_6214186 : Nat := 4983230072969 + 3 ^ 40 * 6214186 * 2
def baseEnd_6214186 : Nat := 3190864294440529202396485

theorem tailTrace_6214186 : CollatzResearch.WordTrace tailWord_6214186 prefixEnd_6214186 3190864294440529202396485 := by
  unfold tailWord_6214186
  simp only [CollatzResearch.WordTrace]
  refine ⟨56662495866268223829905603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151099988976715263546414941 56662495866268223829905603)
  ·
    refine ⟨84993743799402335744858405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56662495866268223829905603 84993743799402335744858405)
    ·
      refine ⟨15936326962387937952160951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84993743799402335744858405 15936326962387937952160951)
      ·
        refine ⟨23904490443581906928241427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15936326962387937952160951 23904490443581906928241427)
        ·
          refine ⟨35856735665372860392362141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23904490443581906928241427 35856735665372860392362141)
          ·
            refine ⟨13446275874514822647135803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35856735665372860392362141 13446275874514822647135803)
            ·
              refine ⟨20169413811772233970703705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13446275874514822647135803 20169413811772233970703705)
              ·
                refine ⟨15127060358829175478027779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20169413811772233970703705 15127060358829175478027779)
                ·
                  refine ⟨22690590538243763217041669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15127060358829175478027779 22690590538243763217041669)
                  ·
                    refine ⟨4254485725920705603195313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22690590538243763217041669 4254485725920705603195313)
                    ·
                      refine ⟨3190864294440529202396485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4254485725920705603195313 3190864294440529202396485)
                      ·
                        rfl

theorem cell23_6214186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_6214186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214186 prefixEnd_6214186 := by exact prefixLift 6214186
  have htrace : WordTrace (prefixWord ++ tailWord_6214186) baseStart_6214186 baseEnd_6214186 := by
    simpa [prefixWord, tailWord_6214186, baseEnd_6214186] using wordTrace_append hprefix tailTrace_6214186
  have hstable : (prefixWord ++ tailWord_6214186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214186).length < 2 ^ (prefixWord ++ tailWord_6214186).sum := by decide
  have hdescent : baseEnd_6214186 < baseStart_6214186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214190 : List Nat := [4, 1, 3, 1, 3, 1, 3, 1, 1, 3, 2]
def baseStart_6214190 : Nat := 118140960795 + 6214190 * 2 ^ 59
def prefixEnd_6214190 : Nat := 4983230072969 + 3 ^ 40 * 6214190 * 2
def baseEnd_6214190 : Nat := 3190866348363147186746467

theorem tailTrace_6214190 : CollatzResearch.WordTrace tailWord_6214190 prefixEnd_6214190 3190866348363147186746467 := by
  unfold tailWord_6214190
  simp only [CollatzResearch.WordTrace]
  refine ⟨28331266169632300500346003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151100086238038936001845349 28331266169632300500346003)
  ·
    refine ⟨42496899254448450750519005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28331266169632300500346003 42496899254448450750519005)
    ·
      refine ⟨15936337220418169031444627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42496899254448450750519005 15936337220418169031444627)
      ·
        refine ⟨23904505830627253547166941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15936337220418169031444627 23904505830627253547166941)
        ·
          refine ⟨8964189686485220080187603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23904505830627253547166941 8964189686485220080187603)
          ·
            refine ⟨13446284529727830120281405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8964189686485220080187603 13446284529727830120281405)
            ·
              refine ⟨5042356698647936295105527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13446284529727830120281405 5042356698647936295105527)
              ·
                refine ⟨7563535047971904442658291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5042356698647936295105527 7563535047971904442658291)
                ·
                  refine ⟨11345302571957856663987437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7563535047971904442658291 11345302571957856663987437)
                  ·
                    refine ⟨4254488464484196248995289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11345302571957856663987437 4254488464484196248995289)
                    ·
                      refine ⟨3190866348363147186746467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4254488464484196248995289 3190866348363147186746467)
                      ·
                        rfl

theorem cell23_6214190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_6214190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214190 prefixEnd_6214190 := by exact prefixLift 6214190
  have htrace : WordTrace (prefixWord ++ tailWord_6214190) baseStart_6214190 baseEnd_6214190 := by
    simpa [prefixWord, tailWord_6214190, baseEnd_6214190] using wordTrace_append hprefix tailTrace_6214190
  have hstable : (prefixWord ++ tailWord_6214190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214190).length < 2 ^ (prefixWord ++ tailWord_6214190).sum := by decide
  have hdescent : baseEnd_6214190 < baseStart_6214190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214222 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 4, 5]
def baseStart_6214222 : Nat := 118140960795 + 6214222 * 2 ^ 59
def prefixEnd_6214222 : Nat := 4983230072969 + 3 ^ 40 * 6214222 * 2
def baseEnd_6214222 : Nat := 1063627593248030353848773

theorem tailTrace_6214222 : CollatzResearch.WordTrace tailWord_6214222 prefixEnd_6214222 1063627593248030353848773 := by
  unfold tailWord_6214222
  simp only [CollatzResearch.WordTrace]
  refine ⟨28331412061617809183491615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151100864328628315645288613 28331412061617809183491615)
  ·
    refine ⟨42497118092426713775237423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28331412061617809183491615 42497118092426713775237423)
    ·
      refine ⟨63745677138640070662856135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42497118092426713775237423 63745677138640070662856135)
      ·
        refine ⟨95618515707960105994284203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63745677138640070662856135 95618515707960105994284203)
        ·
          refine ⟨143427773561940158991426305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95618515707960105994284203 143427773561940158991426305)
          ·
            refine ⟨107570830171455119243569729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143427773561940158991426305 107570830171455119243569729)
            ·
              refine ⟨80678122628591339432677297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107570830171455119243569729 80678122628591339432677297)
              ·
                refine ⟨60508591971443504574507973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80678122628591339432677297 60508591971443504574507973)
                ·
                  refine ⟨11345360994645657107720245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60508591971443504574507973 11345360994645657107720245)
                  ·
                    refine ⟨1063627593248030353848773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11345360994645657107720245 1063627593248030353848773)
                    ·
                      rfl

theorem cell23_6214222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_6214222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214222 prefixEnd_6214222 := by exact prefixLift 6214222
  have htrace : WordTrace (prefixWord ++ tailWord_6214222) baseStart_6214222 baseEnd_6214222 := by
    simpa [prefixWord, tailWord_6214222, baseEnd_6214222] using wordTrace_append hprefix tailTrace_6214222
  have hstable : (prefixWord ++ tailWord_6214222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214222).length < 2 ^ (prefixWord ++ tailWord_6214222).sum := by decide
  have hdescent : baseEnd_6214222 < baseStart_6214222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214276 : List Nat := [2, 3, 2, 1, 3, 1, 2, 1, 2, 4, 2]
def baseStart_6214276 : Nat := 118140960795 + 6214276 * 2 ^ 59
def prefixEnd_6214276 : Nat := 4983230072969 + 3 ^ 40 * 6214276 * 2
def baseEnd_6214276 : Nat := 3190910507699433850271071

theorem tailTrace_6214276 : CollatzResearch.WordTrace tailWord_6214276 prefixEnd_6214276 3190910507699433850271071 := by
  unfold tailWord_6214276
  simp only [CollatzResearch.WordTrace]
  refine ⟨113326633017373420345199341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151102177356497893793599121 113326633017373420345199341)
  ·
    refine ⟨42497487381515032629449753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113326633017373420345199341 42497487381515032629449753)
    ·
      refine ⟨31873115536136274472087315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42497487381515032629449753 31873115536136274472087315)
      ·
        refine ⟨47809673304204411708130973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31873115536136274472087315 47809673304204411708130973)
        ·
          refine ⟨17928627489076654390549115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47809673304204411708130973 17928627489076654390549115)
          ·
            refine ⟨26892941233614981585823673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17928627489076654390549115 26892941233614981585823673)
            ·
              refine ⟨20169705925211236189367755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26892941233614981585823673 20169705925211236189367755)
              ·
                refine ⟨30254558887816854284051633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20169705925211236189367755 30254558887816854284051633)
                ·
                  refine ⟨22690919165862640713038725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30254558887816854284051633 22690919165862640713038725)
                  ·
                    refine ⟨4254547343599245133694761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22690919165862640713038725 4254547343599245133694761)
                    ·
                      refine ⟨3190910507699433850271071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4254547343599245133694761 3190910507699433850271071)
                      ·
                        rfl

theorem cell23_6214276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_6214276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214276 prefixEnd_6214276 := by exact prefixLift 6214276
  have htrace : WordTrace (prefixWord ++ tailWord_6214276) baseStart_6214276 baseEnd_6214276 := by
    simpa [prefixWord, tailWord_6214276, baseEnd_6214276] using wordTrace_append hprefix tailTrace_6214276
  have hstable : (prefixWord ++ tailWord_6214276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214276).length < 2 ^ (prefixWord ++ tailWord_6214276).sum := by decide
  have hdescent : baseEnd_6214276 < baseStart_6214276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214322 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7]
def baseStart_6214322 : Nat := 118140960795 + 6214322 * 2 ^ 59
def prefixEnd_6214322 : Nat := 4983230072969 + 3 ^ 40 * 6214322 * 2
def baseEnd_6214322 : Nat := 3190934127809540670295859

theorem tailTrace_6214322 : CollatzResearch.WordTrace tailWord_6214322 prefixEnd_6214322 3190934127809540670295859 := by
  unfold tailWord_6214322
  simp only [CollatzResearch.WordTrace]
  refine ⟨56663735948145047636643305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151103295861720127031048813 56663735948145047636643305)
  ·
    refine ⟨42497801961108785727482479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56663735948145047636643305 42497801961108785727482479)
    ·
      refine ⟨63746702941663178591223719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42497801961108785727482479 63746702941663178591223719)
      ·
        refine ⟨95620054412494767886835579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63746702941663178591223719 95620054412494767886835579)
        ·
          refine ⟨143430081618742151830253369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95620054412494767886835579 143430081618742151830253369)
          ·
            refine ⟨107572561214056613872690027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143430081618742151830253369 107572561214056613872690027)
            ·
              refine ⟨161358841821084920809035041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107572561214056613872690027 161358841821084920809035041)
              ·
                refine ⟨121019131365813690606776281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161358841821084920809035041 121019131365813690606776281)
                ·
                  refine ⟨90764348524360267955082211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121019131365813690606776281 90764348524360267955082211)
                  ·
                    refine ⟨136146522786540401932623317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90764348524360267955082211 136146522786540401932623317)
                    ·
                      refine ⟨3190934127809540670295859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 136146522786540401932623317 3190934127809540670295859)
                      ·
                        rfl

theorem cell23_6214322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_6214322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214322 prefixEnd_6214322 := by exact prefixLift 6214322
  have htrace : WordTrace (prefixWord ++ tailWord_6214322) baseStart_6214322 baseEnd_6214322 := by
    simpa [prefixWord, tailWord_6214322, baseEnd_6214322] using wordTrace_append hprefix tailTrace_6214322
  have hstable : (prefixWord ++ tailWord_6214322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214322).length < 2 ^ (prefixWord ++ tailWord_6214322).sum := by decide
  have hdescent : baseEnd_6214322 < baseStart_6214322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214346 : List Nat := [3, 1, 2, 1, 4, 1, 3, 2, 1, 5]
def baseStart_6214346 : Nat := 118140960795 + 6214346 * 2 ^ 59
def prefixEnd_6214346 : Nat := 4983230072969 + 3 ^ 40 * 6214346 * 2
def baseEnd_6214346 : Nat := 1063648817115082858798583

theorem tailTrace_6214346 : CollatzResearch.WordTrace tailWord_6214346 prefixEnd_6214346 1063648817115082858798583 := by
  unfold tailWord_6214346
  simp only [CollatzResearch.WordTrace]
  refine ⟨56663954786123310661361723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151103879429662161763631261 56663954786123310661361723)
  ·
    refine ⟨84995932179184965992042585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56663954786123310661361723 84995932179184965992042585)
    ·
      refine ⟨63746949134388724494031939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84995932179184965992042585 63746949134388724494031939)
      ·
        refine ⟨95620423701583086741047909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63746949134388724494031939 95620423701583086741047909)
        ·
          refine ⟨17928829444046828763946483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95620423701583086741047909 17928829444046828763946483)
          ·
            refine ⟨26893244166070243145919725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17928829444046828763946483 26893244166070243145919725)
            ·
              refine ⟨10084966562276341179719897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26893244166070243145919725 10084966562276341179719897)
              ·
                refine ⟨7563724921707255884789923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10084966562276341179719897 7563724921707255884789923)
                ·
                  refine ⟨11345587382560883827184885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7563724921707255884789923 11345587382560883827184885)
                  ·
                    refine ⟨1063648817115082858798583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11345587382560883827184885 1063648817115082858798583)
                    ·
                      rfl

theorem cell23_6214346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_6214346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214346 prefixEnd_6214346 := by exact prefixLift 6214346
  have htrace : WordTrace (prefixWord ++ tailWord_6214346) baseStart_6214346 baseEnd_6214346 := by
    simpa [prefixWord, tailWord_6214346, baseEnd_6214346] using wordTrace_append hprefix tailTrace_6214346
  have hstable : (prefixWord ++ tailWord_6214346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214346).length < 2 ^ (prefixWord ++ tailWord_6214346).sum := by decide
  have hdescent : baseEnd_6214346 < baseStart_6214346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214359 : List Nat := [1, 1, 3, 2, 1, 5, 1, 2, 1, 6]
def baseStart_6214359 : Nat := 118140960795 + 6214359 * 2 ^ 59
def prefixEnd_6214359 : Nat := 4983230072969 + 3 ^ 40 * 6214359 * 2
def baseEnd_6214359 : Nat := 1063651042197919008511063

theorem tailTrace_6214359 : CollatzResearch.WordTrace tailWord_6214359 prefixEnd_6214359 1063651042197919008511063 := by
  unfold tailWord_6214359
  simp only [CollatzResearch.WordTrace]
  refine ⟨226656293293446145865670131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151104195528964097243780087 226656293293446145865670131)
  ·
    refine ⟨339984439940169218798505197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226656293293446145865670131 339984439940169218798505197)
    ·
      refine ⟨127494164977563457049439449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 339984439940169218798505197 127494164977563457049439449)
      ·
        refine ⟨95620623733172592787079587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127494164977563457049439449 95620623733172592787079587)
        ·
          refine ⟨143430935599758889180619381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95620623733172592787079587 143430935599758889180619381)
          ·
            refine ⟨13446650212477395860683067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 143430935599758889180619381 13446650212477395860683067)
            ·
              refine ⟨20169975318716093791024601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13446650212477395860683067 20169975318716093791024601)
              ·
                refine ⟨15127481489037070343268451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20169975318716093791024601 15127481489037070343268451)
                ·
                  refine ⟨22691222233555605514902677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15127481489037070343268451 22691222233555605514902677)
                  ·
                    refine ⟨1063651042197919008511063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22691222233555605514902677 1063651042197919008511063)
                    ·
                      rfl

theorem cell23_6214359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 6].length) (baseStart_6214359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214359 prefixEnd_6214359 := by exact prefixLift 6214359
  have htrace : WordTrace (prefixWord ++ tailWord_6214359) baseStart_6214359 baseEnd_6214359 := by
    simpa [prefixWord, tailWord_6214359, baseEnd_6214359] using wordTrace_append hprefix tailTrace_6214359
  have hstable : (prefixWord ++ tailWord_6214359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214359).length < 2 ^ (prefixWord ++ tailWord_6214359).sum := by decide
  have hdescent : baseEnd_6214359 < baseStart_6214359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214372 : List Nat := [2, 3, 1, 1, 1, 15]
def baseStart_6214372 : Nat := 118140960795 + 6214372 * 2 ^ 59
def prefixEnd_6214372 : Nat := 4983230072969 + 3 ^ 40 * 6214372 * 2
def baseEnd_6214372 : Nat := 13131521818280927879303

theorem tailTrace_6214372 : CollatzResearch.WordTrace tailWord_6214372 prefixEnd_6214372 13131521818280927879303 := by
  unfold tailWord_6214372
  simp only [CollatzResearch.WordTrace]
  refine ⟨113328383721199524542946685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151104511628266032723928913 113328383721199524542946685)
  ·
    refine ⟨42498143895449821703605007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113328383721199524542946685 42498143895449821703605007)
    ·
      refine ⟨63747215843174732555407511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42498143895449821703605007 63747215843174732555407511)
      ·
        refine ⟨95620823764762098833111267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63747215843174732555407511 95620823764762098833111267)
        ·
          refine ⟨143431235647143148249666901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95620823764762098833111267 143431235647143148249666901)
          ·
            refine ⟨13131521818280927879303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 143431235647143148249666901 13131521818280927879303)
            ·
              rfl

theorem cell23_6214372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 15].length) (baseStart_6214372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214372 prefixEnd_6214372 := by exact prefixLift 6214372
  have htrace : WordTrace (prefixWord ++ tailWord_6214372) baseStart_6214372 baseEnd_6214372 := by
    simpa [prefixWord, tailWord_6214372, baseEnd_6214372] using wordTrace_append hprefix tailTrace_6214372
  have hstable : (prefixWord ++ tailWord_6214372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214372).length < 2 ^ (prefixWord ++ tailWord_6214372).sum := by decide
  have hdescent : baseEnd_6214372 < baseStart_6214372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214386 : List Nat := [3, 2, 1, 3, 1, 2, 1, 2, 3, 2, 3]
def baseStart_6214386 : Nat := 118140960795 + 6214386 * 2 ^ 59
def prefixEnd_6214386 : Nat := 4983230072969 + 3 ^ 40 * 6214386 * 2
def baseEnd_6214386 : Nat := 3190966990571428419895565

theorem tailTrace_6214386 : CollatzResearch.WordTrace tailWord_6214386 prefixEnd_6214386 3190966990571428419895565 := by
  unfold tailWord_6214386
  simp only [CollatzResearch.WordTrace]
  refine ⟨56664319516087082369225753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151104852042898886317935341 56664319516087082369225753)
  ·
    refine ⟨42498239637065311776919315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56664319516087082369225753 42498239637065311776919315)
    ·
      refine ⟨63747359455597967665378973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42498239637065311776919315 63747359455597967665378973)
      ·
        refine ⟨23905259795849237874517115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63747359455597967665378973 23905259795849237874517115)
        ·
          refine ⟨35857889693773856811775673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23905259795849237874517115 35857889693773856811775673)
          ·
            refine ⟨26893417270330392608831755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35857889693773856811775673 26893417270330392608831755)
            ·
              refine ⟨40340125905495588913247633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26893417270330392608831755 40340125905495588913247633)
              ·
                refine ⟨30255094429121691684935725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40340125905495588913247633 30255094429121691684935725)
                ·
                  refine ⟨11345660410920634381850897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30255094429121691684935725 11345660410920634381850897)
                  ·
                    refine ⟨8509245308190475786388173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11345660410920634381850897 8509245308190475786388173)
                    ·
                      refine ⟨3190966990571428419895565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8509245308190475786388173 3190966990571428419895565)
                      ·
                        rfl

theorem cell23_6214386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_6214386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214386 prefixEnd_6214386 := by exact prefixLift 6214386
  have htrace : WordTrace (prefixWord ++ tailWord_6214386) baseStart_6214386 baseEnd_6214386 := by
    simpa [prefixWord, tailWord_6214386, baseEnd_6214386] using wordTrace_append hprefix tailTrace_6214386
  have hstable : (prefixWord ++ tailWord_6214386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214386).length < 2 ^ (prefixWord ++ tailWord_6214386).sum := by decide
  have hdescent : baseEnd_6214386 < baseStart_6214386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214396 : List Nat := [2, 2, 2, 1, 3, 3, 2, 1, 1, 2, 4]
def baseStart_6214396 : Nat := 118140960795 + 6214396 * 2 ^ 59
def prefixEnd_6214396 : Nat := 4983230072969 + 3 ^ 40 * 6214396 * 2
def baseEnd_6214396 : Nat := 3190972125377973380770519

theorem tailTrace_6214396 : CollatzResearch.WordTrace tailWord_6214396 prefixEnd_6214396 3190972125377973380770519 := by
  unfold tailWord_6214396
  simp only [CollatzResearch.WordTrace]
  refine ⟨113328821397156050592383521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151105095196208067456511361 113328821397156050592383521)
  ·
    refine ⟨84996616047867037944287641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113328821397156050592383521 84996616047867037944287641)
    ·
      refine ⟨63747462035900278458215731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84996616047867037944287641 63747462035900278458215731)
      ·
        refine ⟨95621193053850417687323597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63747462035900278458215731 95621193053850417687323597)
        ·
          refine ⟨35857947395193906632746349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95621193053850417687323597 35857947395193906632746349)
          ·
            refine ⟨13446730273197714987279881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35857947395193906632746349 13446730273197714987279881)
            ·
              refine ⟨10085047704898286240459911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13446730273197714987279881 10085047704898286240459911)
              ·
                refine ⟨15127571557347429360689867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10085047704898286240459911 15127571557347429360689867)
                ·
                  refine ⟨22691357336021144041034801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15127571557347429360689867 22691357336021144041034801)
                  ·
                    refine ⟨17018518002015858030776101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22691357336021144041034801 17018518002015858030776101)
                    ·
                      refine ⟨3190972125377973380770519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17018518002015858030776101 3190972125377973380770519)
                      ·
                        rfl

theorem cell23_6214396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_6214396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214396 prefixEnd_6214396 := by exact prefixLift 6214396
  have htrace : WordTrace (prefixWord ++ tailWord_6214396) baseStart_6214396 baseEnd_6214396 := by
    simpa [prefixWord, tailWord_6214396, baseEnd_6214396] using wordTrace_append hprefix tailTrace_6214396
  have hstable : (prefixWord ++ tailWord_6214396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214396).length < 2 ^ (prefixWord ++ tailWord_6214396).sum := by decide
  have hdescent : baseEnd_6214396 < baseStart_6214396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214449 : List Nat := [1, 2, 2, 3, 2, 1, 1, 3, 2, 6]
def baseStart_6214449 : Nat := 118140960795 + 6214449 * 2 ^ 59
def prefixEnd_6214449 : Nat := 4983230072969 + 3 ^ 40 * 6214449 * 2
def baseEnd_6214449 : Nat := 1063666446617553891135925

theorem tailTrace_6214449 : CollatzResearch.WordTrace tailWord_6214449 prefixEnd_6214449 1063666446617553891135925 := by
  unfold tailWord_6214449
  simp only [CollatzResearch.WordTrace]
  refine ⟨226659575863120091236446401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151106383908746727490964267 226659575863120091236446401)
  ·
    refine ⟨169994681897340068427334801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226659575863120091236446401 169994681897340068427334801)
    ·
      refine ⟨127496011423005051320501101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169994681897340068427334801 127496011423005051320501101)
      ·
        refine ⟨47811004283626894245187913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127496011423005051320501101 47811004283626894245187913)
        ·
          refine ⟨35858253212720170683890935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47811004283626894245187913 35858253212720170683890935)
          ·
            refine ⟨53787379819080256025836403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35858253212720170683890935 53787379819080256025836403)
            ·
              refine ⟨80681069728620384038754605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53787379819080256025836403 80681069728620384038754605)
              ·
                refine ⟨30255401148232644014532977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80681069728620384038754605 30255401148232644014532977)
                ·
                  refine ⟨22691550861174483010899733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30255401148232644014532977 22691550861174483010899733)
                  ·
                    refine ⟨1063666446617553891135925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22691550861174483010899733 1063666446617553891135925)
                    ·
                      rfl

theorem cell23_6214449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 6].length) (baseStart_6214449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214449 prefixEnd_6214449 := by exact prefixLift 6214449
  have htrace : WordTrace (prefixWord ++ tailWord_6214449) baseStart_6214449 baseEnd_6214449 := by
    simpa [prefixWord, tailWord_6214449, baseEnd_6214449] using wordTrace_append hprefix tailTrace_6214449
  have hstable : (prefixWord ++ tailWord_6214449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214449).length < 2 ^ (prefixWord ++ tailWord_6214449).sum := by decide
  have hdescent : baseEnd_6214449 < baseStart_6214449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214450 : List Nat := [3, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3]
def baseStart_6214450 : Nat := 118140960795 + 6214450 * 2 ^ 59
def prefixEnd_6214450 : Nat := 4983230072969 + 3 ^ 40 * 6214450 * 2
def baseEnd_6214450 : Nat := 3190999853333316169495271

theorem tailTrace_6214450 : CollatzResearch.WordTrace tailWord_6214450 prefixEnd_6214450 3190999853333316169495271 := by
  unfold tailWord_6214450
  simp only [CollatzResearch.WordTrace]
  refine ⟨56664903084029117101808201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151106408224077645604821869 56664903084029117101808201)
  ·
    refine ⟨42498677313021837826356151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56664903084029117101808201 42498677313021837826356151)
    ·
      refine ⟨63748015969532756739534227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42498677313021837826356151 63748015969532756739534227)
      ·
        refine ⟨95622023954299135109301341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63748015969532756739534227 95622023954299135109301341)
        ·
          refine ⟨35858258982862175665988003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95622023954299135109301341 35858258982862175665988003)
          ·
            refine ⟨53787388474293263498982005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35858258982862175665988003 53787388474293263498982005)
            ·
              refine ⟨5042567669464993453029563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53787388474293263498982005 5042567669464993453029563)
              ·
                refine ⟨7563851504197490179544345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5042567669464993453029563 7563851504197490179544345)
                ·
                  refine ⟨5672888628148117634658259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7563851504197490179544345 5672888628148117634658259)
                  ·
                    refine ⟨8509332942222176451987389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5672888628148117634658259 8509332942222176451987389)
                    ·
                      refine ⟨3190999853333316169495271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8509332942222176451987389 3190999853333316169495271)
                      ·
                        rfl

theorem cell23_6214450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3].length) (baseStart_6214450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214450 prefixEnd_6214450 := by exact prefixLift 6214450
  have htrace : WordTrace (prefixWord ++ tailWord_6214450) baseStart_6214450 baseEnd_6214450 := by
    simpa [prefixWord, tailWord_6214450, baseEnd_6214450] using wordTrace_append hprefix tailTrace_6214450
  have hstable : (prefixWord ++ tailWord_6214450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214450).length < 2 ^ (prefixWord ++ tailWord_6214450).sum := by decide
  have hdescent : baseEnd_6214450 < baseStart_6214450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214468 : List Nat := [2, 3, 4, 2, 2, 1, 1, 3, 1, 2, 2]
def baseStart_6214468 : Nat := 118140960795 + 6214468 * 2 ^ 59
def prefixEnd_6214468 : Nat := 4983230072969 + 3 ^ 40 * 6214468 * 2
def baseEnd_6214468 : Nat := 3191009095985097099070189

theorem tailTrace_6214468 : CollatzResearch.WordTrace tailWord_6214468 prefixEnd_6214468 3191009095985097099070189 := by
  unfold tailWord_6214468
  simp only [CollatzResearch.WordTrace]
  refine ⟨113330134425025628740694029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151106845900034171654258705 113330134425025628740694029)
  ·
    refine ⟨42498800409384610777760261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113330134425025628740694029 42498800409384610777760261)
    ·
      refine ⟨7968525076759614520830049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42498800409384610777760261 7968525076759614520830049)
      ·
        refine ⟨5976393807569710890622537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7968525076759614520830049 5976393807569710890622537)
        ·
          refine ⟨4482295355677283167966903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5976393807569710890622537 4482295355677283167966903)
          ·
            refine ⟨6723443033515924751950355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4482295355677283167966903 6723443033515924751950355)
            ·
              refine ⟨10085164550273887127925533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6723443033515924751950355 10085164550273887127925533)
              ·
                refine ⟨3781936706352707672972075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10085164550273887127925533 3781936706352707672972075)
                ·
                  refine ⟨5672905059529061509458113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3781936706352707672972075 5672905059529061509458113)
                  ·
                    refine ⟨4254678794646796132093585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5672905059529061509458113 4254678794646796132093585)
                    ·
                      refine ⟨3191009095985097099070189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4254678794646796132093585 3191009095985097099070189)
                      ·
                        rfl

theorem cell23_6214468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_6214468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214468 prefixEnd_6214468 := by exact prefixLift 6214468
  have htrace : WordTrace (prefixWord ++ tailWord_6214468) baseStart_6214468 baseEnd_6214468 := by
    simpa [prefixWord, tailWord_6214468, baseEnd_6214468] using wordTrace_append hprefix tailTrace_6214468
  have hstable : (prefixWord ++ tailWord_6214468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214468).length < 2 ^ (prefixWord ++ tailWord_6214468).sum := by decide
  have hdescent : baseEnd_6214468 < baseStart_6214468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214469 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 4, 2, 4]
def baseStart_6214469 : Nat := 118140960795 + 6214469 * 2 ^ 59
def prefixEnd_6214469 : Nat := 4983230072969 + 3 ^ 40 * 6214469 * 2
def baseEnd_6214469 : Nat := 3191009609465751595157683

theorem tailTrace_6214469 : CollatzResearch.WordTrace tailWord_6214469 prefixEnd_6214469 3191009609465751595157683 := by
  unfold tailWord_6214469
  simp only [CollatzResearch.WordTrace]
  refine ⟨226660305323047634652174461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151106870215365089768116307 226660305323047634652174461)
  ·
    refine ⟨84997614496142862994565423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226660305323047634652174461 84997614496142862994565423)
    ·
      refine ⟨127496421744214294491848135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84997614496142862994565423 127496421744214294491848135)
      ·
        refine ⟨191244632616321441737772203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127496421744214294491848135 191244632616321441737772203)
        ·
          refine ⟨286866948924482162606658305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191244632616321441737772203 286866948924482162606658305)
          ·
            refine ⟨215150211693361621954993729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286866948924482162606658305 215150211693361621954993729)
            ·
              refine ⟨161362658770021216466245297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215150211693361621954993729 161362658770021216466245297)
              ·
                refine ⟨121021994077515912349683973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161362658770021216466245297 121021994077515912349683973)
                ·
                  refine ⟨22691623889534233565565745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121021994077515912349683973 22691623889534233565565745)
                  ·
                    refine ⟨17018717917150675174174309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22691623889534233565565745 17018717917150675174174309)
                    ·
                      refine ⟨3191009609465751595157683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17018717917150675174174309 3191009609465751595157683)
                      ·
                        rfl

theorem cell23_6214469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_6214469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214469 prefixEnd_6214469 := by exact prefixLift 6214469
  have htrace : WordTrace (prefixWord ++ tailWord_6214469) baseStart_6214469 baseEnd_6214469 := by
    simpa [prefixWord, tailWord_6214469, baseEnd_6214469] using wordTrace_append hprefix tailTrace_6214469
  have hstable : (prefixWord ++ tailWord_6214469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214469).length < 2 ^ (prefixWord ++ tailWord_6214469).sum := by decide
  have hdescent : baseEnd_6214469 < baseStart_6214469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214473 : List Nat := [1, 2, 1, 1, 2, 5, 1, 2, 4, 2, 2]
def baseStart_6214473 : Nat := 118140960795 + 6214473 * 2 ^ 59
def prefixEnd_6214473 : Nat := 4983230072969 + 3 ^ 40 * 6214473 * 2
def baseEnd_6214473 : Nat := 3191011663388369579507665

theorem tailTrace_6214473 : CollatzResearch.WordTrace tailWord_6214473 prefixEnd_6214473 3191011663388369579507665 := by
  unfold tailWord_6214473
  simp only [CollatzResearch.WordTrace]
  refine ⟨226660451215033143335320073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151106967476688762223546715 226660451215033143335320073)
  ·
    refine ⟨169995338411274857501490055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226660451215033143335320073 169995338411274857501490055)
    ·
      refine ⟨254993007616912286252235083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169995338411274857501490055 254993007616912286252235083)
      ·
        refine ⟨382489511425368429378352625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254993007616912286252235083 382489511425368429378352625)
        ·
          refine ⟨286867133569026322033764469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382489511425368429378352625 286867133569026322033764469)
          ·
            refine ⟨26893793772096217690665419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 286867133569026322033764469 26893793772096217690665419)
            ·
              refine ⟨40340690658144326535998129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26893793772096217690665419 40340690658144326535998129)
              ·
                refine ⟨30255517993608244901998597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40340690658144326535998129 30255517993608244901998597)
                ·
                  refine ⟨5672909623801545919124737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30255517993608244901998597 5672909623801545919124737)
                  ·
                    refine ⟨4254682217851159439343553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5672909623801545919124737 4254682217851159439343553)
                    ·
                      refine ⟨3191011663388369579507665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4254682217851159439343553 3191011663388369579507665)
                      ·
                        rfl

theorem cell23_6214473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4, 2, 2].length) (baseStart_6214473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214473 prefixEnd_6214473 := by exact prefixLift 6214473
  have htrace : WordTrace (prefixWord ++ tailWord_6214473) baseStart_6214473 baseEnd_6214473 := by
    simpa [prefixWord, tailWord_6214473, baseEnd_6214473] using wordTrace_append hprefix tailTrace_6214473
  have hstable : (prefixWord ++ tailWord_6214473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214473).length < 2 ^ (prefixWord ++ tailWord_6214473).sum := by decide
  have hdescent : baseEnd_6214473 < baseStart_6214473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214476 : List Nat := [2, 2, 1, 3, 3, 2, 1, 1, 2, 1, 5]
def baseStart_6214476 : Nat := 118140960795 + 6214476 * 2 ^ 59
def prefixEnd_6214476 : Nat := 4983230072969 + 3 ^ 40 * 6214476 * 2
def baseEnd_6214476 : Nat := 3191013203830333067770151

theorem tailTrace_6214476 : CollatzResearch.WordTrace tailWord_6214476 prefixEnd_6214476 3191013203830333067770151 := by
  unfold tailWord_6214476
  simp only [CollatzResearch.WordTrace]
  refine ⟨113330280317011137423839641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151107040422681516565119521 113330280317011137423839641)
  ·
    refine ⟨84997710237758353067879731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113330280317011137423839641 84997710237758353067879731)
    ·
      refine ⟨127496565356637529601819597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84997710237758353067879731 127496565356637529601819597)
      ·
        refine ⟨47811212008739073600682349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127496565356637529601819597 47811212008739073600682349)
        ·
          refine ⟨17929204503277152600255881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47811212008739073600682349 17929204503277152600255881)
          ·
            refine ⟨13446903377457864450191911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17929204503277152600255881 13446903377457864450191911)
            ·
              refine ⟨20170355066186796675287867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13446903377457864450191911 20170355066186796675287867)
              ·
                refine ⟨30255532599280195012931801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20170355066186796675287867 30255532599280195012931801)
                ·
                  refine ⟨22691649449460146259698851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30255532599280195012931801 22691649449460146259698851)
                  ·
                    refine ⟨34037474174190219389548277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22691649449460146259698851 34037474174190219389548277)
                    ·
                      refine ⟨3191013203830333067770151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34037474174190219389548277 3191013203830333067770151)
                      ·
                        rfl

theorem cell23_6214476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_6214476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214476 prefixEnd_6214476 := by exact prefixLift 6214476
  have htrace : WordTrace (prefixWord ++ tailWord_6214476) baseStart_6214476 baseEnd_6214476 := by
    simpa [prefixWord, tailWord_6214476, baseEnd_6214476] using wordTrace_append hprefix tailTrace_6214476
  have hstable : (prefixWord ++ tailWord_6214476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214476).length < 2 ^ (prefixWord ++ tailWord_6214476).sum := by decide
  have hdescent : baseEnd_6214476 < baseStart_6214476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214536 : List Nat := [2, 1, 3, 3, 2, 1, 1, 2, 1, 2, 5]
def baseStart_6214536 : Nat := 118140960795 + 6214536 * 2 ^ 59
def prefixEnd_6214536 : Nat := 4983230072969 + 3 ^ 40 * 6214536 * 2
def baseEnd_6214536 : Nat := 3191044012669602833019875

theorem tailTrace_6214536 : CollatzResearch.WordTrace tailWord_6214536 prefixEnd_6214536 3191044012669602833019875 := by
  unfold tailWord_6214536
  simp only [CollatzResearch.WordTrace]
  refine ⟨113331374506902452547431731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151108499342536603396575641 113331374506902452547431731)
  ·
    refine ⟨169997061760353678821147597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113331374506902452547431731 169997061760353678821147597)
    ·
      refine ⟨63748898160132629557930349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169997061760353678821147597 63748898160132629557930349)
      ·
        refine ⟨23905836810049736084223881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63748898160132629557930349 23905836810049736084223881)
        ·
          refine ⟨17929377607537302063167911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23905836810049736084223881 17929377607537302063167911)
          ·
            refine ⟨26894066411305953094751867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17929377607537302063167911 26894066411305953094751867)
            ·
              refine ⟨40341099616958929642127801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26894066411305953094751867 40341099616958929642127801)
              ·
                refine ⟨30255824712719197231595851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40341099616958929642127801 30255824712719197231595851)
                ·
                  refine ⟨45383737069078795847393777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30255824712719197231595851 45383737069078795847393777)
                  ·
                    refine ⟨34037802801809096885545333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45383737069078795847393777 34037802801809096885545333)
                    ·
                      refine ⟨3191044012669602833019875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34037802801809096885545333 3191044012669602833019875)
                      ·
                        rfl

theorem cell23_6214536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_6214536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214536 prefixEnd_6214536 := by exact prefixLift 6214536
  have htrace : WordTrace (prefixWord ++ tailWord_6214536) baseStart_6214536 baseEnd_6214536 := by
    simpa [prefixWord, tailWord_6214536, baseEnd_6214536] using wordTrace_append hprefix tailTrace_6214536
  have hstable : (prefixWord ++ tailWord_6214536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214536).length < 2 ^ (prefixWord ++ tailWord_6214536).sum := by decide
  have hdescent : baseEnd_6214536 < baseStart_6214536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214580 : List Nat := [2, 5, 2, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_6214580 : Nat := 118140960795 + 6214580 * 2 ^ 59
def prefixEnd_6214580 : Nat := 4983230072969 + 3 ^ 40 * 6214580 * 2
def baseEnd_6214580 : Nat := 3191066605818400660869673

theorem tailTrace_6214580 : CollatzResearch.WordTrace tailWord_6214580 prefixEnd_6214580 3191066605818400660869673 := by
  unfold tailWord_6214580
  simp only [CollatzResearch.WordTrace]
  refine ⟨113332176912822750304732597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151109569217097000406310129 113332176912822750304732597)
  ·
    refine ⟨10624891585577132841068681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113332176912822750304732597 10624891585577132841068681)
    ·
      refine ⟨7968668689182849630801511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10624891585577132841068681 7968668689182849630801511)
      ·
        refine ⟨11953003033774274446202267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7968668689182849630801511 11953003033774274446202267)
        ·
          refine ⟨17929504550661411669303401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11953003033774274446202267 17929504550661411669303401)
          ·
            refine ⟨13447128412996058751977551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17929504550661411669303401 13447128412996058751977551)
            ·
              refine ⟨20170692619494088127966327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13447128412996058751977551 20170692619494088127966327)
              ·
                refine ⟨30256038929241132191949491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20170692619494088127966327 30256038929241132191949491)
                ·
                  refine ⟨45384058393861698287924237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30256038929241132191949491 45384058393861698287924237)
                  ·
                    refine ⟨17019021897698136857971589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45384058393861698287924237 17019021897698136857971589)
                    ·
                      refine ⟨3191066605818400660869673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17019021897698136857971589 3191066605818400660869673)
                      ·
                        rfl

theorem cell23_6214580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_6214580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214580 prefixEnd_6214580 := by exact prefixLift 6214580
  have htrace : WordTrace (prefixWord ++ tailWord_6214580) baseStart_6214580 baseEnd_6214580 := by
    simpa [prefixWord, tailWord_6214580, baseEnd_6214580] using wordTrace_append hprefix tailTrace_6214580
  have hstable : (prefixWord ++ tailWord_6214580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214580).length < 2 ^ (prefixWord ++ tailWord_6214580).sum := by decide
  have hdescent : baseEnd_6214580 < baseStart_6214580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214583 : List Nat := [1, 1, 3, 1, 3, 1, 5, 1, 2, 2, 3]
def baseStart_6214583 : Nat := 118140960795 + 6214583 * 2 ^ 59
def prefixEnd_6214583 : Nat := 4983230072969 + 3 ^ 40 * 6214583 * 2
def baseEnd_6214583 : Nat := 3191068146260364149132159

theorem tailTrace_6214583 : CollatzResearch.WordTrace tailWord_6214583 prefixEnd_6214583 3191068146260364149132159 := by
  unfold tailWord_6214583
  simp only [CollatzResearch.WordTrace]
  refine ⟨226664463244634632121824403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151109642163089754747882935 226664463244634632121824403)
  ·
    refine ⟨339996694866951948182736605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226664463244634632121824403 339996694866951948182736605)
    ·
      refine ⟨127498760575106980568526227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 339996694866951948182736605 127498760575106980568526227)
      ·
        refine ⟨191248140862660470852789341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127498760575106980568526227 191248140862660470852789341)
        ·
          refine ⟨71718052823497676569796003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191248140862660470852789341 71718052823497676569796003)
          ·
            refine ⟨107577079235246514854694005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71718052823497676569796003 107577079235246514854694005)
            ·
              refine ⟨10085351178304360767627563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107577079235246514854694005 10085351178304360767627563)
              ·
                refine ⟨15128026767456541151441345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10085351178304360767627563 15128026767456541151441345)
                ·
                  refine ⟨11346020075592405863581009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15128026767456541151441345 11346020075592405863581009)
                  ·
                    refine ⟨8509515056694304397685757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11346020075592405863581009 8509515056694304397685757)
                    ·
                      refine ⟨3191068146260364149132159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8509515056694304397685757 3191068146260364149132159)
                      ·
                        rfl

theorem cell23_6214583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2, 3].length) (baseStart_6214583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214583 prefixEnd_6214583 := by exact prefixLift 6214583
  have htrace : WordTrace (prefixWord ++ tailWord_6214583) baseStart_6214583 baseEnd_6214583 := by
    simpa [prefixWord, tailWord_6214583, baseEnd_6214583] using wordTrace_append hprefix tailTrace_6214583
  have hstable : (prefixWord ++ tailWord_6214583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214583).length < 2 ^ (prefixWord ++ tailWord_6214583).sum := by decide
  have hdescent : baseEnd_6214583 < baseStart_6214583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214603 : List Nat := [1, 1, 1, 1, 3, 7, 1, 2, 6]
def baseStart_6214603 : Nat := 118140960795 + 6214603 * 2 ^ 59
def prefixEnd_6214603 : Nat := 4983230072969 + 3 ^ 40 * 6214603 * 2
def baseEnd_6214603 : Nat := 354564268430383785653563

theorem tailTrace_6214603 : CollatzResearch.WordTrace tailWord_6214603 prefixEnd_6214603 354564268430383785653563 := by
  unfold tailWord_6214603
  simp only [CollatzResearch.WordTrace]
  refine ⟨226665192704562175537552463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151110128469708117025034975 226665192704562175537552463)
  ·
    refine ⟨339997789056843263306328695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226665192704562175537552463 339997789056843263306328695)
    ·
      refine ⟨509996683585264894959493043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339997789056843263306328695 509996683585264894959493043)
      ·
        refine ⟨764995025377897342439239565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509996683585264894959493043 764995025377897342439239565)
        ·
          refine ⟨286873134516711503414714837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 764995025377897342439239565 286873134516711503414714837)
          ·
            refine ⟨6723589090235425861282379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 286873134516711503414714837 6723589090235425861282379)
            ·
              refine ⟨10085383635353138791923569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6723589090235425861282379 10085383635353138791923569)
              ·
                refine ⟨7564037726514854093942677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10085383635353138791923569 7564037726514854093942677)
                ·
                  refine ⟨354564268430383785653563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7564037726514854093942677 354564268430383785653563)
                  ·
                    rfl

theorem cell23_6214603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 6].length) (baseStart_6214603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214603 prefixEnd_6214603 := by exact prefixLift 6214603
  have htrace : WordTrace (prefixWord ++ tailWord_6214603) baseStart_6214603 baseEnd_6214603 := by
    simpa [prefixWord, tailWord_6214603, baseEnd_6214603] using wordTrace_append hprefix tailTrace_6214603
  have hstable : (prefixWord ++ tailWord_6214603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214603).length < 2 ^ (prefixWord ++ tailWord_6214603).sum := by decide
  have hdescent : baseEnd_6214603 < baseStart_6214603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214606 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6]
def baseStart_6214606 : Nat := 118140960795 + 6214606 * 2 ^ 59
def prefixEnd_6214606 : Nat := 4983230072969 + 3 ^ 40 * 6214606 * 2
def baseEnd_6214606 : Nat := 3191079956315417559144553

theorem tailTrace_6214606 : CollatzResearch.WordTrace tailWord_6214606 prefixEnd_6214606 3191079956315417559144553 := by
  unfold tailWord_6214606
  simp only [CollatzResearch.WordTrace]
  refine ⟨28333162765443913381238959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151110201415700871366607781 28333162765443913381238959)
  ·
    refine ⟨42499744148165870071858439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28333162765443913381238959 42499744148165870071858439)
    ·
      refine ⟨63749616222248805107787659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42499744148165870071858439 63749616222248805107787659)
      ·
        refine ⟨95624424333373207661681489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63749616222248805107787659 95624424333373207661681489)
        ·
          refine ⟨71718318250029905746261117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95624424333373207661681489 71718318250029905746261117)
          ·
            refine ⟨26894369343761214654847919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71718318250029905746261117 26894369343761214654847919)
            ·
              refine ⟨40341554015641821982271879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26894369343761214654847919 40341554015641821982271879)
              ·
                refine ⟨60512331023462732973407819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40341554015641821982271879 60512331023462732973407819)
                ·
                  refine ⟨90768496535194099460111729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60512331023462732973407819 90768496535194099460111729)
                  ·
                    refine ⟨68076372401395574595083797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90768496535194099460111729 68076372401395574595083797)
                    ·
                      refine ⟨3191079956315417559144553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68076372401395574595083797 3191079956315417559144553)
                      ·
                        rfl

theorem cell23_6214606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_6214606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214606 prefixEnd_6214606 := by exact prefixLift 6214606
  have htrace : WordTrace (prefixWord ++ tailWord_6214606) baseStart_6214606 baseEnd_6214606 := by
    simpa [prefixWord, tailWord_6214606, baseEnd_6214606] using wordTrace_append hprefix tailTrace_6214606
  have hstable : (prefixWord ++ tailWord_6214606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214606).length < 2 ^ (prefixWord ++ tailWord_6214606).sum := by decide
  have hdescent : baseEnd_6214606 < baseStart_6214606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214656 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 3]
def baseStart_6214656 : Nat := 118140960795 + 6214656 * 2 ^ 59
def prefixEnd_6214656 : Nat := 4983230072969 + 3 ^ 40 * 6214656 * 2
def baseEnd_6214656 : Nat := 3191105630348142363519323

theorem tailTrace_6214656 : CollatzResearch.WordTrace tailWord_6214656 prefixEnd_6214656 3191105630348142363519323 := by
  unfold tailWord_6214656
  simp only [CollatzResearch.WordTrace]
  refine ⟨113333562886685082794615911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151111417182246777059487881 113333562886685082794615911)
  ·
    refine ⟨170000344330027624191923867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113333562886685082794615911 170000344330027624191923867)
    ·
      refine ⟨255000516495041436287885801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170000344330027624191923867 255000516495041436287885801)
      ·
        refine ⟨191250387371281077215914351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255000516495041436287885801 191250387371281077215914351)
        ·
          refine ⟨286875581056921615823871527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191250387371281077215914351 286875581056921615823871527)
          ·
            refine ⟨430313371585382423735807291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286875581056921615823871527 430313371585382423735807291)
            ·
              refine ⟨645470057378073635603710937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430313371585382423735807291 645470057378073635603710937)
              ·
                refine ⟨484102543033555226702783203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 645470057378073635603710937 484102543033555226702783203)
                ·
                  refine ⟨726153814550332840054174805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 484102543033555226702783203 726153814550332840054174805)
                  ·
                    refine ⟨8509615014261712969384861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 726153814550332840054174805 8509615014261712969384861)
                    ·
                      refine ⟨3191105630348142363519323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8509615014261712969384861 3191105630348142363519323)
                      ·
                        rfl

theorem cell23_6214656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 3].length) (baseStart_6214656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214656 prefixEnd_6214656 := by exact prefixLift 6214656
  have htrace : WordTrace (prefixWord ++ tailWord_6214656) baseStart_6214656 baseEnd_6214656 := by
    simpa [prefixWord, tailWord_6214656, baseEnd_6214656] using wordTrace_append hprefix tailTrace_6214656
  have hstable : (prefixWord ++ tailWord_6214656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214656).length < 2 ^ (prefixWord ++ tailWord_6214656).sum := by decide
  have hdescent : baseEnd_6214656 < baseStart_6214656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214663 : List Nat := [1, 1, 4, 3, 1, 1, 1, 3, 4, 4]
def baseStart_6214663 : Nat := 118140960795 + 6214663 * 2 ^ 59
def prefixEnd_6214663 : Nat := 4983230072969 + 3 ^ 40 * 6214663 * 2
def baseEnd_6214663 : Nat := 1063703074904241278710597

theorem tailTrace_6214663 : CollatzResearch.WordTrace tailWord_6214663 prefixEnd_6214663 1063703074904241278710597 := by
  unfold tailWord_6214663
  simp only [CollatzResearch.WordTrace]
  refine ⟨226667381084344805784736643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151111587389563203856491095 226667381084344805784736643)
  ·
    refine ⟨340001071626517208677104965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226667381084344805784736643 340001071626517208677104965)
    ·
      refine ⟨63750200929971976626957181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 340001071626517208677104965 63750200929971976626957181)
      ·
        refine ⟨23906325348739491235108943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63750200929971976626957181 23906325348739491235108943)
        ·
          refine ⟨35859488023109236852663415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23906325348739491235108943 35859488023109236852663415)
          ·
            refine ⟨53789232034663855278995123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35859488023109236852663415 53789232034663855278995123)
            ·
              refine ⟨80683848051995782918492685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53789232034663855278995123 80683848051995782918492685)
              ·
                refine ⟨30256443019498418594434757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80683848051995782918492685 30256443019498418594434757)
                ·
                  refine ⟨5673083066155953486456517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30256443019498418594434757 5673083066155953486456517)
                  ·
                    refine ⟨1063703074904241278710597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5673083066155953486456517 1063703074904241278710597)
                    ·
                      rfl

theorem cell23_6214663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_6214663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214663 prefixEnd_6214663 := by exact prefixLift 6214663
  have htrace : WordTrace (prefixWord ++ tailWord_6214663) baseStart_6214663 baseEnd_6214663 := by
    simpa [prefixWord, tailWord_6214663, baseEnd_6214663] using wordTrace_append hprefix tailTrace_6214663
  have hstable : (prefixWord ++ tailWord_6214663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214663).length < 2 ^ (prefixWord ++ tailWord_6214663).sum := by decide
  have hdescent : baseEnd_6214663 < baseStart_6214663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214664 : List Nat := [2, 1, 3, 2, 1, 4, 3, 2, 1, 1, 3]
def baseStart_6214664 : Nat := 118140960795 + 6214664 * 2 ^ 59
def prefixEnd_6214664 : Nat := 4983230072969 + 3 ^ 40 * 6214664 * 2
def baseEnd_6214664 : Nat := 3191109738193378332219287

theorem tailTrace_6214664 : CollatzResearch.WordTrace tailWord_6214664 prefixEnd_6214664 3191109738193378332219287 := by
  unfold tailWord_6214664
  simp only [CollatzResearch.WordTrace]
  refine ⟨113333708778670591477761523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151111611704894121970348697 113333708778670591477761523)
  ·
    refine ⟨170000563168005887216642285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113333708778670591477761523 170000563168005887216642285)
    ·
      refine ⟨63750211188002207706240857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170000563168005887216642285 63750211188002207706240857)
      ·
        refine ⟨47812658391001655779680643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63750211188002207706240857 47812658391001655779680643)
        ·
          refine ⟨71718987586502483669520965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47812658391001655779680643 71718987586502483669520965)
          ·
            refine ⟨13447310172469215688035181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71718987586502483669520965 13447310172469215688035181)
            ·
              refine ⟨5042741314675955883013193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13447310172469215688035181 5042741314675955883013193)
              ·
                refine ⟨3782055986006966912259895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5042741314675955883013193 3782055986006966912259895)
                ·
                  refine ⟨5673083979010450368389843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3782055986006966912259895 5673083979010450368389843)
                  ·
                    refine ⟨8509625968515675552584765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5673083979010450368389843 8509625968515675552584765)
                    ·
                      refine ⟨3191109738193378332219287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8509625968515675552584765 3191109738193378332219287)
                      ·
                        rfl

theorem cell23_6214664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_6214664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214664 prefixEnd_6214664 := by exact prefixLift 6214664
  have htrace : WordTrace (prefixWord ++ tailWord_6214664) baseStart_6214664 baseEnd_6214664 := by
    simpa [prefixWord, tailWord_6214664, baseEnd_6214664] using wordTrace_append hprefix tailTrace_6214664
  have hstable : (prefixWord ++ tailWord_6214664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214664).length < 2 ^ (prefixWord ++ tailWord_6214664).sum := by decide
  have hdescent : baseEnd_6214664 < baseStart_6214664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214680 : List Nat := [2, 1, 2, 3, 2, 3, 1, 3, 2, 4]
def baseStart_6214680 : Nat := 118140960795 + 6214680 * 2 ^ 59
def prefixEnd_6214680 : Nat := 4983230072969 + 3 ^ 40 * 6214680 * 2
def baseEnd_6214680 : Nat := 1063705984627950089873071

theorem tailTrace_6214680 : CollatzResearch.WordTrace tailWord_6214680 prefixEnd_6214680 1063705984627950089873071 := by
  unfold tailWord_6214680
  simp only [CollatzResearch.WordTrace]
  refine ⟨113334000562641608844052747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151112000750188811792070329 113334000562641608844052747)
  ·
    refine ⟨170001000843962413266079121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113334000562641608844052747 170001000843962413266079121)
    ·
      refine ⟨127500750632971809949559341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170001000843962413266079121 127500750632971809949559341)
      ·
        refine ⟨47812781487364428731084753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127500750632971809949559341 47812781487364428731084753)
        ·
          refine ⟨35859586115523321548313565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47812781487364428731084753 35859586115523321548313565)
          ·
            refine ⟨13447344793321245580617587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35859586115523321548313565 13447344793321245580617587)
            ·
              refine ⟨20171017189981868370926381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13447344793321245580617587 20171017189981868370926381)
              ·
                refine ⟨7564131446243200639097393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20171017189981868370926381 7564131446243200639097393)
                ·
                  refine ⟨5673098584682400479323045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7564131446243200639097393 5673098584682400479323045)
                  ·
                    refine ⟨1063705984627950089873071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5673098584682400479323045 1063705984627950089873071)
                    ·
                      rfl

theorem cell23_6214680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 2, 4].length) (baseStart_6214680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214680 prefixEnd_6214680 := by exact prefixLift 6214680
  have htrace : WordTrace (prefixWord ++ tailWord_6214680) baseStart_6214680 baseEnd_6214680 := by
    simpa [prefixWord, tailWord_6214680, baseEnd_6214680] using wordTrace_append hprefix tailTrace_6214680
  have hstable : (prefixWord ++ tailWord_6214680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214680).length < 2 ^ (prefixWord ++ tailWord_6214680).sum := by decide
  have hdescent : baseEnd_6214680 < baseStart_6214680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214690 : List Nat := [3, 3, 1, 1, 1, 4, 1, 1, 3, 2, 3]
def baseStart_6214690 : Nat := 118140960795 + 6214690 * 2 ^ 59
def prefixEnd_6214690 : Nat := 4983230072969 + 3 ^ 40 * 6214690 * 2
def baseEnd_6214690 : Nat := 3191123088690395230494167

theorem tailTrace_6214690 : CollatzResearch.WordTrace tailWord_6214690 prefixEnd_6214690 3191123088690395230494167 := by
  unfold tailWord_6214690
  simp only [CollatzResearch.WordTrace]
  refine ⟨56667091463811747348992381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151112243903497992930646349 56667091463811747348992381)
  ·
    refine ⟨21250159298929405255872143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56667091463811747348992381 21250159298929405255872143)
    ·
      refine ⟨31875238948394107883808215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21250159298929405255872143 31875238948394107883808215)
      ·
        refine ⟨47812858422591161825712323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31875238948394107883808215 47812858422591161825712323)
        ·
          refine ⟨71719287633886742738568485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47812858422591161825712323 71719287633886742738568485)
          ·
            refine ⟨13447366431353764263481591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71719287633886742738568485 13447366431353764263481591)
            ·
              refine ⟨20171049647030646395222387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13447366431353764263481591 20171049647030646395222387)
              ·
                refine ⟨30256574470545969592833581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20171049647030646395222387 30256574470545969592833581)
                ·
                  refine ⟨11346215426454738597312593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30256574470545969592833581 11346215426454738597312593)
                  ·
                    refine ⟨8509661569841053947984445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11346215426454738597312593 8509661569841053947984445)
                    ·
                      refine ⟨3191123088690395230494167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8509661569841053947984445 3191123088690395230494167)
                      ·
                        rfl

theorem cell23_6214690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_6214690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214690 prefixEnd_6214690 := by exact prefixLift 6214690
  have htrace : WordTrace (prefixWord ++ tailWord_6214690) baseStart_6214690 baseEnd_6214690 := by
    simpa [prefixWord, tailWord_6214690, baseEnd_6214690] using wordTrace_append hprefix tailTrace_6214690
  have hstable : (prefixWord ++ tailWord_6214690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214690).length < 2 ^ (prefixWord ++ tailWord_6214690).sum := by decide
  have hdescent : baseEnd_6214690 < baseStart_6214690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214721 : List Nat := [1, 2, 5, 1, 3, 1, 1, 4, 1, 2, 2]
def baseStart_6214721 : Nat := 118140960795 + 6214721 * 2 ^ 59
def prefixEnd_6214721 : Nat := 4983230072969 + 3 ^ 40 * 6214721 * 2
def baseEnd_6214721 : Nat := 3191139006590684609206525

theorem tailTrace_6214721 : CollatzResearch.WordTrace tailWord_6214721 prefixEnd_6214721 3191139006590684609206525 := by
  unfold tailWord_6214721
  simp only [CollatzResearch.WordTrace]
  refine ⟨226669496518134681690348017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151112997678756454460232011 226669496518134681690348017)
  ·
    refine ⟨170002122388601011267761013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226669496518134681690348017 170002122388601011267761013)
    ·
      refine ⟨15937698973931344806352595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170002122388601011267761013 15937698973931344806352595)
      ·
        refine ⟨23906548460897017209528893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15937698973931344806352595 23906548460897017209528893)
        ·
          refine ⟨8964955672836381453573335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23906548460897017209528893 8964955672836381453573335)
          ·
            refine ⟨13447433509254572180360003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8964955672836381453573335 13447433509254572180360003)
            ·
              refine ⟨20171150263881858270540005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13447433509254572180360003 20171150263881858270540005)
              ·
                refine ⟨3782090674477848425726251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20171150263881858270540005 3782090674477848425726251)
                ·
                  refine ⟨5673136011716772638589377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3782090674477848425726251 5673136011716772638589377)
                  ·
                    refine ⟨4254852008787579478942033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5673136011716772638589377 4254852008787579478942033)
                    ·
                      refine ⟨3191139006590684609206525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4254852008787579478942033 3191139006590684609206525)
                      ·
                        rfl

theorem cell23_6214721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_6214721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214721 prefixEnd_6214721 := by exact prefixLift 6214721
  have htrace : WordTrace (prefixWord ++ tailWord_6214721) baseStart_6214721 baseEnd_6214721 := by
    simpa [prefixWord, tailWord_6214721, baseEnd_6214721] using wordTrace_append hprefix tailTrace_6214721
  have hstable : (prefixWord ++ tailWord_6214721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214721).length < 2 ^ (prefixWord ++ tailWord_6214721).sum := by decide
  have hdescent : baseEnd_6214721 < baseStart_6214721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214730 : List Nat := [3, 1, 2, 1, 1, 2, 3, 2, 3, 3, 2]
def baseStart_6214730 : Nat := 118140960795 + 6214730 * 2 ^ 59
def prefixEnd_6214730 : Nat := 4983230072969 + 3 ^ 40 * 6214730 * 2
def baseEnd_6214730 : Nat := 3191143627916575073993983

theorem tailTrace_6214730 : CollatzResearch.WordTrace tailWord_6214730 prefixEnd_6214730 3191143627916575073993983 := by
  unfold tailWord_6214730
  simp only [CollatzResearch.WordTrace]
  refine ⟨56667456193775519056856411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151113216516734717484950429 56667456193775519056856411)
  ·
    refine ⟨85001184290663278585284617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56667456193775519056856411 85001184290663278585284617)
    ·
      refine ⟨63750888217997458938963463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85001184290663278585284617 63750888217997458938963463)
      ·
        refine ⟨95626332326996188408445195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63750888217997458938963463 95626332326996188408445195)
        ·
          refine ⟨143439498490494282612667793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95626332326996188408445195 143439498490494282612667793)
          ·
            refine ⟨107579623867870711959500845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143439498490494282612667793 107579623867870711959500845)
            ·
              refine ⟨40342358950451516984812817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107579623867870711959500845 40342358950451516984812817)
              ·
                refine ⟨30256769212838637738609613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40342358950451516984812817 30256769212838637738609613)
                ·
                  refine ⟨11346288454814489151978605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30256769212838637738609613 11346288454814489151978605)
                  ·
                    refine ⟨4254858170555433431991977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11346288454814489151978605 4254858170555433431991977)
                    ·
                      refine ⟨3191143627916575073993983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4254858170555433431991977 3191143627916575073993983)
                      ·
                        rfl

theorem cell23_6214730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 3, 3, 2].length) (baseStart_6214730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214730 prefixEnd_6214730 := by exact prefixLift 6214730
  have htrace : WordTrace (prefixWord ++ tailWord_6214730) baseStart_6214730 baseEnd_6214730 := by
    simpa [prefixWord, tailWord_6214730, baseEnd_6214730] using wordTrace_append hprefix tailTrace_6214730
  have hstable : (prefixWord ++ tailWord_6214730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214730).length < 2 ^ (prefixWord ++ tailWord_6214730).sum := by decide
  have hdescent : baseEnd_6214730 < baseStart_6214730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214813 : List Nat := [1, 4, 2, 1, 1, 2, 1, 3, 1, 7]
def baseStart_6214813 : Nat := 118140960795 + 6214813 * 2 ^ 59
def prefixEnd_6214813 : Nat := 4983230072969 + 3 ^ 40 * 6214813 * 2
def baseEnd_6214813 : Nat := 1063728748936966083085367

theorem tailTrace_6214813 : CollatzResearch.WordTrace tailWord_6214813 prefixEnd_6214813 1063728748936966083085367 := by
  unfold tailWord_6214813
  simp only [CollatzResearch.WordTrace]
  refine ⟨226672852033801381402697093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151115234689200920935131395 226672852033801381402697093)
  ·
    refine ⟨42501159756337759013005705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226672852033801381402697093 42501159756337759013005705)
    ·
      refine ⟨31875869817253319259754279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42501159756337759013005705 31875869817253319259754279)
      ·
        refine ⟨47813804725879978889631419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31875869817253319259754279 47813804725879978889631419)
        ·
          refine ⟨71720707088819968334447129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47813804725879978889631419 71720707088819968334447129)
          ·
            refine ⟨53790530316614976250835347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71720707088819968334447129 53790530316614976250835347)
            ·
              refine ⟨80685795474922464376253021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53790530316614976250835347 80685795474922464376253021)
              ·
                refine ⟨30257173303095924141094883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80685795474922464376253021 30257173303095924141094883)
                ·
                  refine ⟨45385759954643886211642325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30257173303095924141094883 45385759954643886211642325)
                  ·
                    refine ⟨1063728748936966083085367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45385759954643886211642325 1063728748936966083085367)
                    ·
                      rfl

theorem cell23_6214813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_6214813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214813 prefixEnd_6214813 := by exact prefixLift 6214813
  have htrace : WordTrace (prefixWord ++ tailWord_6214813) baseStart_6214813 baseEnd_6214813 := by
    simpa [prefixWord, tailWord_6214813, baseEnd_6214813] using wordTrace_append hprefix tailTrace_6214813
  have hstable : (prefixWord ++ tailWord_6214813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214813).length < 2 ^ (prefixWord ++ tailWord_6214813).sum := by decide
  have hdescent : baseEnd_6214813 < baseStart_6214813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214890 : List Nat := [3, 1, 3, 1, 1, 3, 1, 4, 6]
def baseStart_6214890 : Nat := 118140960795 + 6214890 * 2 ^ 59
def prefixEnd_6214890 : Nat := 4983230072969 + 3 ^ 40 * 6214890 * 2
def baseEnd_6214890 : Nat := 354580642757921605332583

theorem tailTrace_6214890 : CollatzResearch.WordTrace tailWord_6214890 prefixEnd_6214890 354580642757921605332583 := by
  unfold tailWord_6214890
  simp only [CollatzResearch.WordTrace]
  refine ⟨56668915113630605888312531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151117106969681615702166749 56668915113630605888312531)
  ·
    refine ⟨85003372670445908832468797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56668915113630605888312531 85003372670445908832468797)
    ·
      refine ⟨31876264751417215812175799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85003372670445908832468797 31876264751417215812175799)
      ·
        refine ⟨47814397127125823718263699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31876264751417215812175799 47814397127125823718263699)
        ·
          refine ⟨71721595690688735577395549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47814397127125823718263699 71721595690688735577395549)
          ·
            refine ⟨26895598384008275841523331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71721595690688735577395549 26895598384008275841523331)
            ·
              refine ⟨40343397576012413762284997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26895598384008275841523331 40343397576012413762284997)
              ·
                refine ⟨7564387045502327580428437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40343397576012413762284997 7564387045502327580428437)
                ·
                  refine ⟨354580642757921605332583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7564387045502327580428437 354580642757921605332583)
                  ·
                    rfl

theorem cell23_6214890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 6].length) (baseStart_6214890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214890 prefixEnd_6214890 := by exact prefixLift 6214890
  have htrace : WordTrace (prefixWord ++ tailWord_6214890) baseStart_6214890 baseEnd_6214890 := by
    simpa [prefixWord, tailWord_6214890, baseEnd_6214890] using wordTrace_append hprefix tailTrace_6214890
  have hstable : (prefixWord ++ tailWord_6214890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214890).length < 2 ^ (prefixWord ++ tailWord_6214890).sum := by decide
  have hdescent : baseEnd_6214890 < baseStart_6214890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214917 : List Nat := [1, 3, 1, 1, 2, 1, 5, 2, 3, 1, 3]
def baseStart_6214917 : Nat := 118140960795 + 6214917 * 2 ^ 59
def prefixEnd_6214917 : Nat := 4983230072969 + 3 ^ 40 * 6214917 * 2
def baseEnd_6214917 : Nat := 3191239648798965842355623

theorem tailTrace_6214917 : CollatzResearch.WordTrace tailWord_6214917 prefixEnd_6214917 3191239648798965842355623 := by
  unfold tailWord_6214917
  simp only [CollatzResearch.WordTrace]
  refine ⟨226676645225424607164483005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151117763483616404776322003 226676645225424607164483005)
  ·
    refine ⟨85003741959534227686681127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226676645225424607164483005 85003741959534227686681127)
    ·
      refine ⟨127505612939301341530021691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85003741959534227686681127 127505612939301341530021691)
      ·
        refine ⟨191258419408952012295032537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127505612939301341530021691 191258419408952012295032537)
        ·
          refine ⟨143443814556714009221274403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191258419408952012295032537 143443814556714009221274403)
          ·
            refine ⟨215165721835071013831911605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143443814556714009221274403 215165721835071013831911605)
            ·
              refine ⟨20171786422037907546741713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 215165721835071013831911605 20171786422037907546741713)
              ·
                refine ⟨15128839816528430660056285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20171786422037907546741713 15128839816528430660056285)
                ·
                  refine ⟨5673314931198161497521107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15128839816528430660056285 5673314931198161497521107)
                  ·
                    refine ⟨8509972396797242246281661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5673314931198161497521107 8509972396797242246281661)
                    ·
                      refine ⟨3191239648798965842355623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8509972396797242246281661 3191239648798965842355623)
                      ·
                        rfl

theorem cell23_6214917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3, 1, 3].length) (baseStart_6214917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214917 prefixEnd_6214917 := by exact prefixLift 6214917
  have htrace : WordTrace (prefixWord ++ tailWord_6214917) baseStart_6214917 baseEnd_6214917 := by
    simpa [prefixWord, tailWord_6214917, baseEnd_6214917] using wordTrace_append hprefix tailTrace_6214917
  have hstable : (prefixWord ++ tailWord_6214917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214917).length < 2 ^ (prefixWord ++ tailWord_6214917).sum := by decide
  have hdescent : baseEnd_6214917 < baseStart_6214917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214953 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 2, 5, 6]
def baseStart_6214953 : Nat := 118140960795 + 6214953 * 2 ^ 59
def prefixEnd_6214953 : Nat := 4983230072969 + 3 ^ 40 * 6214953 * 2
def baseEnd_6214953 : Nat := 3191258134102527701505457

theorem tailTrace_6214953 : CollatzResearch.WordTrace tailWord_6214953 prefixEnd_6214953 3191258134102527701505457 := by
  unfold tailWord_6214953
  simp only [CollatzResearch.WordTrace]
  refine ⟨226677958253294185312793513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151118638835529456875195675 226677958253294185312793513)
  ·
    refine ⟨170008468689970638984595135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226677958253294185312793513 170008468689970638984595135)
    ·
      refine ⟨255012703034955958476892703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170008468689970638984595135 255012703034955958476892703)
      ·
        refine ⟨382519054552433937715339055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255012703034955958476892703 382519054552433937715339055)
        ·
          refine ⟨573778581828650906573008583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382519054552433937715339055 573778581828650906573008583)
          ·
            refine ⟨860667872742976359859512875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573778581828650906573008583 860667872742976359859512875)
            ·
              refine ⟨1291001809114464539789269313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 860667872742976359859512875 1291001809114464539789269313)
              ·
                refine ⟨968251356835848404841951985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1291001809114464539789269313 968251356835848404841951985)
                ·
                  refine ⟨726188517626886303631463989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 968251356835848404841951985 726188517626886303631463989)
                  ·
                    refine ⟨68080173527520590965449749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 726188517626886303631463989 68080173527520590965449749)
                    ·
                      refine ⟨3191258134102527701505457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68080173527520590965449749 3191258134102527701505457)
                      ·
                        rfl

theorem cell23_6214953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 5, 6].length) (baseStart_6214953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214953 prefixEnd_6214953 := by exact prefixLift 6214953
  have htrace : WordTrace (prefixWord ++ tailWord_6214953) baseStart_6214953 baseEnd_6214953 := by
    simpa [prefixWord, tailWord_6214953, baseEnd_6214953] using wordTrace_append hprefix tailTrace_6214953
  have hstable : (prefixWord ++ tailWord_6214953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214953).length < 2 ^ (prefixWord ++ tailWord_6214953).sum := by decide
  have hdescent : baseEnd_6214953 < baseStart_6214953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214960 : List Nat := [2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 5]
def baseStart_6214960 : Nat := 118140960795 + 6214960 * 2 ^ 59
def prefixEnd_6214960 : Nat := 4983230072969 + 3 ^ 40 * 6214960 * 2
def baseEnd_6214960 : Nat := 3191261728467109174117925

theorem tailTrace_6214960 : CollatzResearch.WordTrace tailWord_6214960 prefixEnd_6214960 3191261728467109174117925 := by
  unfold tailWord_6214960
  simp only [CollatzResearch.WordTrace]
  refine ⟨113339106782134412754149167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151118809042845883672198889 113339106782134412754149167)
  ·
    refine ⟨170008660173201619131223751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113339106782134412754149167 170008660173201619131223751)
    ·
      refine ⟨255012990259802428696835627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170008660173201619131223751 255012990259802428696835627)
      ·
        refine ⟨382519485389703643045253441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255012990259802428696835627 382519485389703643045253441)
        ·
          refine ⟨286889614042277732283940081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382519485389703643045253441 286889614042277732283940081)
          ·
            refine ⟨215167210531708299212955061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286889614042277732283940081 215167210531708299212955061)
            ·
              refine ⟨20171925987347653051214537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 215167210531708299212955061 20171925987347653051214537)
              ·
                refine ⟨15128944490510739788410903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20171925987347653051214537 15128944490510739788410903)
                ·
                  refine ⟨22693416735766109682616355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15128944490510739788410903 22693416735766109682616355)
                  ·
                    refine ⟨34040125103649164523924533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22693416735766109682616355 34040125103649164523924533)
                    ·
                      refine ⟨3191261728467109174117925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34040125103649164523924533 3191261728467109174117925)
                      ·
                        rfl

theorem cell23_6214960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 5].length) (baseStart_6214960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214960 prefixEnd_6214960 := by exact prefixLift 6214960
  have htrace : WordTrace (prefixWord ++ tailWord_6214960) baseStart_6214960 baseEnd_6214960 := by
    simpa [prefixWord, tailWord_6214960, baseEnd_6214960] using wordTrace_append hprefix tailTrace_6214960
  have hstable : (prefixWord ++ tailWord_6214960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214960).length < 2 ^ (prefixWord ++ tailWord_6214960).sum := by decide
  have hdescent : baseEnd_6214960 < baseStart_6214960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214970 : List Nat := [3, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6]
def baseStart_6214970 : Nat := 118140960795 + 6214970 * 2 ^ 59
def prefixEnd_6214970 : Nat := 4983230072969 + 3 ^ 40 * 6214970 * 2
def baseEnd_6214970 : Nat := 3191266863273654134992879

theorem tailTrace_6214970 : CollatzResearch.WordTrace tailWord_6214970 prefixEnd_6214970 3191266863273654134992879 := by
  unfold tailWord_6214970
  simp only [CollatzResearch.WordTrace]
  refine ⟨56669644573558149304040591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151119052196155064810774909 56669644573558149304040591)
  ·
    refine ⟨85004466860337223956060887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56669644573558149304040591 85004466860337223956060887)
    ·
      refine ⟨127506700290505835934091331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85004466860337223956060887 127506700290505835934091331)
      ·
        refine ⟨191260050435758753901136997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127506700290505835934091331 191260050435758753901136997)
        ·
          refine ⟨35861259456704766356463187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191260050435758753901136997 35861259456704766356463187)
          ·
            refine ⟨53791889185057149534694781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35861259456704766356463187 53791889185057149534694781)
            ·
              refine ⟨20171958444396431075510543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53791889185057149534694781 20171958444396431075510543)
              ·
                refine ⟨30257937666594646613265815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20171958444396431075510543 30257937666594646613265815)
                ·
                  refine ⟨45386906499891969919898723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30257937666594646613265815 45386906499891969919898723)
                  ·
                    refine ⟨68080359749837954879848085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45386906499891969919898723 68080359749837954879848085)
                    ·
                      refine ⟨3191266863273654134992879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68080359749837954879848085 3191266863273654134992879)
                      ·
                        rfl

theorem cell23_6214970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_6214970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214970 prefixEnd_6214970 := by exact prefixLift 6214970
  have htrace : WordTrace (prefixWord ++ tailWord_6214970) baseStart_6214970 baseEnd_6214970 := by
    simpa [prefixWord, tailWord_6214970, baseEnd_6214970] using wordTrace_append hprefix tailTrace_6214970
  have hstable : (prefixWord ++ tailWord_6214970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214970).length < 2 ^ (prefixWord ++ tailWord_6214970).sum := by decide
  have hdescent : baseEnd_6214970 < baseStart_6214970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6214974 : List Nat := [4, 2, 1, 2, 1, 1, 4, 2, 1, 1, 4]
def baseStart_6214974 : Nat := 118140960795 + 6214974 * 2 ^ 59
def prefixEnd_6214974 : Nat := 4983230072969 + 3 ^ 40 * 6214974 * 2
def baseEnd_6214974 : Nat := 3191268917196272119342861

theorem tailTrace_6214974 : CollatzResearch.WordTrace tailWord_6214974 prefixEnd_6214974 3191268917196272119342861 := by
  unfold tailWord_6214974
  simp only [CollatzResearch.WordTrace]
  refine ⟨28334840523277263237413497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151119149457478737266205317 28334840523277263237413497)
  ·
    refine ⟨21251130392457947428060123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28334840523277263237413497 21251130392457947428060123)
    ·
      refine ⟨31876695588686921142090185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21251130392457947428060123 31876695588686921142090185)
      ·
        refine ⟨23907521691515190856567639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31876695588686921142090185 23907521691515190856567639)
        ·
          refine ⟨35861282537272786284851459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23907521691515190856567639 35861282537272786284851459)
          ·
            refine ⟨53791923805909179427277189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35861282537272786284851459 53791923805909179427277189)
            ·
              refine ⟨10085985713607971142614473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53791923805909179427277189 10085985713607971142614473)
              ·
                refine ⟨7564489285205978356960855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10085985713607971142614473 7564489285205978356960855)
                ·
                  refine ⟨11346733927808967535441283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7564489285205978356960855 11346733927808967535441283)
                  ·
                    refine ⟨17020100891713451303161925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11346733927808967535441283 17020100891713451303161925)
                    ·
                      refine ⟨3191268917196272119342861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17020100891713451303161925 3191268917196272119342861)
                      ·
                        rfl

theorem cell23_6214974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_6214974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6214974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6214974 prefixEnd_6214974 := by exact prefixLift 6214974
  have htrace : WordTrace (prefixWord ++ tailWord_6214974) baseStart_6214974 baseEnd_6214974 := by
    simpa [prefixWord, tailWord_6214974, baseEnd_6214974] using wordTrace_append hprefix tailTrace_6214974
  have hstable : (prefixWord ++ tailWord_6214974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6214974).length < 2 ^ (prefixWord ++ tailWord_6214974).sum := by decide
  have hdescent : baseEnd_6214974 < baseStart_6214974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6214974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215018 : List Nat := [3, 1, 3, 3, 2, 2, 2, 1, 2, 4]
def baseStart_6215018 : Nat := 118140960795 + 6215018 * 2 ^ 59
def prefixEnd_6215018 : Nat := 4983230072969 + 3 ^ 40 * 6215018 * 2
def baseEnd_6215018 : Nat := 1063763836781689982397553

theorem tailTrace_6215018 : CollatzResearch.WordTrace tailWord_6215018 prefixEnd_6215018 1063763836781689982397553 := by
  unfold tailWord_6215018
  simp only [CollatzResearch.WordTrace]
  refine ⟨56670082249514675353477427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151120219332039134275939805 56670082249514675353477427)
  ·
    refine ⟨85005123374272013030216141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56670082249514675353477427 85005123374272013030216141)
    ·
      refine ⟨31876921265352004886331053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85005123374272013030216141 31876921265352004886331053)
      ·
        refine ⟨11953845474507001832374145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31876921265352004886331053 11953845474507001832374145)
        ·
          refine ⟨8965384105880251374280609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11953845474507001832374145 8965384105880251374280609)
          ·
            refine ⟨6724038079410188530710457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8965384105880251374280609 6724038079410188530710457)
            ·
              refine ⟨5043028559557641398032843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6724038079410188530710457 5043028559557641398032843)
              ·
                refine ⟨7564542839336462097049265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5043028559557641398032843 7564542839336462097049265)
                ·
                  refine ⟨5673407129502346572786949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7564542839336462097049265 5673407129502346572786949)
                  ·
                    refine ⟨1063763836781689982397553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5673407129502346572786949 1063763836781689982397553)
                    ·
                      rfl

theorem cell23_6215018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_6215018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215018 prefixEnd_6215018 := by exact prefixLift 6215018
  have htrace : WordTrace (prefixWord ++ tailWord_6215018) baseStart_6215018 baseEnd_6215018 := by
    simpa [prefixWord, tailWord_6215018, baseEnd_6215018] using wordTrace_append hprefix tailTrace_6215018
  have hstable : (prefixWord ++ tailWord_6215018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215018).length < 2 ^ (prefixWord ++ tailWord_6215018).sum := by decide
  have hdescent : baseEnd_6215018 < baseStart_6215018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215024 : List Nat := [2, 1, 1, 1, 4, 2, 3, 3, 2, 1, 3]
def baseStart_6215024 : Nat := 118140960795 + 6215024 * 2 ^ 59
def prefixEnd_6215024 : Nat := 4983230072969 + 3 ^ 40 * 6215024 * 2
def baseEnd_6215024 : Nat := 3191294591228996923717631

theorem tailTrace_6215024 : CollatzResearch.WordTrace tailWord_6215024 prefixEnd_6215024 3191294591228996923717631 := by
  unfold tailWord_6215024
  simp only [CollatzResearch.WordTrace]
  refine ⟨113340273918018482219314063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151120365224024642959085417 113340273918018482219314063)
  ·
    refine ⟨170010410877027723328971095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113340273918018482219314063 170010410877027723328971095)
    ·
      refine ⟨255015616315541584993456643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170010410877027723328971095 255015616315541584993456643)
      ·
        refine ⟨382523424473312377490184965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255015616315541584993456643 382523424473312377490184965)
        ·
          refine ⟨71723142088746070779409681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 382523424473312377490184965 71723142088746070779409681)
          ·
            refine ⟨53792356566559553084557261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71723142088746070779409681 53792356566559553084557261)
            ·
              refine ⟨20172133712459832406708973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53792356566559553084557261 20172133712459832406708973)
              ·
                refine ⟨7564550142172437152515865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20172133712459832406708973 7564550142172437152515865)
                ·
                  refine ⟨5673412606629327864386899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7564550142172437152515865 5673412606629327864386899)
                  ·
                    refine ⟨8510118909943991796580349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5673412606629327864386899 8510118909943991796580349)
                    ·
                      refine ⟨3191294591228996923717631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8510118909943991796580349 3191294591228996923717631)
                      ·
                        rfl

theorem cell23_6215024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 2, 1, 3].length) (baseStart_6215024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215024 prefixEnd_6215024 := by exact prefixLift 6215024
  have htrace : WordTrace (prefixWord ++ tailWord_6215024) baseStart_6215024 baseEnd_6215024 := by
    simpa [prefixWord, tailWord_6215024, baseEnd_6215024] using wordTrace_append hprefix tailTrace_6215024
  have hstable : (prefixWord ++ tailWord_6215024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215024).length < 2 ^ (prefixWord ++ tailWord_6215024).sum := by decide
  have hdescent : baseEnd_6215024 < baseStart_6215024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215051 : List Nat := [1, 1, 1, 1, 4, 3, 5, 1, 1, 3, 2]
def baseStart_6215051 : Nat := 118140960795 + 6215051 * 2 ^ 59
def prefixEnd_6215051 : Nat := 4983230072969 + 3 ^ 40 * 6215051 * 2
def baseEnd_6215051 : Nat := 3191308455206668318080007

theorem tailTrace_6215051 : CollatzResearch.WordTrace tailWord_6215051 prefixEnd_6215051 3191308455206668318080007 := by
  unfold tailWord_6215051
  simp only [CollatzResearch.WordTrace]
  refine ⟨226681532606939148049861007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151121021737959432033240671 226681532606939148049861007)
  ·
    refine ⟨340022298910408722074791511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226681532606939148049861007 340022298910408722074791511)
    ·
      refine ⟨510033448365613083112187267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340022298910408722074791511 510033448365613083112187267)
      ·
        refine ⟨765050172548419624668280901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510033448365613083112187267 765050172548419624668280901)
        ·
          refine ⟨143446907352828679625302669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 765050172548419624668280901 143446907352828679625302669)
          ·
            refine ⟨53792590257310754859488501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143446907352828679625302669 53792590257310754859488501)
            ·
              refine ⟨5043055336622883268077047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53792590257310754859488501 5043055336622883268077047)
              ·
                refine ⟨7564583004934324902115571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5043055336622883268077047 7564583004934324902115571)
                ·
                  refine ⟨11346874507401487353173357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7564583004934324902115571 11346874507401487353173357)
                  ·
                    refine ⟨4255077940275557757440009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11346874507401487353173357 4255077940275557757440009)
                    ·
                      refine ⟨3191308455206668318080007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4255077940275557757440009 3191308455206668318080007)
                      ·
                        rfl

theorem cell23_6215051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 1, 3, 2].length) (baseStart_6215051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215051 prefixEnd_6215051 := by exact prefixLift 6215051
  have htrace : WordTrace (prefixWord ++ tailWord_6215051) baseStart_6215051 baseEnd_6215051 := by
    simpa [prefixWord, tailWord_6215051, baseEnd_6215051] using wordTrace_append hprefix tailTrace_6215051
  have hstable : (prefixWord ++ tailWord_6215051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215051).length < 2 ^ (prefixWord ++ tailWord_6215051).sum := by decide
  have hdescent : baseEnd_6215051 < baseStart_6215051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215137 : List Nat := [1, 2, 3, 1, 2, 3, 1, 2, 1, 3, 4]
def baseStart_6215137 : Nat := 118140960795 + 6215137 * 2 ^ 59
def prefixEnd_6215137 : Nat := 4983230072969 + 3 ^ 40 * 6215137 * 2
def baseEnd_6215137 : Nat := 3191352614542954981604611

theorem tailTrace_6215137 : CollatzResearch.WordTrace tailWord_6215137 prefixEnd_6215137 3191352614542954981604611 := by
  unfold tailWord_6215137
  simp only [CollatzResearch.WordTrace]
  refine ⟨226684669284627584737491665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151123112856418389824994443 226684669284627584737491665)
  ·
    refine ⟨170013501963470688553118749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226684669284627584737491665 170013501963470688553118749)
    ·
      refine ⟨63755063236301508207419531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170013501963470688553118749 63755063236301508207419531)
      ·
        refine ⟨95632594854452262311129297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63755063236301508207419531 95632594854452262311129297)
        ·
          refine ⟨71724446140839196733346973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95632594854452262311129297 71724446140839196733346973)
          ·
            refine ⟨26896667302814698775005115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71724446140839196733346973 26896667302814698775005115)
            ·
              refine ⟨40345000954222048162507673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26896667302814698775005115 40345000954222048162507673)
              ·
                refine ⟨30258750715666536121880755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40345000954222048162507673 30258750715666536121880755)
                ·
                  refine ⟨45388126073499804182821133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30258750715666536121880755 45388126073499804182821133)
                  ·
                    refine ⟨17020547277562426568557925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45388126073499804182821133 17020547277562426568557925)
                    ·
                      refine ⟨3191352614542954981604611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17020547277562426568557925 3191352614542954981604611)
                      ·
                        rfl

theorem cell23_6215137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_6215137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215137 prefixEnd_6215137 := by exact prefixLift 6215137
  have htrace : WordTrace (prefixWord ++ tailWord_6215137) baseStart_6215137 baseEnd_6215137 := by
    simpa [prefixWord, tailWord_6215137, baseEnd_6215137] using wordTrace_append hprefix tailTrace_6215137
  have hstable : (prefixWord ++ tailWord_6215137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215137).length < 2 ^ (prefixWord ++ tailWord_6215137).sum := by decide
  have hdescent : baseEnd_6215137 < baseStart_6215137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215147 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 5, 4]
def baseStart_6215147 : Nat := 118140960795 + 6215147 * 2 ^ 59
def prefixEnd_6215147 : Nat := 4983230072969 + 3 ^ 40 * 6215147 * 2
def baseEnd_6215147 : Nat := 1063785916449833314159855

theorem tailTrace_6215147 : CollatzResearch.WordTrace tailWord_6215147 prefixEnd_6215147 1063785916449833314159855 := by
  unfold tailWord_6215147
  simp only [CollatzResearch.WordTrace]
  refine ⟨226685034014591356445355695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151123356009727570963570463 226685034014591356445355695)
  ·
    refine ⟨340027551021887034668033543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226685034014591356445355695 340027551021887034668033543)
    ·
      refine ⟨510041326532830552002050315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340027551021887034668033543 510041326532830552002050315)
      ·
        refine ⟨765061989799245828003075473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510041326532830552002050315 765061989799245828003075473)
        ·
          refine ⟨573796492349434371002306605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 765061989799245828003075473 573796492349434371002306605)
          ·
            refine ⟨215173684631037889125864977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 573796492349434371002306605 215173684631037889125864977)
            ·
              refine ⟨161380263473278416844398733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215173684631037889125864977 161380263473278416844398733)
              ·
                refine ⟨60517598802479406316649525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161380263473278416844398733 60517598802479406316649525)
                ·
                  refine ⟨5673524887732444342185893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60517598802479406316649525 5673524887732444342185893)
                  ·
                    refine ⟨1063785916449833314159855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5673524887732444342185893 1063785916449833314159855)
                    ·
                      rfl

theorem cell23_6215147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5, 4].length) (baseStart_6215147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215147 prefixEnd_6215147 := by exact prefixLift 6215147
  have htrace : WordTrace (prefixWord ++ tailWord_6215147) baseStart_6215147 baseEnd_6215147 := by
    simpa [prefixWord, tailWord_6215147, baseEnd_6215147] using wordTrace_append hprefix tailTrace_6215147
  have hstable : (prefixWord ++ tailWord_6215147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215147).length < 2 ^ (prefixWord ++ tailWord_6215147).sum := by decide
  have hdescent : baseEnd_6215147 < baseStart_6215147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215154 : List Nat := [3, 2, 1, 4, 1, 1, 2, 1, 1, 3, 4]
def baseStart_6215154 : Nat := 118140960795 + 6215154 * 2 ^ 59
def prefixEnd_6215154 : Nat := 4983230072969 + 3 ^ 40 * 6215154 * 2
def baseEnd_6215154 : Nat := 3191361343714081415092033

theorem tailTrace_6215154 : CollatzResearch.WordTrace tailWord_6215154 prefixEnd_6215154 3191361343714081415092033 := by
  unfold tailWord_6215154
  simp only [CollatzResearch.WordTrace]
  refine ⟨56671322331391499160215129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151123526217043997760573677 56671322331391499160215129)
  ·
    refine ⟨42503491748543624370161347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56671322331391499160215129 42503491748543624370161347)
    ·
      refine ⟨63755237622815436555242021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42503491748543624370161347 63755237622815436555242021)
      ·
        refine ⟨11954107054277894354107879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63755237622815436555242021 11954107054277894354107879)
        ·
          refine ⟨17931160581416841531161819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11954107054277894354107879 17931160581416841531161819)
          ·
            refine ⟨26896740872125262296742729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17931160581416841531161819 26896740872125262296742729)
            ·
              refine ⟨20172555654093946722557047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26896740872125262296742729 20172555654093946722557047)
              ·
                refine ⟨30258833481140920083835571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20172555654093946722557047 30258833481140920083835571)
                ·
                  refine ⟨45388250221711380125753357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30258833481140920083835571 45388250221711380125753357)
                  ·
                    refine ⟨17020593833141767547157509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45388250221711380125753357 17020593833141767547157509)
                    ·
                      refine ⟨3191361343714081415092033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17020593833141767547157509 3191361343714081415092033)
                      ·
                        rfl

theorem cell23_6215154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_6215154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215154 prefixEnd_6215154 := by exact prefixLift 6215154
  have htrace : WordTrace (prefixWord ++ tailWord_6215154) baseStart_6215154 baseEnd_6215154 := by
    simpa [prefixWord, tailWord_6215154, baseEnd_6215154] using wordTrace_append hprefix tailTrace_6215154
  have hstable : (prefixWord ++ tailWord_6215154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215154).length < 2 ^ (prefixWord ++ tailWord_6215154).sum := by decide
  have hdescent : baseEnd_6215154 < baseStart_6215154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215177 : List Nat := [1, 2, 1, 1, 3, 1, 4, 4, 6]
def baseStart_6215177 : Nat := 118140960795 + 6215177 * 2 ^ 59
def prefixEnd_6215177 : Nat := 4983230072969 + 3 ^ 40 * 6215177 * 2
def baseEnd_6215177 : Nat := 354597017085459425011603

theorem tailTrace_6215177 : CollatzResearch.WordTrace tailWord_6215177 prefixEnd_6215177 354597017085459425011603 := by
  unfold tailWord_6215177
  simp only [CollatzResearch.WordTrace]
  refine ⟨226686128204482671568947785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151124085469655114379298523 226686128204482671568947785)
  ·
    refine ⟨170014596153362003676710839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226686128204482671568947785 170014596153362003676710839)
    ·
      refine ⟨255021894230043005515066259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170014596153362003676710839 255021894230043005515066259)
      ·
        refine ⟨382532841345064508272599389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255021894230043005515066259 382532841345064508272599389)
        ·
          refine ⟨143449815504399190602224771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 382532841345064508272599389 143449815504399190602224771)
          ·
            refine ⟨215174723256598785903337157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143449815504399190602224771 215174723256598785903337157)
            ·
              refine ⟨40345260610612272356875717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 215174723256598785903337157 40345260610612272356875717)
              ·
                refine ⟨7564736364489801066914197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40345260610612272356875717 7564736364489801066914197)
                ·
                  refine ⟨354597017085459425011603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7564736364489801066914197 354597017085459425011603)
                  ·
                    rfl

theorem cell23_6215177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 6].length) (baseStart_6215177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215177 prefixEnd_6215177 := by exact prefixLift 6215177
  have htrace : WordTrace (prefixWord ++ tailWord_6215177) baseStart_6215177 baseEnd_6215177 := by
    simpa [prefixWord, tailWord_6215177, baseEnd_6215177] using wordTrace_append hprefix tailTrace_6215177
  have hstable : (prefixWord ++ tailWord_6215177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215177).length < 2 ^ (prefixWord ++ tailWord_6215177).sum := by decide
  have hdescent : baseEnd_6215177 < baseStart_6215177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215208 : List Nat := [2, 1, 5, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_6215208 : Nat := 118140960795 + 6215208 * 2 ^ 59
def prefixEnd_6215208 : Nat := 4983230072969 + 3 ^ 40 * 6215208 * 2
def baseEnd_6215208 : Nat := 3191389071669424203816785

theorem tailTrace_6215208 : CollatzResearch.WordTrace tailWord_6215208 prefixEnd_6215208 3191389071669424203816785 := by
  unfold tailWord_6215208
  simp only [CollatzResearch.WordTrace]
  refine ⟨113343629433685181931663139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151124839244913575908884185 113343629433685181931663139)
  ·
    refine ⟨170015444150527772897494709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113343629433685181931663139 170015444150527772897494709)
    ·
      refine ⟨15938947889111978709140129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170015444150527772897494709 15938947889111978709140129)
      ·
        refine ⟨11954210916833984031855097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15938947889111978709140129 11954210916833984031855097)
        ·
          refine ⟨8965658187625488023891323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11954210916833984031855097 8965658187625488023891323)
          ·
            refine ⟨13448487281438232035836985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8965658187625488023891323 13448487281438232035836985)
            ·
              refine ⟨10086365461078674026877739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13448487281438232035836985 10086365461078674026877739)
              ·
                refine ⟨15129548191618011040316609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10086365461078674026877739 15129548191618011040316609)
                ·
                  refine ⟨11347161143713508280237457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15129548191618011040316609 11347161143713508280237457)
                  ·
                    refine ⟨8510370857785131210178093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11347161143713508280237457 8510370857785131210178093)
                    ·
                      refine ⟨3191389071669424203816785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8510370857785131210178093 3191389071669424203816785)
                      ·
                        rfl

theorem cell23_6215208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_6215208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215208 prefixEnd_6215208 := by exact prefixLift 6215208
  have htrace : WordTrace (prefixWord ++ tailWord_6215208) baseStart_6215208 baseEnd_6215208 := by
    simpa [prefixWord, tailWord_6215208, baseEnd_6215208] using wordTrace_append hprefix tailTrace_6215208
  have hstable : (prefixWord ++ tailWord_6215208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215208).length < 2 ^ (prefixWord ++ tailWord_6215208).sum := by decide
  have hdescent : baseEnd_6215208 < baseStart_6215208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215231 : List Nat := [1, 1, 2, 2, 3, 3, 2, 2, 2, 3, 2]
def baseStart_6215231 : Nat := 118140960795 + 6215231 * 2 ^ 59
def prefixEnd_6215231 : Nat := 4983230072969 + 3 ^ 40 * 6215231 * 2
def baseEnd_6215231 : Nat := 3191400881724477613829179

theorem tailTrace_6215231 : CollatzResearch.WordTrace tailWord_6215231 prefixEnd_6215231 3191400881724477613829179 := by
  unfold tailWord_6215231
  simp only [CollatzResearch.WordTrace]
  refine ⟨226688097746287038791413547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151125398497524692527609031 226688097746287038791413547)
  ·
    refine ⟨340032146619430558187120321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226688097746287038791413547 340032146619430558187120321)
    ·
      refine ⟨255024109964572918640340241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340032146619430558187120321 255024109964572918640340241)
      ·
        refine ⟨191268082473429688980255181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255024109964572918640340241 191268082473429688980255181)
        ·
          refine ⟨71725530927536133367595693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191268082473429688980255181 71725530927536133367595693)
          ·
            refine ⟨26897074097826050012848385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71725530927536133367595693 26897074097826050012848385)
            ·
              refine ⟨20172805573369537509636289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26897074097826050012848385 20172805573369537509636289)
              ·
                refine ⟨15129604180027153132227217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20172805573369537509636289 15129604180027153132227217)
                ·
                  refine ⟨11347203135020364849170413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15129604180027153132227217 11347203135020364849170413)
                  ·
                    refine ⟨4255201175632636818438905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11347203135020364849170413 4255201175632636818438905)
                    ·
                      refine ⟨3191400881724477613829179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4255201175632636818438905 3191400881724477613829179)
                      ·
                        rfl

theorem cell23_6215231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 3, 2].length) (baseStart_6215231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215231 prefixEnd_6215231 := by exact prefixLift 6215231
  have htrace : WordTrace (prefixWord ++ tailWord_6215231) baseStart_6215231 baseEnd_6215231 := by
    simpa [prefixWord, tailWord_6215231, baseEnd_6215231] using wordTrace_append hprefix tailTrace_6215231
  have hstable : (prefixWord ++ tailWord_6215231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215231).length < 2 ^ (prefixWord ++ tailWord_6215231).sum := by decide
  have hdescent : baseEnd_6215231 < baseStart_6215231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215237 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 3, 6]
def baseStart_6215237 : Nat := 118140960795 + 6215237 * 2 ^ 59
def prefixEnd_6215237 : Nat := 4983230072969 + 3 ^ 40 * 6215237 * 2
def baseEnd_6215237 : Nat := 1063801320869468196784717

theorem tailTrace_6215237 : CollatzResearch.WordTrace tailWord_6215237 prefixEnd_6215237 1063801320869468196784717 := by
  unfold tailWord_6215237
  simp only [CollatzResearch.WordTrace]
  refine ⟨226688316584265301816131965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151125544389510201210754643 226688316584265301816131965)
  ·
    refine ⟨85008118719099488181049487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226688316584265301816131965 85008118719099488181049487)
    ·
      refine ⟨127512178078649232271574231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85008118719099488181049487 127512178078649232271574231)
      ·
        refine ⟨191268267117973848407361347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127512178078649232271574231 191268267117973848407361347)
        ·
          refine ⟨286902400676960772611042021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191268267117973848407361347 286902400676960772611042021)
          ·
            refine ⟨53794200126930144864570379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 286902400676960772611042021 53794200126930144864570379)
            ·
              refine ⟨80691300190395217296855569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53794200126930144864570379 80691300190395217296855569)
              ·
                refine ⟨60518475142796412972641677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80691300190395217296855569 60518475142796412972641677)
                ·
                  refine ⟨22694428178548654864740629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60518475142796412972641677 22694428178548654864740629)
                  ·
                    refine ⟨1063801320869468196784717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22694428178548654864740629 1063801320869468196784717)
                    ·
                      rfl

theorem cell23_6215237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 6].length) (baseStart_6215237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215237 prefixEnd_6215237 := by exact prefixLift 6215237
  have htrace : WordTrace (prefixWord ++ tailWord_6215237) baseStart_6215237 baseEnd_6215237 := by
    simpa [prefixWord, tailWord_6215237, baseEnd_6215237] using wordTrace_append hprefix tailTrace_6215237
  have hstable : (prefixWord ++ tailWord_6215237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215237).length < 2 ^ (prefixWord ++ tailWord_6215237).sum := by decide
  have hdescent : baseEnd_6215237 < baseStart_6215237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215244 : List Nat := [2, 2, 1, 3, 1, 3, 1, 2, 3, 1, 4]
def baseStart_6215244 : Nat := 118140960795 + 6215244 * 2 ^ 59
def prefixEnd_6215244 : Nat := 4983230072969 + 3 ^ 40 * 6215244 * 2
def baseEnd_6215244 : Nat := 3191407556972986062966619

theorem tailTrace_6215244 : CollatzResearch.WordTrace tailWord_6215244 prefixEnd_6215244 3191407556972986062966619 := by
  unfold tailWord_6215244
  simp only [CollatzResearch.WordTrace]
  refine ⟨113344285947619971005818393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151125714596826628007757857 113344285947619971005818393)
  ·
    refine ⟨85008214460714978254363795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113344285947619971005818393 85008214460714978254363795)
    ·
      refine ⟨127512321691072467381545693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85008214460714978254363795 127512321691072467381545693)
      ·
        refine ⟨47817120634152175268079635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127512321691072467381545693 47817120634152175268079635)
        ·
          refine ⟨71725680951228262902119453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47817120634152175268079635 71725680951228262902119453)
          ·
            refine ⟨26897130356710598588294795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71725680951228262902119453 26897130356710598588294795)
            ·
              refine ⟨40345695535065897882442193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26897130356710598588294795 40345695535065897882442193)
              ·
                refine ⟨30259271651299423411831645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40345695535065897882442193 30259271651299423411831645)
                ·
                  refine ⟨11347226869237283779436867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30259271651299423411831645 11347226869237283779436867)
                  ·
                    refine ⟨17020840303855925669155301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11347226869237283779436867 17020840303855925669155301)
                    ·
                      refine ⟨3191407556972986062966619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17020840303855925669155301 3191407556972986062966619)
                      ·
                        rfl

theorem cell23_6215244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_6215244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215244 prefixEnd_6215244 := by exact prefixLift 6215244
  have htrace : WordTrace (prefixWord ++ tailWord_6215244) baseStart_6215244 baseEnd_6215244 := by
    simpa [prefixWord, tailWord_6215244, baseEnd_6215244] using wordTrace_append hprefix tailTrace_6215244
  have hstable : (prefixWord ++ tailWord_6215244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215244).length < 2 ^ (prefixWord ++ tailWord_6215244).sum := by decide
  have hdescent : baseEnd_6215244 < baseStart_6215244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215247 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 5]
def baseStart_6215247 : Nat := 118140960795 + 6215247 * 2 ^ 59
def prefixEnd_6215247 : Nat := 4983230072969 + 3 ^ 40 * 6215247 * 2
def baseEnd_6215247 : Nat := 3191409097414949551229105

theorem tailTrace_6215247 : CollatzResearch.WordTrace tailWord_6215247 prefixEnd_6215247 3191409097414949551229105 := by
  unfold tailWord_6215247
  simp only [CollatzResearch.WordTrace]
  refine ⟨226688681314229073523995995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151125787542819382349330663 226688681314229073523995995)
  ·
    refine ⟨340033021971343610285993993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226688681314229073523995995 340033021971343610285993993)
    ·
      refine ⟨255024766478507707714495495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340033021971343610285993993 255024766478507707714495495)
      ·
        refine ⟨382537149717761561571743243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255024766478507707714495495 382537149717761561571743243)
        ·
          refine ⟨573805724576642342357614865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382537149717761561571743243 573805724576642342357614865)
          ·
            refine ⟨430354293432481756768211149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 573805724576642342357614865 430354293432481756768211149)
            ·
              refine ⟨161382860037180658788079181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 430354293432481756768211149 161382860037180658788079181)
              ·
                refine ⟨60518572513942747045529693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161382860037180658788079181 60518572513942747045529693)
                ·
                  refine ⟨22694464692728530142073635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60518572513942747045529693 22694464692728530142073635)
                  ·
                    refine ⟨34041697039092795213110453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22694464692728530142073635 34041697039092795213110453)
                    ·
                      refine ⟨3191409097414949551229105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34041697039092795213110453 3191409097414949551229105)
                      ·
                        rfl

theorem cell23_6215247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 5].length) (baseStart_6215247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215247 prefixEnd_6215247 := by exact prefixLift 6215247
  have htrace : WordTrace (prefixWord ++ tailWord_6215247) baseStart_6215247 baseEnd_6215247 := by
    simpa [prefixWord, tailWord_6215247, baseEnd_6215247] using wordTrace_append hprefix tailTrace_6215247
  have hstable : (prefixWord ++ tailWord_6215247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215247).length < 2 ^ (prefixWord ++ tailWord_6215247).sum := by decide
  have hdescent : baseEnd_6215247 < baseStart_6215247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215257 : List Nat := [1, 2, 1, 2, 2, 1, 1, 5, 1, 1, 6]
def baseStart_6215257 : Nat := 118140960795 + 6215257 * 2 ^ 59
def prefixEnd_6215257 : Nat := 4983230072969 + 3 ^ 40 * 6215257 * 2
def baseEnd_6215257 : Nat := 3191414232221494512104059

theorem tailTrace_6215257 : CollatzResearch.WordTrace tailWord_6215257 prefixEnd_6215257 3191414232221494512104059 := by
  unfold tailWord_6215257
  simp only [CollatzResearch.WordTrace]
  refine ⟨226689046044192845231860025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151126030696128563487906683 226689046044192845231860025)
  ·
    refine ⟨170016784533144633923895019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226689046044192845231860025 170016784533144633923895019)
    ·
      refine ⟨255025176799716950885842529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170016784533144633923895019 255025176799716950885842529)
      ·
        refine ⟨191268882599787713164381897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255025176799716950885842529 191268882599787713164381897)
        ·
          refine ⟨143451661949840784873286423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191268882599787713164381897 143451661949840784873286423)
          ·
            refine ⟨215177492924761177309929635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143451661949840784873286423 215177492924761177309929635)
            ·
              refine ⟨322766239387141765964894453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215177492924761177309929635 322766239387141765964894453)
              ·
                refine ⟨30259334942544540559208855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 322766239387141765964894453 30259334942544540559208855)
                ·
                  refine ⟨45389002413816810838813283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30259334942544540559208855 45389002413816810838813283)
                  ·
                    refine ⟨68083503620725216258219925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45389002413816810838813283 68083503620725216258219925)
                    ·
                      refine ⟨3191414232221494512104059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68083503620725216258219925 3191414232221494512104059)
                      ·
                        rfl

theorem cell23_6215257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_6215257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215257 prefixEnd_6215257 := by exact prefixLift 6215257
  have htrace : WordTrace (prefixWord ++ tailWord_6215257) baseStart_6215257 baseEnd_6215257 := by
    simpa [prefixWord, tailWord_6215257, baseEnd_6215257] using wordTrace_append hprefix tailTrace_6215257
  have hstable : (prefixWord ++ tailWord_6215257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215257).length < 2 ^ (prefixWord ++ tailWord_6215257).sum := by decide
  have hdescent : baseEnd_6215257 < baseStart_6215257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215278 : List Nat := [4, 1, 2, 2, 3, 1, 1, 3, 1, 1, 4]
def baseStart_6215278 : Nat := 118140960795 + 6215278 * 2 ^ 59
def prefixEnd_6215278 : Nat := 4983230072969 + 3 ^ 40 * 6215278 * 2
def baseEnd_6215278 : Nat := 3191425015315238929941463

theorem tailTrace_6215278 : CollatzResearch.WordTrace tailWord_6215278 prefixEnd_6215278 3191425015315238929941463 := by
  unfold tailWord_6215278
  simp only [CollatzResearch.WordTrace]
  refine ⟨28336226497139595727296811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151126541318077843878916325 28336226497139595727296811)
  ·
    refine ⟨42504339745709393590945217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28336226497139595727296811 42504339745709393590945217)
    ·
      refine ⟨31878254809282045193208913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42504339745709393590945217 31878254809282045193208913)
      ·
        refine ⟨23908691106961533894906685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31878254809282045193208913 23908691106961533894906685)
        ·
          refine ⟨8965759165110575210590007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23908691106961533894906685 8965759165110575210590007)
          ·
            refine ⟨13448638747665862815885011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8965759165110575210590007 13448638747665862815885011)
            ·
              refine ⟨20172958121498794223827517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13448638747665862815885011 20172958121498794223827517)
              ·
                refine ⟨7564859295562047833935319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20172958121498794223827517 7564859295562047833935319)
                ·
                  refine ⟨11347288943343071750902979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7564859295562047833935319 11347288943343071750902979)
                  ·
                    refine ⟨17020933415014607626354469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11347288943343071750902979 17020933415014607626354469)
                    ·
                      refine ⟨3191425015315238929941463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17020933415014607626354469 3191425015315238929941463)
                      ·
                        rfl

theorem cell23_6215278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_6215278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215278 prefixEnd_6215278 := by exact prefixLift 6215278
  have htrace : WordTrace (prefixWord ++ tailWord_6215278) baseStart_6215278 baseEnd_6215278 := by
    simpa [prefixWord, tailWord_6215278, baseEnd_6215278] using wordTrace_append hprefix tailTrace_6215278
  have hstable : (prefixWord ++ tailWord_6215278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215278).length < 2 ^ (prefixWord ++ tailWord_6215278).sum := by decide
  have hdescent : baseEnd_6215278 < baseStart_6215278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215287 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 6]
def baseStart_6215287 : Nat := 118140960795 + 6215287 * 2 ^ 59
def prefixEnd_6215287 : Nat := 4983230072969 + 3 ^ 40 * 6215287 * 2
def baseEnd_6215287 : Nat := 3191429636641129394728921

theorem tailTrace_6215287 : CollatzResearch.WordTrace tailWord_6215287 prefixEnd_6215287 3191429636641129394728921 := by
  unfold tailWord_6215287
  simp only [CollatzResearch.WordTrace]
  refine ⟨226690140234084160355452115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151126760156056106903634743 226690140234084160355452115)
  ·
    refine ⟨340035210351126240533178173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226690140234084160355452115 340035210351126240533178173)
    ·
      refine ⟨127513203881672340199941815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340035210351126240533178173 127513203881672340199941815)
      ·
        refine ⟨191269805822508510299912723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127513203881672340199941815 191269805822508510299912723)
        ·
          refine ⟨286904708733762765449869085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191269805822508510299912723 286904708733762765449869085)
          ·
            refine ⟨107589265775161037043700907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286904708733762765449869085 107589265775161037043700907)
            ·
              refine ⟨161383898662741555565551361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107589265775161037043700907 161383898662741555565551361)
              ·
                refine ⟨121037923997056166674163521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161383898662741555565551361 121037923997056166674163521)
                ·
                  refine ⟨90778442997792125005622641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121037923997056166674163521 90778442997792125005622641)
                  ·
                    refine ⟨68083832248344093754216981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90778442997792125005622641 68083832248344093754216981)
                    ·
                      refine ⟨3191429636641129394728921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68083832248344093754216981 3191429636641129394728921)
                      ·
                        rfl

theorem cell23_6215287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_6215287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215287 prefixEnd_6215287 := by exact prefixLift 6215287
  have htrace : WordTrace (prefixWord ++ tailWord_6215287) baseStart_6215287 baseEnd_6215287 := by
    simpa [prefixWord, tailWord_6215287, baseEnd_6215287] using wordTrace_append hprefix tailTrace_6215287
  have hstable : (prefixWord ++ tailWord_6215287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215287).length < 2 ^ (prefixWord ++ tailWord_6215287).sum := by decide
  have hdescent : baseEnd_6215287 < baseStart_6215287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215372 : List Nat := [2, 2, 1, 5, 2, 2, 1, 2, 1, 3, 2]
def baseStart_6215372 : Nat := 118140960795 + 6215372 * 2 ^ 59
def prefixEnd_6215372 : Nat := 4983230072969 + 3 ^ 40 * 6215372 * 2
def baseEnd_6215372 : Nat := 3191473282496761562166031

theorem tailTrace_6215372 : CollatzResearch.WordTrace tailWord_6215372 prefixEnd_6215372 3191473282496761562166031 := by
  unfold tailWord_6215372
  simp only [CollatzResearch.WordTrace]
  refine ⟨113346620219388109936148185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151128826959184146581530913 113346620219388109936148185)
  ·
    refine ⟨85009965164541082452111139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113346620219388109936148185 85009965164541082452111139)
    ·
      refine ⟨127514947746811623678166709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85009965164541082452111139 127514947746811623678166709)
      ·
        refine ⟨11954526351263589719828129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127514947746811623678166709 11954526351263589719828129)
        ·
          refine ⟨8965894763447692289871097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11954526351263589719828129 8965894763447692289871097)
          ·
            refine ⟨6724421072585769217403323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8965894763447692289871097 6724421072585769217403323)
            ·
              refine ⟨10086631608878653826104985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6724421072585769217403323 10086631608878653826104985)
              ·
                refine ⟨7564973706658990369578739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10086631608878653826104985 7564973706658990369578739)
                ·
                  refine ⟨11347460559988485554368109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7564973706658990369578739 11347460559988485554368109)
                  ·
                    refine ⟨4255297709995682082888041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11347460559988485554368109 4255297709995682082888041)
                    ·
                      refine ⟨3191473282496761562166031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4255297709995682082888041 3191473282496761562166031)
                      ·
                        rfl

theorem cell23_6215372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_6215372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215372 prefixEnd_6215372 := by exact prefixLift 6215372
  have htrace : WordTrace (prefixWord ++ tailWord_6215372) baseStart_6215372 baseEnd_6215372 := by
    simpa [prefixWord, tailWord_6215372, baseEnd_6215372] using wordTrace_append hprefix tailTrace_6215372
  have hstable : (prefixWord ++ tailWord_6215372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215372).length < 2 ^ (prefixWord ++ tailWord_6215372).sum := by decide
  have hdescent : baseEnd_6215372 < baseStart_6215372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215374 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 9]
def baseStart_6215374 : Nat := 118140960795 + 6215374 * 2 ^ 59
def prefixEnd_6215374 : Nat := 4983230072969 + 3 ^ 40 * 6215374 * 2
def baseEnd_6215374 : Nat := 354608256606452283815669

theorem tailTrace_6215374 : CollatzResearch.WordTrace tailWord_6215374 prefixEnd_6215374 354608256606452283815669 := by
  unfold tailWord_6215374
  simp only [CollatzResearch.WordTrace]
  refine ⟨28336664173096121776733647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151128875589845982809246117 28336664173096121776733647)
  ·
    refine ⟨42504996259644182665100471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28336664173096121776733647 42504996259644182665100471)
    ·
      refine ⟨63757494389466273997650707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42504996259644182665100471 63757494389466273997650707)
      ·
        refine ⟨95636241584199410996476061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63757494389466273997650707 95636241584199410996476061)
        ·
          refine ⟨35863590594074779123678523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95636241584199410996476061 35863590594074779123678523)
          ·
            refine ⟨53795385891112168685517785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35863590594074779123678523 53795385891112168685517785)
            ·
              refine ⟨40346539418334126514138339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53795385891112168685517785 40346539418334126514138339)
              ·
                refine ⟨60519809127501189771207509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40346539418334126514138339 60519809127501189771207509)
                ·
                  refine ⟨354608256606452283815669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60519809127501189771207509 354608256606452283815669)
                  ·
                    rfl

theorem cell23_6215374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_6215374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215374 prefixEnd_6215374 := by exact prefixLift 6215374
  have htrace : WordTrace (prefixWord ++ tailWord_6215374) baseStart_6215374 baseEnd_6215374 := by
    simpa [prefixWord, tailWord_6215374, baseEnd_6215374] using wordTrace_append hprefix tailTrace_6215374
  have hstable : (prefixWord ++ tailWord_6215374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215374).length < 2 ^ (prefixWord ++ tailWord_6215374).sum := by decide
  have hdescent : baseEnd_6215374 < baseStart_6215374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215389 : List Nat := [1, 4, 3, 3, 1, 1, 3, 1, 1, 3, 2]
def baseStart_6215389 : Nat := 118140960795 + 6215389 * 2 ^ 59
def prefixEnd_6215389 : Nat := 4983230072969 + 3 ^ 40 * 6215389 * 2
def baseEnd_6215389 : Nat := 3191482011667887995653453

theorem tailTrace_6215389 : CollatzResearch.WordTrace tailWord_6215389 prefixEnd_6215389 3191482011667887995653453 := by
  unfold tailWord_6215389
  simp only [CollatzResearch.WordTrace]
  refine ⟨226693860479714631775665221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151129240319809754517110147 226693860479714631775665221)
  ·
    refine ⟨42505098839946493457937229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226693860479714631775665221 42505098839946493457937229)
    ·
      refine ⟨15939412064979935046726461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42505098839946493457937229 15939412064979935046726461)
      ·
        refine ⟨5977279524367475642522423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15939412064979935046726461 5977279524367475642522423)
        ·
          refine ⟨8965919286551213463783635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5977279524367475642522423 8965919286551213463783635)
          ·
            refine ⟨13448878929826820195675453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8965919286551213463783635 13448878929826820195675453)
            ·
              refine ⟨5043329598685057573378295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13448878929826820195675453 5043329598685057573378295)
              ·
                refine ⟨7564994398027586360067443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5043329598685057573378295 7564994398027586360067443)
                ·
                  refine ⟨11347491597041379540101165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7564994398027586360067443 11347491597041379540101165)
                  ·
                    refine ⟨4255309348890517327537937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11347491597041379540101165 4255309348890517327537937)
                    ·
                      refine ⟨3191482011667887995653453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4255309348890517327537937 3191482011667887995653453)
                      ·
                        rfl

theorem cell23_6215389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_6215389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215389 prefixEnd_6215389 := by exact prefixLift 6215389
  have htrace : WordTrace (prefixWord ++ tailWord_6215389) baseStart_6215389 baseEnd_6215389 := by
    simpa [prefixWord, tailWord_6215389, baseEnd_6215389] using wordTrace_append hprefix tailTrace_6215389
  have hstable : (prefixWord ++ tailWord_6215389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215389).length < 2 ^ (prefixWord ++ tailWord_6215389).sum := by decide
  have hdescent : baseEnd_6215389 < baseStart_6215389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215391 : List Nat := [1, 1, 2, 3, 2, 2, 2, 5, 5]
def baseStart_6215391 : Nat := 118140960795 + 6215391 * 2 ^ 59
def prefixEnd_6215391 : Nat := 4983230072969 + 3 ^ 40 * 6215391 * 2
def baseEnd_6215391 : Nat := 354609226514355220869827

theorem tailTrace_6215391 : CollatzResearch.WordTrace tailWord_6215391 prefixEnd_6215391 354609226514355220869827 := by
  unfold tailWord_6215391
  simp only [CollatzResearch.WordTrace]
  refine ⟨226693933425707386117238027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151129288950471590744825351 226693933425707386117238027)
  ·
    refine ⟨340040900138561079175857041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226693933425707386117238027 340040900138561079175857041)
    ·
      refine ⟨255030675103920809381892781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340040900138561079175857041 255030675103920809381892781)
      ·
        refine ⟨95636503163970303518209793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255030675103920809381892781 95636503163970303518209793)
        ·
          refine ⟨71727377372977727638657345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95636503163970303518209793 71727377372977727638657345)
          ·
            refine ⟨53795533029733295728993009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71727377372977727638657345 53795533029733295728993009)
            ·
              refine ⟨40346649772299971796744757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53795533029733295728993009 40346649772299971796744757)
              ·
                refine ⟨3782498416153122355944821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40346649772299971796744757 3782498416153122355944821)
                ·
                  refine ⟨354609226514355220869827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3782498416153122355944821 354609226514355220869827)
                  ·
                    rfl

theorem cell23_6215391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5, 5].length) (baseStart_6215391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215391 prefixEnd_6215391 := by exact prefixLift 6215391
  have htrace : WordTrace (prefixWord ++ tailWord_6215391) baseStart_6215391 baseEnd_6215391 := by
    simpa [prefixWord, tailWord_6215391, baseEnd_6215391] using wordTrace_append hprefix tailTrace_6215391
  have hstable : (prefixWord ++ tailWord_6215391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215391).length < 2 ^ (prefixWord ++ tailWord_6215391).sum := by decide
  have hdescent : baseEnd_6215391 < baseStart_6215391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215411 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 2, 5, 2]
def baseStart_6215411 : Nat := 118140960795 + 6215411 * 2 ^ 59
def prefixEnd_6215411 : Nat := 4983230072969 + 3 ^ 40 * 6215411 * 2
def baseEnd_6215411 : Nat := 3191493308242286909578351

theorem tailTrace_6215411 : CollatzResearch.WordTrace tailWord_6215411 prefixEnd_6215411 3191493308242286909578351 := by
  unfold tailWord_6215411
  simp only [CollatzResearch.WordTrace]
  refine ⟨226694662885634929532966087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151129775257089953021977391 226694662885634929532966087)
  ·
    refine ⟨340041994328452394299449131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226694662885634929532966087 340041994328452394299449131)
    ·
      refine ⟨510062991492678591449173697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340041994328452394299449131 510062991492678591449173697)
      ·
        refine ⟨382547243619508943586880273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510062991492678591449173697 382547243619508943586880273)
        ·
          refine ⟨286910432714631707690160205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382547243619508943586880273 286910432714631707690160205)
          ·
            refine ⟨107591412267986890383810077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286910432714631707690160205 107591412267986890383810077)
            ·
              refine ⟨40346779600495083893928779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107591412267986890383810077 40346779600495083893928779)
              ·
                refine ⟨60520169400742625840893169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40346779600495083893928779 60520169400742625840893169)
                ·
                  refine ⟨45390127050556969380669877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60520169400742625840893169 45390127050556969380669877)
                  ·
                    refine ⟨4255324410989715879437801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45390127050556969380669877 4255324410989715879437801)
                    ·
                      refine ⟨3191493308242286909578351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4255324410989715879437801 3191493308242286909578351)
                      ·
                        rfl

theorem cell23_6215411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 5, 2].length) (baseStart_6215411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215411 prefixEnd_6215411 := by exact prefixLift 6215411
  have htrace : WordTrace (prefixWord ++ tailWord_6215411) baseStart_6215411 baseEnd_6215411 := by
    simpa [prefixWord, tailWord_6215411, baseEnd_6215411] using wordTrace_append hprefix tailTrace_6215411
  have hstable : (prefixWord ++ tailWord_6215411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215411).length < 2 ^ (prefixWord ++ tailWord_6215411).sum := by decide
  have hdescent : baseEnd_6215411 < baseStart_6215411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215424 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 4]
def baseStart_6215424 : Nat := 118140960795 + 6215424 * 2 ^ 59
def prefixEnd_6215424 : Nat := 4983230072969 + 3 ^ 40 * 6215424 * 2
def baseEnd_6215424 : Nat := 3191499983490795358715791

theorem tailTrace_6215424 : CollatzResearch.WordTrace tailWord_6215424 prefixEnd_6215424 3191499983490795358715791 := by
  unfold tailWord_6215424
  simp only [CollatzResearch.WordTrace]
  refine ⟨113347568517293916376594663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151130091356391888502126217 113347568517293916376594663)
  ·
    refine ⟨170021352775940874564891995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113347568517293916376594663 170021352775940874564891995)
    ·
      refine ⟨255032029163911311847337993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170021352775940874564891995 255032029163911311847337993)
      ·
        refine ⟨191274021872933483885503495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255032029163911311847337993 191274021872933483885503495)
        ·
          refine ⟨286911032809400225828255243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191274021872933483885503495 286911032809400225828255243)
          ·
            refine ⟨430366549214100338742382865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286911032809400225828255243 430366549214100338742382865)
            ·
              refine ⟨322774911910575254056787149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 430366549214100338742382865 322774911910575254056787149)
              ·
                refine ⟨121040591966465720271295181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 322774911910575254056787149 121040591966465720271295181)
                ·
                  refine ⟨45390221987424645101735693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121040591966465720271295181 45390221987424645101735693)
                  ·
                    refine ⟨17021333245284241913150885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45390221987424645101735693 17021333245284241913150885)
                    ·
                      refine ⟨3191499983490795358715791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17021333245284241913150885 3191499983490795358715791)
                      ·
                        rfl

theorem cell23_6215424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_6215424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215424 prefixEnd_6215424 := by exact prefixLift 6215424
  have htrace : WordTrace (prefixWord ++ tailWord_6215424) baseStart_6215424 baseEnd_6215424 := by
    simpa [prefixWord, tailWord_6215424, baseEnd_6215424] using wordTrace_append hprefix tailTrace_6215424
  have hstable : (prefixWord ++ tailWord_6215424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215424).length < 2 ^ (prefixWord ++ tailWord_6215424).sum := by decide
  have hdescent : baseEnd_6215424 < baseStart_6215424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215441 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 3, 6, 2]
def baseStart_6215441 : Nat := 118140960795 + 6215441 * 2 ^ 59
def prefixEnd_6215441 : Nat := 4983230072969 + 3 ^ 40 * 6215441 * 2
def baseEnd_6215441 : Nat := 3191508712661921792203213

theorem tailTrace_6215441 : CollatzResearch.WordTrace tailWord_6215441 prefixEnd_6215441 3191508712661921792203213 := by
  unfold tailWord_6215441
  simp only [CollatzResearch.WordTrace]
  refine ⟨226695757075526244656558177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151130504717017496437705451 226695757075526244656558177)
  ·
    refine ⟨170021817806644683492418633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226695757075526244656558177 170021817806644683492418633)
    ·
      refine ⟨127516363354983512619313975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170021817806644683492418633 127516363354983512619313975)
      ·
        refine ⟨191274545032475268928970963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127516363354983512619313975 191274545032475268928970963)
        ·
          refine ⟨286911817548712903393456445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191274545032475268928970963 286911817548712903393456445)
          ·
            refine ⟨107591931580767338772546167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286911817548712903393456445 107591931580767338772546167)
            ·
              refine ⟨161387897371151008158819251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107591931580767338772546167 161387897371151008158819251)
              ·
                refine ⟨242081846056726512238228877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161387897371151008158819251 242081846056726512238228877)
                ·
                  refine ⟨90780692271272442089335829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 242081846056726512238228877 90780692271272442089335829)
                  ·
                    refine ⟨4255344950215895722937617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90780692271272442089335829 4255344950215895722937617)
                    ·
                      refine ⟨3191508712661921792203213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4255344950215895722937617 3191508712661921792203213)
                      ·
                        rfl

theorem cell23_6215441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 6, 2].length) (baseStart_6215441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215441 prefixEnd_6215441 := by exact prefixLift 6215441
  have htrace : WordTrace (prefixWord ++ tailWord_6215441) baseStart_6215441 baseEnd_6215441 := by
    simpa [prefixWord, tailWord_6215441, baseEnd_6215441] using wordTrace_append hprefix tailTrace_6215441
  have hstable : (prefixWord ++ tailWord_6215441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215441).length < 2 ^ (prefixWord ++ tailWord_6215441).sum := by decide
  have hdescent : baseEnd_6215441 < baseStart_6215441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215458 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 4, 4, 2]
def baseStart_6215458 : Nat := 118140960795 + 6215458 * 2 ^ 59
def prefixEnd_6215458 : Nat := 4983230072969 + 3 ^ 40 * 6215458 * 2
def baseEnd_6215458 : Nat := 3191517441833048225690635

theorem tailTrace_6215458 : CollatzResearch.WordTrace tailWord_6215458 prefixEnd_6215458 3191517441833048225690635 := by
  unfold tailWord_6215458
  simp only [CollatzResearch.WordTrace]
  refine ⟨56674094279116164139981757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151130918077643104373284685 56674094279116164139981757)
  ·
    refine ⟨21252785354668561552493159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56674094279116164139981757 21252785354668561552493159)
    ·
      refine ⟨31879178032002842328739739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21252785354668561552493159 31879178032002842328739739)
      ·
        refine ⟨47818767048004263493109609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31879178032002842328739739 47818767048004263493109609)
        ·
          refine ⟨35864075286003197619832207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47818767048004263493109609 35864075286003197619832207)
          ·
            refine ⟨53796112929004796429748311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35864075286003197619832207 53796112929004796429748311)
            ·
              refine ⟨80694169393507194644622467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53796112929004796429748311 80694169393507194644622467)
              ·
                refine ⟨121041254090260791966933701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80694169393507194644622467 121041254090260791966933701)
                ·
                  refine ⟨22695235141923898493800069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121041254090260791966933701 22695235141923898493800069)
                  ·
                    refine ⟨4255356589110730967587513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22695235141923898493800069 4255356589110730967587513)
                    ·
                      refine ⟨3191517441833048225690635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4255356589110730967587513 3191517441833048225690635)
                      ·
                        rfl

theorem cell23_6215458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_6215458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215458 prefixEnd_6215458 := by exact prefixLift 6215458
  have htrace : WordTrace (prefixWord ++ tailWord_6215458) baseStart_6215458 baseEnd_6215458 := by
    simpa [prefixWord, tailWord_6215458, baseEnd_6215458] using wordTrace_append hprefix tailTrace_6215458
  have hstable : (prefixWord ++ tailWord_6215458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215458).length < 2 ^ (prefixWord ++ tailWord_6215458).sum := by decide
  have hdescent : baseEnd_6215458 < baseStart_6215458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215468 : List Nat := [2, 2, 1, 1, 1, 6, 2, 1, 3, 4]
def baseStart_6215468 : Nat := 118140960795 + 6215468 * 2 ^ 59
def prefixEnd_6215468 : Nat := 4983230072969 + 3 ^ 40 * 6215468 * 2
def baseEnd_6215468 : Nat := 1063840858879864395521863

theorem tailTrace_6215468 : CollatzResearch.WordTrace tailWord_6215468 prefixEnd_6215468 1063840858879864395521863 := by
  unfold tailWord_6215468
  simp only [CollatzResearch.WordTrace]
  refine ⟨113348370923214214133895529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151131161230952285511860705 113348370923214214133895529)
  ·
    refine ⟨85011278192410660600421647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113348370923214214133895529 85011278192410660600421647)
    ·
      refine ⟨127516917288615990900632471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85011278192410660600421647 127516917288615990900632471)
      ·
        refine ⟨191275375932923986350948707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127516917288615990900632471 191275375932923986350948707)
        ·
          refine ⟨286913063899385979526423061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191275375932923986350948707 286913063899385979526423061)
          ·
            refine ⟨13449049870283717790301081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 286913063899385979526423061 13449049870283717790301081)
            ·
              refine ⟨10086787402712788342725811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13449049870283717790301081 10086787402712788342725811)
              ·
                refine ⟨15130181104069182514088717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10086787402712788342725811 15130181104069182514088717)
                ·
                  refine ⟨5673817914025943442783269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15130181104069182514088717 5673817914025943442783269)
                  ·
                    refine ⟨1063840858879864395521863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5673817914025943442783269 1063840858879864395521863)
                    ·
                      rfl

theorem cell23_6215468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 4].length) (baseStart_6215468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215468 prefixEnd_6215468 := by exact prefixLift 6215468
  have htrace : WordTrace (prefixWord ++ tailWord_6215468) baseStart_6215468 baseEnd_6215468 := by
    simpa [prefixWord, tailWord_6215468, baseEnd_6215468] using wordTrace_append hprefix tailTrace_6215468
  have hstable : (prefixWord ++ tailWord_6215468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215468).length < 2 ^ (prefixWord ++ tailWord_6215468).sum := by decide
  have hdescent : baseEnd_6215468 < baseStart_6215468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215531 : List Nat := [1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 4]
def baseStart_6215531 : Nat := 118140960795 + 6215531 * 2 ^ 59
def prefixEnd_6215531 : Nat := 4983230072969 + 3 ^ 40 * 6215531 * 2
def baseEnd_6215531 : Nat := 3191554925920826440077799

theorem tailTrace_6215531 : CollatzResearch.WordTrace tailWord_6215531 prefixEnd_6215531 3191554925920826440077799 := by
  unfold tailWord_6215531
  simp only [CollatzResearch.WordTrace]
  refine ⟨226699039645200190027334447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151132693096800126684889631 226699039645200190027334447)
  ·
    refine ⟨340048559467800285041001671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226699039645200190027334447 340048559467800285041001671)
    ·
      refine ⟨510072839201700427561502507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340048559467800285041001671 510072839201700427561502507)
      ·
        refine ⟨765109258802550641342253761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510072839201700427561502507 765109258802550641342253761)
        ·
          refine ⟨573831944101912981006690321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 765109258802550641342253761 573831944101912981006690321)
          ·
            refine ⟨430373958076434735755017741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 573831944101912981006690321 430373958076434735755017741)
            ·
              refine ⟨161390234278663025908131653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 430373958076434735755017741 161390234278663025908131653)
              ·
                refine ⟨30260668927249317357774685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161390234278663025908131653 30260668927249317357774685)
                ·
                  refine ⟨11347750847718494009165507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30260668927249317357774685 11347750847718494009165507)
                  ·
                    refine ⟨17021626271577741013748261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11347750847718494009165507 17021626271577741013748261)
                    ·
                      refine ⟨3191554925920826440077799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17021626271577741013748261 3191554925920826440077799)
                      ·
                        rfl

theorem cell23_6215531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 4].length) (baseStart_6215531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215531 prefixEnd_6215531 := by exact prefixLift 6215531
  have htrace : WordTrace (prefixWord ++ tailWord_6215531) baseStart_6215531 baseEnd_6215531 := by
    simpa [prefixWord, tailWord_6215531, baseEnd_6215531] using wordTrace_append hprefix tailTrace_6215531
  have hstable : (prefixWord ++ tailWord_6215531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215531).length < 2 ^ (prefixWord ++ tailWord_6215531).sum := by decide
  have hdescent : baseEnd_6215531 < baseStart_6215531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215562 : List Nat := [3, 1, 2, 4, 2, 1, 3, 1, 1, 5]
def baseStart_6215562 : Nat := 118140960795 + 6215562 * 2 ^ 59
def prefixEnd_6215562 : Nat := 4983230072969 + 3 ^ 40 * 6215562 * 2
def baseEnd_6215562 : Nat := 1063856947940371939596719

theorem tailTrace_6215562 : CollatzResearch.WordTrace tailWord_6215562 prefixEnd_6215562 1063856947940371939596719 := by
  unfold tailWord_6215562
  simp only [CollatzResearch.WordTrace]
  refine ⟨56675042577021970580428235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151133446872058588214475293 56675042577021970580428235)
  ·
    refine ⟨85012563865532955870642353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56675042577021970580428235 85012563865532955870642353)
    ·
      refine ⟨63759422899149716902981765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85012563865532955870642353 63759422899149716902981765)
      ·
        refine ⟨11954891793590571919309081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63759422899149716902981765 11954891793590571919309081)
        ·
          refine ⟨8966168845192928939481811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11954891793590571919309081 8966168845192928939481811)
          ·
            refine ⟨13449253267789393409222717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8966168845192928939481811 13449253267789393409222717)
            ·
              refine ⟨5043469975421022528458519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13449253267789393409222717 5043469975421022528458519)
              ·
                refine ⟨7565204963131533792687779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5043469975421022528458519 7565204963131533792687779)
                ·
                  refine ⟨11347807444697300689031669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7565204963131533792687779 11347807444697300689031669)
                  ·
                    refine ⟨1063856947940371939596719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11347807444697300689031669 1063856947940371939596719)
                    ·
                      rfl

theorem cell23_6215562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_6215562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215562 prefixEnd_6215562 := by exact prefixLift 6215562
  have htrace : WordTrace (prefixWord ++ tailWord_6215562) baseStart_6215562 baseEnd_6215562 := by
    simpa [prefixWord, tailWord_6215562, baseEnd_6215562] using wordTrace_append hprefix tailTrace_6215562
  have hstable : (prefixWord ++ tailWord_6215562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215562).length < 2 ^ (prefixWord ++ tailWord_6215562).sum := by decide
  have hdescent : baseEnd_6215562 < baseStart_6215562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215575 : List Nat := [1, 1, 3, 3, 1, 4, 2, 2, 2, 4]
def baseStart_6215575 : Nat := 118140960795 + 6215575 * 2 ^ 59
def prefixEnd_6215575 : Nat := 4983230072969 + 3 ^ 40 * 6215575 * 2
def baseEnd_6215575 : Nat := 1063859173023208089309199

theorem tailTrace_6215575 : CollatzResearch.WordTrace tailWord_6215575 prefixEnd_6215575 1063859173023208089309199 := by
  unfold tailWord_6215575
  simp only [CollatzResearch.WordTrace]
  refine ⟨226700644457040785541936179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151133762971360523694624119 226700644457040785541936179)
  ·
    refine ⟨340050966685561178312904269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226700644457040785541936179 340050966685561178312904269)
    ·
      refine ⟨127519112507085441867339101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340050966685561178312904269 127519112507085441867339101)
      ·
        refine ⟨47819667190157040700252163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127519112507085441867339101 47819667190157040700252163)
        ·
          refine ⟨71729500785235561050378245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47819667190157040700252163 71729500785235561050378245)
          ·
            refine ⟨13449281397231667696945921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71729500785235561050378245 13449281397231667696945921)
            ·
              refine ⟨10086961047923750772709441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13449281397231667696945921 10086961047923750772709441)
              ·
                refine ⟨7565220785942813079532081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10086961047923750772709441 7565220785942813079532081)
                ·
                  refine ⟨5673915589457109809649061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7565220785942813079532081 5673915589457109809649061)
                  ·
                    refine ⟨1063859173023208089309199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5673915589457109809649061 1063859173023208089309199)
                    ·
                      rfl

theorem cell23_6215575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2, 4].length) (baseStart_6215575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215575 prefixEnd_6215575 := by exact prefixLift 6215575
  have htrace : WordTrace (prefixWord ++ tailWord_6215575) baseStart_6215575 baseEnd_6215575 := by
    simpa [prefixWord, tailWord_6215575, baseEnd_6215575] using wordTrace_append hprefix tailTrace_6215575
  have hstable : (prefixWord ++ tailWord_6215575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215575).length < 2 ^ (prefixWord ++ tailWord_6215575).sum := by decide
  have hdescent : baseEnd_6215575 < baseStart_6215575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215588 : List Nat := [2, 3, 1, 2, 1, 5, 1, 8]
def baseStart_6215588 : Nat := 118140960795 + 6215588 * 2 ^ 59
def prefixEnd_6215588 : Nat := 4983230072969 + 3 ^ 40 * 6215588 * 2
def baseEnd_6215588 : Nat := 118206822011782693224631

theorem tailTrace_6215588 : CollatzResearch.WordTrace tailWord_6215588 prefixEnd_6215588 118206822011782693224631 := by
  unfold tailWord_6215588
  simp only [CollatzResearch.WordTrace]
  refine ⟨113350559302996844381079709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151134079070662459174772945 113350559302996844381079709)
  ·
    refine ⟨42506459738623816642904891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113350559302996844381079709 42506459738623816642904891)
    ·
      refine ⟨63759689607935724964357337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42506459738623816642904891 63759689607935724964357337)
      ·
        refine ⟨47819767205951793723268003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63759689607935724964357337 47819767205951793723268003)
        ·
          refine ⟨71729650808927690584902005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47819767205951793723268003 71729650808927690584902005)
          ·
            refine ⟨6724654763336970992334563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71729650808927690584902005 6724654763336970992334563)
            ·
              refine ⟨10086982145005456488501845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6724654763336970992334563 10086982145005456488501845)
              ·
                refine ⟨118206822011782693224631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10086982145005456488501845 118206822011782693224631)
                ·
                  rfl

theorem cell23_6215588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 8].length) (baseStart_6215588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215588 prefixEnd_6215588 := by exact prefixLift 6215588
  have htrace : WordTrace (prefixWord ++ tailWord_6215588) baseStart_6215588 baseEnd_6215588 := by
    simpa [prefixWord, tailWord_6215588, baseEnd_6215588] using wordTrace_append hprefix tailTrace_6215588
  have hstable : (prefixWord ++ tailWord_6215588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215588).length < 2 ^ (prefixWord ++ tailWord_6215588).sum := by decide
  have hdescent : baseEnd_6215588 < baseStart_6215588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215592 : List Nat := [2, 1, 6, 2, 1, 1, 2, 1, 1, 6]
def baseStart_6215592 : Nat := 118140960795 + 6215592 * 2 ^ 59
def prefixEnd_6215592 : Nat := 4983230072969 + 3 ^ 40 * 6215592 * 2
def baseEnd_6215592 : Nat := 1063862082746916900471673

theorem tailTrace_6215592 : CollatzResearch.WordTrace tailWord_6215592 prefixEnd_6215592 1063862082746916900471673 := by
  unfold tailWord_6215592
  simp only [CollatzResearch.WordTrace]
  refine ⟨113350632248989598722652515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151134176331986131630203353 113350632248989598722652515)
  ·
    refine ⟨170025948373484398083978773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113350632248989598722652515 170025948373484398083978773)
    ·
      refine ⟨7969966330007081160186505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 170025948373484398083978773 7969966330007081160186505)
      ·
        refine ⟨5977474747505310870139879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7969966330007081160186505 5977474747505310870139879)
        ·
          refine ⟨8966212121257966305209819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5977474747505310870139879 8966212121257966305209819)
          ·
            refine ⟨13449318181886949457814729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8966212121257966305209819 13449318181886949457814729)
            ·
              refine ⟨10086988636415212093361047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13449318181886949457814729 10086988636415212093361047)
              ·
                refine ⟨15130482954622818140041571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10086988636415212093361047 15130482954622818140041571)
                ·
                  refine ⟨22695724431934227210062357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15130482954622818140041571 22695724431934227210062357)
                  ·
                    refine ⟨1063862082746916900471673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22695724431934227210062357 1063862082746916900471673)
                    ·
                      rfl

theorem cell23_6215592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_6215592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215592 prefixEnd_6215592 := by exact prefixLift 6215592
  have htrace : WordTrace (prefixWord ++ tailWord_6215592) baseStart_6215592 baseEnd_6215592 := by
    simpa [prefixWord, tailWord_6215592, baseEnd_6215592] using wordTrace_append hprefix tailTrace_6215592
  have hstable : (prefixWord ++ tailWord_6215592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215592).length < 2 ^ (prefixWord ++ tailWord_6215592).sum := by decide
  have hdescent : baseEnd_6215592 < baseStart_6215592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215621 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 1, 5, 4]
def baseStart_6215621 : Nat := 118140960795 + 6215621 * 2 ^ 59
def prefixEnd_6215621 : Nat := 4983230072969 + 3 ^ 40 * 6215621 * 2
def baseEnd_6215621 : Nat := 3191601139179731087952385

theorem tailTrace_6215621 : CollatzResearch.WordTrace tailWord_6215621 prefixEnd_6215621 3191601139179731087952385 := by
  unfold tailWord_6215621
  simp only [CollatzResearch.WordTrace]
  refine ⟨226702322214874135398110717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151134881476582756932073811 226702322214874135398110717)
  ·
    refine ⟨85013370830577800774291519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226702322214874135398110717 85013370830577800774291519)
    ·
      refine ⟨127520056245866701161437279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85013370830577800774291519 127520056245866701161437279)
      ·
        refine ⟨191280084368800051742155919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127520056245866701161437279 191280084368800051742155919)
        ·
          refine ⟨286920126553200077613233879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191280084368800051742155919 286920126553200077613233879)
          ·
            refine ⟨430380189829800116419850819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286920126553200077613233879 430380189829800116419850819)
            ·
              refine ⟨645570284744700174629776229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430380189829800116419850819 645570284744700174629776229)
              ·
                refine ⟨121044428389631282743083043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 645570284744700174629776229 121044428389631282743083043)
                ·
                  refine ⟨181566642584446924114624565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121044428389631282743083043 181566642584446924114624565)
                  ·
                    refine ⟨17021872742291899135746053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 181566642584446924114624565 17021872742291899135746053)
                    ·
                      refine ⟨3191601139179731087952385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17021872742291899135746053 3191601139179731087952385)
                      ·
                        rfl

theorem cell23_6215621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_6215621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215621 prefixEnd_6215621 := by exact prefixLift 6215621
  have htrace : WordTrace (prefixWord ++ tailWord_6215621) baseStart_6215621 baseEnd_6215621 := by
    simpa [prefixWord, tailWord_6215621, baseEnd_6215621] using wordTrace_append hprefix tailTrace_6215621
  have hstable : (prefixWord ++ tailWord_6215621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215621).length < 2 ^ (prefixWord ++ tailWord_6215621).sum := by decide
  have hdescent : baseEnd_6215621 < baseStart_6215621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215625 : List Nat := [1, 2, 1, 1, 2, 1, 2, 7, 1, 3, 2]
def baseStart_6215625 : Nat := 118140960795 + 6215625 * 2 ^ 59
def prefixEnd_6215625 : Nat := 4983230072969 + 3 ^ 40 * 6215625 * 2
def baseEnd_6215625 : Nat := 3191603193102349072302367

theorem tailTrace_6215625 : CollatzResearch.WordTrace tailWord_6215625 prefixEnd_6215625 3191603193102349072302367 := by
  unfold tailWord_6215625
  simp only [CollatzResearch.WordTrace]
  refine ⟨226702468106859644081256329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151134978737906429387504219 226702468106859644081256329)
  ·
    refine ⟨170026851080144733060942247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226702468106859644081256329 170026851080144733060942247)
    ·
      refine ⟨255040276620217099591413371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170026851080144733060942247 255040276620217099591413371)
      ·
        refine ⟨382560414930325649387120057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255040276620217099591413371 382560414930325649387120057)
        ·
          refine ⟨286920311197744237040340043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382560414930325649387120057 286920311197744237040340043)
          ·
            refine ⟨430380466796616355560510065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286920311197744237040340043 430380466796616355560510065)
            ·
              refine ⟨322785350097462266670382549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 430380466796616355560510065 322785350097462266670382549)
              ·
                refine ⟨7565281642909271875087091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 322785350097462266670382549 7565281642909271875087091)
                ·
                  refine ⟨11347922464363907812630637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7565281642909271875087091 11347922464363907812630637)
                  ·
                    refine ⟨4255470924136465429736489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11347922464363907812630637 4255470924136465429736489)
                    ·
                      refine ⟨3191603193102349072302367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4255470924136465429736489 3191603193102349072302367)
                      ·
                        rfl

theorem cell23_6215625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 3, 2].length) (baseStart_6215625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215625 prefixEnd_6215625 := by exact prefixLift 6215625
  have htrace : WordTrace (prefixWord ++ tailWord_6215625) baseStart_6215625 baseEnd_6215625 := by
    simpa [prefixWord, tailWord_6215625, baseEnd_6215625] using wordTrace_append hprefix tailTrace_6215625
  have hstable : (prefixWord ++ tailWord_6215625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215625).length < 2 ^ (prefixWord ++ tailWord_6215625).sum := by decide
  have hdescent : baseEnd_6215625 < baseStart_6215625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215631 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 4, 6]
def baseStart_6215631 : Nat := 118140960795 + 6215631 * 2 ^ 59
def prefixEnd_6215631 : Nat := 4983230072969 + 3 ^ 40 * 6215631 * 2
def baseEnd_6215631 : Nat := 1063868757995425349609113

theorem tailTrace_6215631 : CollatzResearch.WordTrace tailWord_6215631 prefixEnd_6215631 1063868757995425349609113 := by
  unfold tailWord_6215631
  simp only [CollatzResearch.WordTrace]
  refine ⟨226702686944837907105974747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151135124629891938070649831 226702686944837907105974747)
  ·
    refine ⟨340054030417256860658962121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226702686944837907105974747 340054030417256860658962121)
    ·
      refine ⟨255040522812942645494221591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340054030417256860658962121 255040522812942645494221591)
      ·
        refine ⟨382560784219413968241332387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255040522812942645494221591 382560784219413968241332387)
        ·
          refine ⟨573841176329120952361998581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382560784219413968241332387 573841176329120952361998581)
          ·
            refine ⟨53797610280855089283937367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 573841176329120952361998581 53797610280855089283937367)
            ·
              refine ⟨80696415421282633925906051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53797610280855089283937367 80696415421282633925906051)
              ·
                refine ⟨121044623131923950888859077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80696415421282633925906051 121044623131923950888859077)
                ·
                  refine ⟨22695866837235740791661077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121044623131923950888859077 22695866837235740791661077)
                  ·
                    refine ⟨1063868757995425349609113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22695866837235740791661077 1063868757995425349609113)
                    ·
                      rfl

theorem cell23_6215631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 6].length) (baseStart_6215631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215631 prefixEnd_6215631 := by exact prefixLift 6215631
  have htrace : WordTrace (prefixWord ++ tailWord_6215631) baseStart_6215631 baseEnd_6215631 := by
    simpa [prefixWord, tailWord_6215631, baseEnd_6215631] using wordTrace_append hprefix tailTrace_6215631
  have hstable : (prefixWord ++ tailWord_6215631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215631).length < 2 ^ (prefixWord ++ tailWord_6215631).sum := by decide
  have hdescent : baseEnd_6215631 < baseStart_6215631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215658 : List Nat := [3, 1, 3, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_6215658 : Nat := 118140960795 + 6215658 * 2 ^ 59
def prefixEnd_6215658 : Nat := 4983230072969 + 3 ^ 40 * 6215658 * 2
def baseEnd_6215658 : Nat := 3191620137963947443189715

theorem tailTrace_6215658 : CollatzResearch.WordTrace tailWord_6215658 prefixEnd_6215658 3191620137963947443189715 := by
  unfold tailWord_6215658
  simp only [CollatzResearch.WordTrace]
  refine ⟨56675917928935022679301907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151135781143826727144805085 56675917928935022679301907)
  ·
    refine ⟨85013876893402534018952861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56675917928935022679301907 85013876893402534018952861)
    ·
      refine ⟨31880203835025950257107323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85013876893402534018952861 31880203835025950257107323)
      ·
        refine ⟨47820305752538925385660985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31880203835025950257107323 47820305752538925385660985)
        ·
          refine ⟨35865229314404194039245739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47820305752538925385660985 35865229314404194039245739)
          ·
            refine ⟨53797843971606291058868609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35865229314404194039245739 53797843971606291058868609)
            ·
              refine ⟨40348382978704718294151457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53797843971606291058868609 40348382978704718294151457)
              ·
                refine ⟨30261287234028538720613593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40348382978704718294151457 30261287234028538720613593)
                ·
                  refine ⟨22695965425521404040460195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30261287234028538720613593 22695965425521404040460195)
                  ·
                    refine ⟨34043948138282106060690293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22695965425521404040460195 34043948138282106060690293)
                    ·
                      refine ⟨3191620137963947443189715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34043948138282106060690293 3191620137963947443189715)
                      ·
                        rfl

theorem cell23_6215658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_6215658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215658 prefixEnd_6215658 := by exact prefixLift 6215658
  have htrace : WordTrace (prefixWord ++ tailWord_6215658) baseStart_6215658 baseEnd_6215658 := by
    simpa [prefixWord, tailWord_6215658, baseEnd_6215658] using wordTrace_append hprefix tailTrace_6215658
  have hstable : (prefixWord ++ tailWord_6215658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215658).length < 2 ^ (prefixWord ++ tailWord_6215658).sum := by decide
  have hdescent : baseEnd_6215658 < baseStart_6215658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215700 : List Nat := [2, 4, 3, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_6215700 : Nat := 118140960795 + 6215700 * 2 ^ 59
def prefixEnd_6215700 : Nat := 4983230072969 + 3 ^ 40 * 6215700 * 2
def baseEnd_6215700 : Nat := 3191641704151436278864523

theorem tailTrace_6215700 : CollatzResearch.WordTrace tailWord_6215700 prefixEnd_6215700 3191641704151436278864523 := by
  unfold tailWord_6215700
  simp only [CollatzResearch.WordTrace]
  refine ⟨113352601790793965945118277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151136802387725287926824369 113352601790793965945118277)
  ·
    refine ⟨21253612835773868614709677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113352601790793965945118277 21253612835773868614709677)
    ·
      refine ⟨7970104813415200730516129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21253612835773868614709677 7970104813415200730516129)
      ·
        refine ⟨5977578610061400547887097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7970104813415200730516129 5977578610061400547887097)
        ·
          refine ⟨4483183957546050410915323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5977578610061400547887097 4483183957546050410915323)
          ·
            refine ⟨6724775936319075616372985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4483183957546050410915323 6724775936319075616372985)
            ·
              refine ⟨5043581952239306712279739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6724775936319075616372985 5043581952239306712279739)
              ·
                refine ⟨7565372928358960068419609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5043581952239306712279739 7565372928358960068419609)
                ·
                  refine ⟨5674029696269220051314707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7565372928358960068419609 5674029696269220051314707)
                  ·
                    refine ⟨8511044544403830076972061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5674029696269220051314707 8511044544403830076972061)
                    ·
                      refine ⟨3191641704151436278864523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8511044544403830076972061 3191641704151436278864523)
                      ·
                        rfl

theorem cell23_6215700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_6215700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215700 prefixEnd_6215700 := by exact prefixLift 6215700
  have htrace : WordTrace (prefixWord ++ tailWord_6215700) baseStart_6215700 baseEnd_6215700 := by
    simpa [prefixWord, tailWord_6215700, baseEnd_6215700] using wordTrace_append hprefix tailTrace_6215700
  have hstable : (prefixWord ++ tailWord_6215700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215700).length < 2 ^ (prefixWord ++ tailWord_6215700).sum := by decide
  have hdescent : baseEnd_6215700 < baseStart_6215700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215706 : List Nat := [3, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2]
def baseStart_6215706 : Nat := 118140960795 + 6215706 * 2 ^ 59
def prefixEnd_6215706 : Nat := 4983230072969 + 3 ^ 40 * 6215706 * 2
def baseEnd_6215706 : Nat := 3191644785035363255389495

theorem tailTrace_6215706 : CollatzResearch.WordTrace tailWord_6215706 prefixEnd_6215706 3191644785035363255389495 := by
  unfold tailWord_6215706
  simp only [CollatzResearch.WordTrace]
  refine ⟨56676355604891548728738743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151136948279710796609969981 56676355604891548728738743)
  ·
    refine ⟨85014533407337323093108115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56676355604891548728738743 85014533407337323093108115)
    ·
      refine ⟨127521800111005984639662173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85014533407337323093108115 127521800111005984639662173)
      ·
        refine ⟨47820675041627244239873315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127521800111005984639662173 47820675041627244239873315)
        ·
          refine ⟨71731012562440866359809973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47820675041627244239873315 71731012562440866359809973)
          ·
            refine ⟨6724782427728831221232185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71731012562440866359809973 6724782427728831221232185)
            ·
              refine ⟨5043586820796623415924139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6724782427728831221232185 5043586820796623415924139)
              ·
                refine ⟨7565380231194935123886209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5043586820796623415924139 7565380231194935123886209)
                ·
                  refine ⟨5674035173396201342914657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7565380231194935123886209 5674035173396201342914657)
                  ·
                    refine ⟨4255526380047151007185993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5674035173396201342914657 4255526380047151007185993)
                    ·
                      refine ⟨3191644785035363255389495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4255526380047151007185993 3191644785035363255389495)
                      ·
                        rfl

theorem cell23_6215706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_6215706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215706 prefixEnd_6215706 := by exact prefixLift 6215706
  have htrace : WordTrace (prefixWord ++ tailWord_6215706) baseStart_6215706 baseEnd_6215706 := by
    simpa [prefixWord, tailWord_6215706, baseEnd_6215706] using wordTrace_append hprefix tailTrace_6215706
  have hstable : (prefixWord ++ tailWord_6215706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215706).length < 2 ^ (prefixWord ++ tailWord_6215706).sum := by decide
  have hdescent : baseEnd_6215706 < baseStart_6215706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215772 : List Nat := [2, 2, 4, 1, 1, 3, 1, 2, 3, 4]
def baseStart_6215772 : Nat := 118140960795 + 6215772 * 2 ^ 59
def prefixEnd_6215772 : Nat := 4983230072969 + 3 ^ 40 * 6215772 * 2
def baseEnd_6215772 : Nat := 1063892891586186665721397

theorem tailTrace_6215772 : CollatzResearch.WordTrace tailWord_6215772 prefixEnd_6215772 1063892891586186665721397 := by
  unfold tailWord_6215772
  simp only [CollatzResearch.WordTrace]
  refine ⟨113353914818663544093428785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151138553091551392124571713 113353914818663544093428785)
  ·
    refine ⟨85015436113997658070071589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113353914818663544093428785 85015436113997658070071589)
    ·
      refine ⟨15940394271374560888138423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85015436113997658070071589 15940394271374560888138423)
      ·
        refine ⟨23910591407061841332207635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15940394271374560888138423 23910591407061841332207635)
        ·
          refine ⟨35865887110592761998311453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23910591407061841332207635 35865887110592761998311453)
          ·
            refine ⟨13449707666472285749366795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35865887110592761998311453 13449707666472285749366795)
            ·
              refine ⟨20174561499708428624050193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13449707666472285749366795 20174561499708428624050193)
              ·
                refine ⟨15130921124781321468037645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20174561499708428624050193 15130921124781321468037645)
                ·
                  refine ⟨5674095421792995550514117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15130921124781321468037645 5674095421792995550514117)
                  ·
                    refine ⟨1063892891586186665721397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5674095421792995550514117 1063892891586186665721397)
                    ·
                      rfl

theorem cell23_6215772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_6215772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215772 prefixEnd_6215772 := by exact prefixLift 6215772
  have htrace : WordTrace (prefixWord ++ tailWord_6215772) baseStart_6215772 baseEnd_6215772 := by
    simpa [prefixWord, tailWord_6215772, baseEnd_6215772] using wordTrace_append hprefix tailTrace_6215772
  have hstable : (prefixWord ++ tailWord_6215772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215772).length < 2 ^ (prefixWord ++ tailWord_6215772).sum := by decide
  have hdescent : baseEnd_6215772 < baseStart_6215772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215789 : List Nat := [1, 5, 1, 1, 2, 1, 4, 3, 1, 4]
def baseStart_6215789 : Nat := 118140960795 + 6215789 * 2 ^ 59
def prefixEnd_6215789 : Nat := 4983230072969 + 3 ^ 40 * 6215789 * 2
def baseEnd_6215789 : Nat := 1063895801309895476883871

theorem tailTrace_6215789 : CollatzResearch.WordTrace tailWord_6215789 prefixEnd_6215789 1063895801309895476883871 := by
  unfold tailWord_6215789
  simp only [CollatzResearch.WordTrace]
  refine ⟨226708449678265500090226421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151138966452177000060150947 226708449678265500090226421)
  ·
    refine ⟨21253917157337390633458727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 226708449678265500090226421 21253917157337390633458727)
    ·
      refine ⟨31880875736006085950188091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21253917157337390633458727 31880875736006085950188091)
      ·
        refine ⟨47821313604009128925282137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31880875736006085950188091 47821313604009128925282137)
        ·
          refine ⟨35865985203006846693961603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47821313604009128925282137 35865985203006846693961603)
          ·
            refine ⟨53798977804510270040942405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35865985203006846693961603 53798977804510270040942405)
            ·
              refine ⟨10087308338345675632676701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53798977804510270040942405 10087308338345675632676701)
              ·
                refine ⟨3782740626879628362253763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10087308338345675632676701 3782740626879628362253763)
                ·
                  refine ⟨5674110940319442543380645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3782740626879628362253763 5674110940319442543380645)
                  ·
                    refine ⟨1063895801309895476883871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5674110940319442543380645 1063895801309895476883871)
                    ·
                      rfl

theorem cell23_6215789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_6215789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215789 prefixEnd_6215789 := by exact prefixLift 6215789
  have htrace : WordTrace (prefixWord ++ tailWord_6215789) baseStart_6215789 baseEnd_6215789 := by
    simpa [prefixWord, tailWord_6215789, baseEnd_6215789] using wordTrace_append hprefix tailTrace_6215789
  have hstable : (prefixWord ++ tailWord_6215789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215789).length < 2 ^ (prefixWord ++ tailWord_6215789).sum := by decide
  have hdescent : baseEnd_6215789 < baseStart_6215789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215835 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 2, 6, 2]
def baseStart_6215835 : Nat := 118140960795 + 6215835 * 2 ^ 59
def prefixEnd_6215835 : Nat := 4983230072969 + 3 ^ 40 * 6215835 * 2
def baseEnd_6215835 : Nat := 3191711024039793250676401

theorem tailTrace_6215835 : CollatzResearch.WordTrace tailWord_6215835 prefixEnd_6215835 3191711024039793250676401 := by
  unfold tailWord_6215835
  simp only [CollatzResearch.WordTrace]
  refine ⟨226710127436098849946400959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151140084957399233297600639 226710127436098849946400959)
  ·
    refine ⟨340065191154148274919601439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226710127436098849946400959 340065191154148274919601439)
    ·
      refine ⟨510097786731222412379402159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340065191154148274919601439 510097786731222412379402159)
      ·
        refine ⟨765146680096833618569103239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510097786731222412379402159 765146680096833618569103239)
        ·
          refine ⟨1147720020145250427853654859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765146680096833618569103239 1147720020145250427853654859)
          ·
            refine ⟨1721580030217875641780482289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1147720020145250427853654859 1721580030217875641780482289)
            ·
              refine ⟨1291185022663406731335361717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1721580030217875641780482289 1291185022663406731335361717)
              ·
                refine ⟨121048595874694381062690161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1291185022663406731335361717 121048595874694381062690161)
                ·
                  refine ⟨90786446906020785797017621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121048595874694381062690161 90786446906020785797017621)
                  ·
                    refine ⟨4255614698719724334235201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90786446906020785797017621 4255614698719724334235201)
                    ·
                      refine ⟨3191711024039793250676401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4255614698719724334235201 3191711024039793250676401)
                      ·
                        rfl

theorem cell23_6215835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 6, 2].length) (baseStart_6215835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215835 prefixEnd_6215835 := by exact prefixLift 6215835
  have htrace : WordTrace (prefixWord ++ tailWord_6215835) baseStart_6215835 baseEnd_6215835 := by
    simpa [prefixWord, tailWord_6215835, baseEnd_6215835] using wordTrace_append hprefix tailTrace_6215835
  have hstable : (prefixWord ++ tailWord_6215835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215835).length < 2 ^ (prefixWord ++ tailWord_6215835).sum := by decide
  have hdescent : baseEnd_6215835 < baseStart_6215835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215845 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 6, 4]
def baseStart_6215845 : Nat := 118140960795 + 6215845 * 2 ^ 59
def prefixEnd_6215845 : Nat := 4983230072969 + 3 ^ 40 * 6215845 * 2
def baseEnd_6215845 : Nat := 1063905386282112737183785

theorem tailTrace_6215845 : CollatzResearch.WordTrace tailWord_6215845 prefixEnd_6215845 1063905386282112737183785 := by
  unfold tailWord_6215845
  simp only [CollatzResearch.WordTrace]
  refine ⟨226710492166062621654264989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151140328110708414436176659 226710492166062621654264989)
  ·
    refine ⟨85016434562273483120349371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226710492166062621654264989 85016434562273483120349371)
    ·
      refine ⟨127524651843410224680524057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85016434562273483120349371 127524651843410224680524057)
      ·
        refine ⟨95643488882557668510393043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127524651843410224680524057 95643488882557668510393043)
        ·
          refine ⟨143465233323836502765589565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95643488882557668510393043 143465233323836502765589565)
          ·
            refine ⟨53799462496438688537096087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143465233323836502765589565 53799462496438688537096087)
            ·
              refine ⟨80699193744658032805644131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53799462496438688537096087 80699193744658032805644131)
              ·
                refine ⟨121048790616987049208466197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80699193744658032805644131 121048790616987049208466197)
                ·
                  refine ⟨5674162060171267931646853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 121048790616987049208466197 5674162060171267931646853)
                  ·
                    refine ⟨1063905386282112737183785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5674162060171267931646853 1063905386282112737183785)
                    ·
                      rfl

theorem cell23_6215845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6, 4].length) (baseStart_6215845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215845 prefixEnd_6215845 := by exact prefixLift 6215845
  have htrace : WordTrace (prefixWord ++ tailWord_6215845) baseStart_6215845 baseEnd_6215845 := by
    simpa [prefixWord, tailWord_6215845, baseEnd_6215845] using wordTrace_append hprefix tailTrace_6215845
  have hstable : (prefixWord ++ tailWord_6215845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215845).length < 2 ^ (prefixWord ++ tailWord_6215845).sum := by decide
  have hdescent : baseEnd_6215845 < baseStart_6215845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215855 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 5, 2, 3]
def baseStart_6215855 : Nat := 118140960795 + 6215855 * 2 ^ 59
def prefixEnd_6215855 : Nat := 4983230072969 + 3 ^ 40 * 6215855 * 2
def baseEnd_6215855 : Nat := 3191721293652883172426309

theorem tailTrace_6215855 : CollatzResearch.WordTrace tailWord_6215855 prefixEnd_6215855 3191721293652883172426309 := by
  unfold tailWord_6215855
  simp only [CollatzResearch.WordTrace]
  refine ⟨226710856896026393362129019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151140571264017595574752679 226710856896026393362129019)
  ·
    refine ⟨340066285344039590043193529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226710856896026393362129019 340066285344039590043193529)
    ·
      refine ⟨255049714008029692532395147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340066285344039590043193529 255049714008029692532395147)
      ·
        refine ⟨382574571012044538798592721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255049714008029692532395147 382574571012044538798592721)
        ·
          refine ⟨286930928259033404098944541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382574571012044538798592721 286930928259033404098944541)
          ·
            refine ⟨107599098097137526537104203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286930928259033404098944541 107599098097137526537104203)
            ·
              refine ⟨161398647145706289805656305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107599098097137526537104203 161398647145706289805656305)
              ·
                refine ⟨121048985359279717354242229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161398647145706289805656305 121048985359279717354242229)
                ·
                  refine ⟨11348342377432473501960209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121048985359279717354242229 11348342377432473501960209)
                  ·
                    refine ⟨8511256783074355126470157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11348342377432473501960209 8511256783074355126470157)
                    ·
                      refine ⟨3191721293652883172426309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8511256783074355126470157 3191721293652883172426309)
                      ·
                        rfl

theorem cell23_6215855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2, 3].length) (baseStart_6215855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215855 prefixEnd_6215855 := by exact prefixLift 6215855
  have htrace : WordTrace (prefixWord ++ tailWord_6215855) baseStart_6215855 baseEnd_6215855 := by
    simpa [prefixWord, tailWord_6215855, baseEnd_6215855] using wordTrace_append hprefix tailTrace_6215855
  have hstable : (prefixWord ++ tailWord_6215855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215855).length < 2 ^ (prefixWord ++ tailWord_6215855).sum := by decide
  have hdescent : baseEnd_6215855 < baseStart_6215855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215919 : List Nat := [1, 1, 2, 1, 6, 1, 1, 4, 2, 1, 3]
def baseStart_6215919 : Nat := 118140960795 + 6215919 * 2 ^ 59
def prefixEnd_6215919 : Nat := 4983230072969 + 3 ^ 40 * 6215919 * 2
def baseEnd_6215919 : Nat := 3191754156414770922026015

theorem tailTrace_6215919 : CollatzResearch.WordTrace tailWord_6215919 prefixEnd_6215919 3191754156414770922026015 := by
  unfold tailWord_6215919
  simp only [CollatzResearch.WordTrace]
  refine ⟨226713191167794532292458811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151142127445196354861639207 226713191167794532292458811)
  ·
    refine ⟨340069786751691798438688217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226713191167794532292458811 340069786751691798438688217)
    ·
      refine ⟨255052340063768848829016163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340069786751691798438688217 255052340063768848829016163)
      ·
        refine ⟨382578510095653273243524245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255052340063768848829016163 382578510095653273243524245)
        ·
          refine ⟨17933367660733747183290199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 382578510095653273243524245 17933367660733747183290199)
          ·
            refine ⟨26900051491100620774935299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17933367660733747183290199 26900051491100620774935299)
            ·
              refine ⟨40350077236650931162402949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26900051491100620774935299 40350077236650931162402949)
              ·
                refine ⟨7565639481872049592950553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40350077236650931162402949 7565639481872049592950553)
                ·
                  refine ⟨5674229611404037194712915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7565639481872049592950553 5674229611404037194712915)
                  ·
                    refine ⟨8511344417106055792069373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5674229611404037194712915 8511344417106055792069373)
                    ·
                      refine ⟨3191754156414770922026015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8511344417106055792069373 3191754156414770922026015)
                      ·
                        rfl

theorem cell23_6215919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2, 1, 3].length) (baseStart_6215919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215919 prefixEnd_6215919 := by exact prefixLift 6215919
  have htrace : WordTrace (prefixWord ++ tailWord_6215919) baseStart_6215919 baseEnd_6215919 := by
    simpa [prefixWord, tailWord_6215919, baseEnd_6215919] using wordTrace_append hprefix tailTrace_6215919
  have hstable : (prefixWord ++ tailWord_6215919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215919).length < 2 ^ (prefixWord ++ tailWord_6215919).sum := by decide
  have hdescent : baseEnd_6215919 < baseStart_6215919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215935 : List Nat := [1, 1, 2, 2, 1, 4, 3, 1, 2, 6]
def baseStart_6215935 : Nat := 118140960795 + 6215935 * 2 ^ 59
def prefixEnd_6215935 : Nat := 4983230072969 + 3 ^ 40 * 6215935 * 2
def baseEnd_6215935 : Nat := 1063920790701747619808647

theorem tailTrace_6215935 : CollatzResearch.WordTrace tailWord_6215935 prefixEnd_6215935 1063920790701747619808647 := by
  unfold tailWord_6215935
  simp only [CollatzResearch.WordTrace]
  refine ⟨226713774735736567025041259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151142516490491044683360839 226713774735736567025041259)
  ·
    refine ⟨340070662103604850537561889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226713774735736567025041259 340070662103604850537561889)
    ·
      refine ⟨255052996577703637903171417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340070662103604850537561889 255052996577703637903171417)
      ·
        refine ⟨191289747433277728427378563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255052996577703637903171417 191289747433277728427378563)
        ·
          refine ⟨286934621149916592641067845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191289747433277728427378563 286934621149916592641067845)
          ·
            refine ⟨53800241465609361120200221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 286934621149916592641067845 53800241465609361120200221)
            ·
              refine ⟨20175090549603510420075083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53800241465609361120200221 20175090549603510420075083)
              ·
                refine ⟨30262635824405265630112625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20175090549603510420075083 30262635824405265630112625)
                ·
                  refine ⟨22696976868303949222584469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30262635824405265630112625 22696976868303949222584469)
                  ·
                    refine ⟨1063920790701747619808647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22696976868303949222584469 1063920790701747619808647)
                    ·
                      rfl

theorem cell23_6215935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 6].length) (baseStart_6215935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215935 prefixEnd_6215935 := by exact prefixLift 6215935
  have htrace : WordTrace (prefixWord ++ tailWord_6215935) baseStart_6215935 baseEnd_6215935 := by
    simpa [prefixWord, tailWord_6215935, baseEnd_6215935] using wordTrace_append hprefix tailTrace_6215935
  have hstable : (prefixWord ++ tailWord_6215935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215935).length < 2 ^ (prefixWord ++ tailWord_6215935).sum := by decide
  have hdescent : baseEnd_6215935 < baseStart_6215935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215959 : List Nat := [1, 1, 3, 4, 1, 2, 2, 2, 1, 4, 2]
def baseStart_6215959 : Nat := 118140960795 + 6215959 * 2 ^ 59
def prefixEnd_6215959 : Nat := 4983230072969 + 3 ^ 40 * 6215959 * 2
def baseEnd_6215959 : Nat := 3191774695640950765525831

theorem tailTrace_6215959 : CollatzResearch.WordTrace tailWord_6215959 prefixEnd_6215959 3191774695640950765525831 := by
  unfold tailWord_6215959
  simp only [CollatzResearch.WordTrace]
  refine ⟨226714650087649619123914931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151143100058433079415943287 226714650087649619123914931)
  ·
    refine ⟨340071975131474428685872397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226714650087649619123914931 340071975131474428685872397)
    ·
      refine ⟨127526990674302910757202149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340071975131474428685872397 127526990674302910757202149)
      ·
        refine ⟨23911310751431795766975403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127526990674302910757202149 23911310751431795766975403)
        ·
          refine ⟨35866966127147693650463105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23911310751431795766975403 35866966127147693650463105)
          ·
            refine ⟨26900224595360770237847329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35866966127147693650463105 26900224595360770237847329)
            ·
              refine ⟨20175168446520577678385497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26900224595360770237847329 20175168446520577678385497)
              ·
                refine ⟨15131376334890433258789123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20175168446520577678385497 15131376334890433258789123)
                ·
                  refine ⟨22697064502335649888183685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15131376334890433258789123 22697064502335649888183685)
                  ·
                    refine ⟨4255699594187934354034441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22697064502335649888183685 4255699594187934354034441)
                    ·
                      refine ⟨3191774695640950765525831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4255699594187934354034441 3191774695640950765525831)
                      ·
                        rfl

theorem cell23_6215959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_6215959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215959 prefixEnd_6215959 := by exact prefixLift 6215959
  have htrace : WordTrace (prefixWord ++ tailWord_6215959) baseStart_6215959 baseEnd_6215959 := by
    simpa [prefixWord, tailWord_6215959, baseEnd_6215959] using wordTrace_append hprefix tailTrace_6215959
  have hstable : (prefixWord ++ tailWord_6215959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215959).length < 2 ^ (prefixWord ++ tailWord_6215959).sum := by decide
  have hdescent : baseEnd_6215959 < baseStart_6215959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215972 : List Nat := [2, 3, 1, 3, 1, 2, 1, 2, 2, 2, 4]
def baseStart_6215972 : Nat := 118140960795 + 6215972 * 2 ^ 59
def prefixEnd_6215972 : Nat := 4983230072969 + 3 ^ 40 * 6215972 * 2
def baseEnd_6215972 : Nat := 3191781370889459214663271

theorem tailTrace_6215972 : CollatzResearch.WordTrace tailWord_6215972 prefixEnd_6215972 3191781370889459214663271 := by
  unfold tailWord_6215972
  simp only [CollatzResearch.WordTrace]
  refine ⟨113357562118301261172069085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151143416157735014896092113 113357562118301261172069085)
  ·
    refine ⟨42509085794362972939525907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113357562118301261172069085 42509085794362972939525907)
    ·
      refine ⟨63763628691544459409288861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42509085794362972939525907 63763628691544459409288861)
      ·
        refine ⟨23911360759329172278483323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63763628691544459409288861 23911360759329172278483323)
        ·
          refine ⟨35867041138993758417724985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23911360759329172278483323 35867041138993758417724985)
          ·
            refine ⟨26900280854245318813293739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35867041138993758417724985 26900280854245318813293739)
            ·
              refine ⟨40350421281367978219940609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26900280854245318813293739 40350421281367978219940609)
              ·
                refine ⟨30262815961025983664955457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40350421281367978219940609 30262815961025983664955457)
                ·
                  refine ⟨22697111970769487748716593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30262815961025983664955457 22697111970769487748716593)
                  ·
                    refine ⟨17022833978077115811537445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22697111970769487748716593 17022833978077115811537445)
                    ·
                      refine ⟨3191781370889459214663271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17022833978077115811537445 3191781370889459214663271)
                      ·
                        rfl

theorem cell23_6215972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_6215972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215972 prefixEnd_6215972 := by exact prefixLift 6215972
  have htrace : WordTrace (prefixWord ++ tailWord_6215972) baseStart_6215972 baseEnd_6215972 := by
    simpa [prefixWord, tailWord_6215972, baseEnd_6215972] using wordTrace_append hprefix tailTrace_6215972
  have hstable : (prefixWord ++ tailWord_6215972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215972).length < 2 ^ (prefixWord ++ tailWord_6215972).sum := by decide
  have hdescent : baseEnd_6215972 < baseStart_6215972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6215992 : List Nat := [2, 1, 2, 1, 3, 1, 4, 1, 2, 3, 3]
def baseStart_6215992 : Nat := 118140960795 + 6215992 * 2 ^ 59
def prefixEnd_6215992 : Nat := 4983230072969 + 3 ^ 40 * 6215992 * 2
def baseEnd_6215992 : Nat := 3191791640502549136413179

theorem tailTrace_6215992 : CollatzResearch.WordTrace tailWord_6215992 prefixEnd_6215992 3191791640502549136413179 := by
  unfold tailWord_6215992
  simp only [CollatzResearch.WordTrace]
  refine ⟨113357926848265032879933115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151143902464353377173244153 113357926848265032879933115)
  ·
    refine ⟨170036890272397549319899673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113357926848265032879933115 170036890272397549319899673)
    ·
      refine ⟨127527667704298161989924755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170036890272397549319899673 127527667704298161989924755)
      ·
        refine ⟨191291501556447242984887133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127527667704298161989924755 191291501556447242984887133)
        ·
          refine ⟨71734313083667716119332675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191291501556447242984887133 71734313083667716119332675)
          ·
            refine ⟨107601469625501574178999013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71734313083667716119332675 107601469625501574178999013)
            ·
              refine ⟨20175275554781545158562315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107601469625501574178999013 20175275554781545158562315)
              ·
                refine ⟨30262913332172317737843473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20175275554781545158562315 30262913332172317737843473)
                ·
                  refine ⟨22697184999129238303382605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30262913332172317737843473 22697184999129238303382605)
                  ·
                    refine ⟨8511444374673464363768477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22697184999129238303382605 8511444374673464363768477)
                    ·
                      refine ⟨3191791640502549136413179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8511444374673464363768477 3191791640502549136413179)
                      ·
                        rfl

theorem cell23_6215992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 2, 3, 3].length) (baseStart_6215992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6215992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6215992 prefixEnd_6215992 := by exact prefixLift 6215992
  have htrace : WordTrace (prefixWord ++ tailWord_6215992) baseStart_6215992 baseEnd_6215992 := by
    simpa [prefixWord, tailWord_6215992, baseEnd_6215992] using wordTrace_append hprefix tailTrace_6215992
  have hstable : (prefixWord ++ tailWord_6215992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6215992).length < 2 ^ (prefixWord ++ tailWord_6215992).sum := by decide
  have hdescent : baseEnd_6215992 < baseStart_6215992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6215992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216005 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 5, 2, 5]
def baseStart_6216005 : Nat := 118140960795 + 6216005 * 2 ^ 59
def prefixEnd_6216005 : Nat := 4983230072969 + 3 ^ 40 * 6216005 * 2
def baseEnd_6216005 : Nat := 3191798315751057585550619

theorem tailTrace_6216005 : CollatzResearch.WordTrace tailWord_6216005 prefixEnd_6216005 3191798315751057585550619 := by
  unfold tailWord_6216005
  simp only [CollatzResearch.WordTrace]
  refine ⟨226716327845482968980089469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151144218563655312653392979 226716327845482968980089469)
  ·
    refine ⟨85018622942056113367533551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226716327845482968980089469 85018622942056113367533551)
    ·
      refine ⟨127527934413084170051300327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85018622942056113367533551 127527934413084170051300327)
      ·
        refine ⟨191291901619626255076950491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127527934413084170051300327 191291901619626255076950491)
        ·
          refine ⟨286937852429439382615425737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191291901619626255076950491 286937852429439382615425737)
          ·
            refine ⟨215203389322079536961569303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286937852429439382615425737 215203389322079536961569303)
            ·
              refine ⟨322805083983119305442353955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215203389322079536961569303 322805083983119305442353955)
              ·
                refine ⟨484207625974678958163530933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322805083983119305442353955 484207625974678958163530933)
                ·
                  refine ⟨45394464935126152327831025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 484207625974678958163530933 45394464935126152327831025)
                  ·
                    refine ⟨34045848701344614245873269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45394464935126152327831025 34045848701344614245873269)
                    ·
                      refine ⟨3191798315751057585550619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34045848701344614245873269 3191798315751057585550619)
                      ·
                        rfl

theorem cell23_6216005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_6216005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216005 prefixEnd_6216005 := by exact prefixLift 6216005
  have htrace : WordTrace (prefixWord ++ tailWord_6216005) baseStart_6216005 baseEnd_6216005 := by
    simpa [prefixWord, tailWord_6216005, baseEnd_6216005] using wordTrace_append hprefix tailTrace_6216005
  have hstable : (prefixWord ++ tailWord_6216005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216005).length < 2 ^ (prefixWord ++ tailWord_6216005).sum := by decide
  have hdescent : baseEnd_6216005 < baseStart_6216005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216012 : List Nat := [2, 2, 1, 3, 2, 1, 2, 3, 2, 5]
def baseStart_6216012 : Nat := 118140960795 + 6216012 * 2 ^ 59
def prefixEnd_6216012 : Nat := 4983230072969 + 3 ^ 40 * 6216012 * 2
def baseEnd_6216012 : Nat := 1063933970038546352721029

theorem tailTrace_6216012 : CollatzResearch.WordTrace tailWord_6216012 prefixEnd_6216012 1063933970038546352721029 := by
  unfold tailWord_6216012
  simp only [CollatzResearch.WordTrace]
  refine ⟨113358291578228804587797145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151144388770971739450396193 113358291578228804587797145)
  ·
    refine ⟨85018718683671603440847859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113358291578228804587797145 85018718683671603440847859)
    ·
      refine ⟨127528078025507405161271789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85018718683671603440847859 127528078025507405161271789)
      ·
        refine ⟨47823029259565276935476921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127528078025507405161271789 47823029259565276935476921)
        ·
          refine ⟨35867271944673957701607691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47823029259565276935476921 35867271944673957701607691)
          ·
            refine ⟨53800907917010936552411537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35867271944673957701607691 53800907917010936552411537)
            ·
              refine ⟨40350680937758202414308653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53800907917010936552411537 40350680937758202414308653)
              ·
                refine ⟨15131505351659325905365745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40350680937758202414308653 15131505351659325905365745)
                ·
                  refine ⟨11348629013744494429024309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15131505351659325905365745 11348629013744494429024309)
                  ·
                    refine ⟨1063933970038546352721029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11348629013744494429024309 1063933970038546352721029)
                    ·
                      rfl

theorem cell23_6216012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 2, 5].length) (baseStart_6216012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216012 prefixEnd_6216012 := by exact prefixLift 6216012
  have htrace : WordTrace (prefixWord ++ tailWord_6216012) baseStart_6216012 baseEnd_6216012 := by
    simpa [prefixWord, tailWord_6216012, baseEnd_6216012] using wordTrace_append hprefix tailTrace_6216012
  have hstable : (prefixWord ++ tailWord_6216012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216012).length < 2 ^ (prefixWord ++ tailWord_6216012).sum := by decide
  have hdescent : baseEnd_6216012 < baseStart_6216012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216055 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 10]
def baseStart_6216055 : Nat := 118140960795 + 6216055 * 2 ^ 59
def prefixEnd_6216055 : Nat := 4983230072969 + 3 ^ 40 * 6216055 * 2
def baseEnd_6216055 : Nat := 354647109975975821102821

theorem tailTrace_6216055 : CollatzResearch.WordTrace tailWord_6216055 prefixEnd_6216055 354647109975975821102821 := by
  unfold tailWord_6216055
  simp only [CollatzResearch.WordTrace]
  refine ⟨226718151495301827519409619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151145434330201218346273079 226718151495301827519409619)
  ·
    refine ⟨340077227242952741279114429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226718151495301827519409619 340077227242952741279114429)
    ·
      refine ⟨127528960216107277979667911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340077227242952741279114429 127528960216107277979667911)
      ·
        refine ⟨191293440324160916969501867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127528960216107277979667911 191293440324160916969501867)
        ·
          refine ⟨286940160486241375454252801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191293440324160916969501867 286940160486241375454252801)
          ·
            refine ⟨215205120364681031590689601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286940160486241375454252801 215205120364681031590689601)
            ·
              refine ⟨161403840273510773693017201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215205120364681031590689601 161403840273510773693017201)
              ·
                refine ⟨121052880205133080269762901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161403840273510773693017201 121052880205133080269762901)
                ·
                  refine ⟨354647109975975821102821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 121052880205133080269762901 354647109975975821102821)
                  ·
                    rfl

theorem cell23_6216055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 10].length) (baseStart_6216055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216055 prefixEnd_6216055 := by exact prefixLift 6216055
  have htrace : WordTrace (prefixWord ++ tailWord_6216055) baseStart_6216055 baseEnd_6216055 := by
    simpa [prefixWord, tailWord_6216055, baseEnd_6216055] using wordTrace_append hprefix tailTrace_6216055
  have hstable : (prefixWord ++ tailWord_6216055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216055).length < 2 ^ (prefixWord ++ tailWord_6216055).sum := by decide
  have hdescent : baseEnd_6216055 < baseStart_6216055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216093 : List Nat := [1, 4, 2, 1, 4, 1, 1, 4, 1, 4]
def baseStart_6216093 : Nat := 118140960795 + 6216093 * 2 ^ 59
def prefixEnd_6216093 : Nat := 4983230072969 + 3 ^ 40 * 6216093 * 2
def baseEnd_6216093 : Nat := 1063947834016217747083405

theorem tailTrace_6216093 : CollatzResearch.WordTrace tailWord_6216093 prefixEnd_6216093 1063947834016217747083405 := by
  unfold tailWord_6216093
  simp only [CollatzResearch.WordTrace]
  refine ⟨226719537469164160009292933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151146358312776106672861955 226719537469164160009292933)
  ·
    refine ⟨42509913275468280001742425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226719537469164160009292933 42509913275468280001742425)
    ·
      refine ⟨31882434956601210001306819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42509913275468280001742425 31882434956601210001306819)
      ·
        refine ⟨47823652434901815001960229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31882434956601210001306819 47823652434901815001960229)
        ·
          refine ⟨8966934831544090312867543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47823652434901815001960229 8966934831544090312867543)
          ·
            refine ⟨13450402247316135469301315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8966934831544090312867543 13450402247316135469301315)
            ·
              refine ⟨20175603370974203203951973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13450402247316135469301315 20175603370974203203951973)
              ·
                refine ⟨3782925632057663100740995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20175603370974203203951973 3782925632057663100740995)
                ·
                  refine ⟨5674388448086494651111493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3782925632057663100740995 5674388448086494651111493)
                  ·
                    refine ⟨1063947834016217747083405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5674388448086494651111493 1063947834016217747083405)
                    ·
                      rfl

theorem cell23_6216093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_6216093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216093 prefixEnd_6216093 := by exact prefixLift 6216093
  have htrace : WordTrace (prefixWord ++ tailWord_6216093) baseStart_6216093 baseEnd_6216093 := by
    simpa [prefixWord, tailWord_6216093, baseEnd_6216093] using wordTrace_append hprefix tailTrace_6216093
  have hstable : (prefixWord ++ tailWord_6216093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216093).length < 2 ^ (prefixWord ++ tailWord_6216093).sum := by decide
  have hdescent : baseEnd_6216093 < baseStart_6216093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216136 : List Nat := [2, 1, 3, 1, 3, 2, 4, 1, 1, 5]
def baseStart_6216136 : Nat := 118140960795 + 6216136 * 2 ^ 59
def prefixEnd_6216136 : Nat := 4983230072969 + 3 ^ 40 * 6216136 * 2
def baseEnd_6216136 : Nat := 1063955193905598857670839

theorem tailTrace_6216136 : CollatzResearch.WordTrace tailWord_6216136 prefixEnd_6216136 1063955193905598857670839 := by
  unfold tailWord_6216136
  simp only [CollatzResearch.WordTrace]
  refine ⟨113360552904004189176554131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151147403872005585568738841 113360552904004189176554131)
  ·
    refine ⟨170040829356006283764831197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113360552904004189176554131 170040829356006283764831197)
    ·
      refine ⟨63765311008502356411811699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170040829356006283764831197 63765311008502356411811699)
      ·
        refine ⟨95647966512753534617717549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63765311008502356411811699 95647966512753534617717549)
        ·
          refine ⟨35867987442282575481644081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95647966512753534617717549 35867987442282575481644081)
          ·
            refine ⟨26900990581711931611233061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35867987442282575481644081 26900990581711931611233061)
            ·
              refine ⟨5043935734070987177106199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26900990581711931611233061 5043935734070987177106199)
              ·
                refine ⟨7565903601106480765659299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5043935734070987177106199 7565903601106480765659299)
                ·
                  refine ⟨11348855401659721148488949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7565903601106480765659299 11348855401659721148488949)
                  ·
                    refine ⟨1063955193905598857670839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11348855401659721148488949 1063955193905598857670839)
                    ·
                      rfl

theorem cell23_6216136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_6216136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216136 prefixEnd_6216136 := by exact prefixLift 6216136
  have htrace : WordTrace (prefixWord ++ tailWord_6216136) baseStart_6216136 baseEnd_6216136 := by
    simpa [prefixWord, tailWord_6216136, baseEnd_6216136] using wordTrace_append hprefix tailTrace_6216136
  have hstable : (prefixWord ++ tailWord_6216136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216136).length < 2 ^ (prefixWord ++ tailWord_6216136).sum := by decide
  have hdescent : baseEnd_6216136 < baseStart_6216136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216150 : List Nat := [5, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3]
def baseStart_6216150 : Nat := 118140960795 + 6216150 * 2 ^ 59
def prefixEnd_6216150 : Nat := 4983230072969 + 3 ^ 40 * 6216150 * 2
def baseEnd_6216150 : Nat := 3191872770445959518237453

theorem tailTrace_6216150 : CollatzResearch.WordTrace tailWord_6216150 prefixEnd_6216150 3191872770445959518237453 := by
  unfold tailWord_6216150
  simp only [CollatzResearch.WordTrace]
  refine ⟨14170101026872353671507369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151147744286638439162745269 14170101026872353671507369)
  ·
    refine ⟨10627575770154265253630527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14170101026872353671507369 10627575770154265253630527)
    ·
      refine ⟨15941363655231397880445791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10627575770154265253630527 15941363655231397880445791)
      ·
        refine ⟨23912045482847096820668687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15941363655231397880445791 23912045482847096820668687)
        ·
          refine ⟨35868068224270645231003031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23912045482847096820668687 35868068224270645231003031)
          ·
            refine ⟨53802102336405967846504547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35868068224270645231003031 53802102336405967846504547)
            ·
              refine ⟨80703153504608951769756821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53802102336405967846504547 80703153504608951769756821)
              ·
                refine ⟨3782960320528544614207351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80703153504608951769756821 3782960320528544614207351)
                ·
                  refine ⟨5674440480792816921311027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3782960320528544614207351 5674440480792816921311027)
                  ·
                    refine ⟨8511660721189225381966541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5674440480792816921311027 8511660721189225381966541)
                    ·
                      refine ⟨3191872770445959518237453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8511660721189225381966541 3191872770445959518237453)
                      ·
                        rfl

theorem cell23_6216150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_6216150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216150 prefixEnd_6216150 := by exact prefixLift 6216150
  have htrace : WordTrace (prefixWord ++ tailWord_6216150) baseStart_6216150 baseEnd_6216150 := by
    simpa [prefixWord, tailWord_6216150, baseEnd_6216150] using wordTrace_append hprefix tailTrace_6216150
  have hstable : (prefixWord ++ tailWord_6216150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216150).length < 2 ^ (prefixWord ++ tailWord_6216150).sum := by decide
  have hdescent : baseEnd_6216150 < baseStart_6216150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216152 : List Nat := [2, 1, 2, 2, 2, 1, 1, 4, 1, 1, 6]
def baseStart_6216152 : Nat := 118140960795 + 6216152 * 2 ^ 59
def prefixEnd_6216152 : Nat := 4983230072969 + 3 ^ 40 * 6216152 * 2
def baseEnd_6216152 : Nat := 3191873797407268510412443

theorem tailTrace_6216152 : CollatzResearch.WordTrace tailWord_6216152 prefixEnd_6216152 3191873797407268510412443 := by
  unfold tailWord_6216152
  simp only [CollatzResearch.WordTrace]
  refine ⟨113360844687975206542845355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151147792917300275390460473 113360844687975206542845355)
  ·
    refine ⟨170041267031962809814268033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113360844687975206542845355 170041267031962809814268033)
    ·
      refine ⟨127530950273972107360701025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170041267031962809814268033 127530950273972107360701025)
      ·
        refine ⟨95648212705479080520525769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127530950273972107360701025 95648212705479080520525769)
        ·
          refine ⟨71736159529109310390394327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95648212705479080520525769 71736159529109310390394327)
          ·
            refine ⟨107604239293663965585591491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71736159529109310390394327 107604239293663965585591491)
            ·
              refine ⟨161406358940495948378387237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107604239293663965585591491 161406358940495948378387237)
              ·
                refine ⟨30263692301342990320947607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161406358940495948378387237 30263692301342990320947607)
                ·
                  refine ⟨45395538452014485481421411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30263692301342990320947607 45395538452014485481421411)
                  ·
                    refine ⟨68093307678021728222132117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45395538452014485481421411 68093307678021728222132117)
                    ·
                      refine ⟨3191873797407268510412443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68093307678021728222132117 3191873797407268510412443)
                      ·
                        rfl

theorem cell23_6216152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_6216152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216152 prefixEnd_6216152 := by exact prefixLift 6216152
  have htrace : WordTrace (prefixWord ++ tailWord_6216152) baseStart_6216152 baseEnd_6216152 := by
    simpa [prefixWord, tailWord_6216152, baseEnd_6216152] using wordTrace_append hprefix tailTrace_6216152
  have hstable : (prefixWord ++ tailWord_6216152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216152).length < 2 ^ (prefixWord ++ tailWord_6216152).sum := by decide
  have hdescent : baseEnd_6216152 < baseStart_6216152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216159 : List Nat := [1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 5]
def baseStart_6216159 : Nat := 118140960795 + 6216159 * 2 ^ 59
def prefixEnd_6216159 : Nat := 4983230072969 + 3 ^ 40 * 6216159 * 2
def baseEnd_6216159 : Nat := 3191877391771849983024911

theorem tailTrace_6216159 : CollatzResearch.WordTrace tailWord_6216159 prefixEnd_6216159 3191877391771849983024911 := by
  unfold tailWord_6216159
  simp only [CollatzResearch.WordTrace]
  refine ⟨226721944686925053281195531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151147963124616702187463687 226721944686925053281195531)
  ·
    refine ⟨340082917030387579921793297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226721944686925053281195531 340082917030387579921793297)
    ·
      refine ⟨255062187772790684941344973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340082917030387579921793297 255062187772790684941344973)
      ·
        refine ⟨95648320414796506853004365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255062187772790684941344973 95648320414796506853004365)
        ·
          refine ⟨35868120155548690069876637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95648320414796506853004365 35868120155548690069876637)
          ·
            refine ⟨13450545058330758776203739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35868120155548690069876637 13450545058330758776203739)
            ·
              refine ⟨20175817587496138164305609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13450545058330758776203739 20175817587496138164305609)
              ·
                refine ⟨15131863190622103623229207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20175817587496138164305609 15131863190622103623229207)
                ·
                  refine ⟨22697794785933155434843811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15131863190622103623229207 22697794785933155434843811)
                  ·
                    refine ⟨34046692178899733152265717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22697794785933155434843811 34046692178899733152265717)
                    ·
                      refine ⟨3191877391771849983024911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34046692178899733152265717 3191877391771849983024911)
                      ·
                        rfl

theorem cell23_6216159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_6216159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216159 prefixEnd_6216159 := by exact prefixLift 6216159
  have htrace : WordTrace (prefixWord ++ tailWord_6216159) baseStart_6216159 baseEnd_6216159 := by
    simpa [prefixWord, tailWord_6216159, baseEnd_6216159] using wordTrace_append hprefix tailTrace_6216159
  have hstable : (prefixWord ++ tailWord_6216159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216159).length < 2 ^ (prefixWord ++ tailWord_6216159).sum := by decide
  have hdescent : baseEnd_6216159 < baseStart_6216159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216173 : List Nat := [1, 5, 1, 3, 1, 2, 2, 2, 1, 1, 4]
def baseStart_6216173 : Nat := 118140960795 + 6216173 * 2 ^ 59
def prefixEnd_6216173 : Nat := 4983230072969 + 3 ^ 40 * 6216173 * 2
def baseEnd_6216173 : Nat := 3191884580501012928249847

theorem tailTrace_6216173 : CollatzResearch.WordTrace tailWord_6216173 prefixEnd_6216173 3191884580501012928249847 := by
  unfold tailWord_6216173
  simp only [CollatzResearch.WordTrace]
  refine ⟨226722455308874333672205173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151148303539249555781470115 226722455308874333672205173)
  ·
    refine ⟨21255230185206968781769235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 226722455308874333672205173 21255230185206968781769235)
    ·
      refine ⟨31882845277810453172653853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21255230185206968781769235 31882845277810453172653853)
      ·
        refine ⟨11956066979178919939745195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31882845277810453172653853 11956066979178919939745195)
        ·
          refine ⟨17934100468768379909617793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11956066979178919939745195 17934100468768379909617793)
          ·
            refine ⟨13450575351576284932213345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17934100468768379909617793 13450575351576284932213345)
            ·
              refine ⟨10087931513682213699160009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13450575351576284932213345 10087931513682213699160009)
              ·
                refine ⟨7565948635261660274370007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10087931513682213699160009 7565948635261660274370007)
                ·
                  refine ⟨11348922952892490411555011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7565948635261660274370007 11348922952892490411555011)
                  ·
                    refine ⟨17023384429338735617332517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11348922952892490411555011 17023384429338735617332517)
                    ·
                      refine ⟨3191884580501012928249847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17023384429338735617332517 3191884580501012928249847)
                      ·
                        rfl

theorem cell23_6216173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_6216173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216173 prefixEnd_6216173 := by exact prefixLift 6216173
  have htrace : WordTrace (prefixWord ++ tailWord_6216173) baseStart_6216173 baseEnd_6216173 := by
    simpa [prefixWord, tailWord_6216173, baseEnd_6216173] using wordTrace_append hprefix tailTrace_6216173
  have hstable : (prefixWord ++ tailWord_6216173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216173).length < 2 ^ (prefixWord ++ tailWord_6216173).sum := by decide
  have hdescent : baseEnd_6216173 < baseStart_6216173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216176 : List Nat := [2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 3]
def baseStart_6216176 : Nat := 118140960795 + 6216176 * 2 ^ 59
def prefixEnd_6216176 : Nat := 4983230072969 + 3 ^ 40 * 6216176 * 2
def baseEnd_6216176 : Nat := 3191886120942976416512333

theorem tailTrace_6216176 : CollatzResearch.WordTrace tailWord_6216176 prefixEnd_6216176 3191886120942976416512333 := by
  unfold tailWord_6216176
  simp only [CollatzResearch.WordTrace]
  refine ⟨113361282363931732592282191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151148376485242310123042921 113361282363931732592282191)
  ·
    refine ⟨170041923545897598888423287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113361282363931732592282191 170041923545897598888423287)
    ·
      refine ⟨255062885318846398332634931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170041923545897598888423287 255062885318846398332634931)
      ·
        refine ⟨382594327978269597498952397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255062885318846398332634931 382594327978269597498952397)
        ·
          refine ⟨143472872991851099062107149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 382594327978269597498952397 143472872991851099062107149)
          ·
            refine ⟨53802327371944162148290181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143472872991851099062107149 53802327371944162148290181)
            ·
              refine ⟨10087936382239530402804409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53802327371944162148290181 10087936382239530402804409)
              ·
                refine ⟨7565952286679647802103307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10087936382239530402804409 7565952286679647802103307)
                ·
                  refine ⟨11348928430019471703154961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7565952286679647802103307 11348928430019471703154961)
                  ·
                    refine ⟨8511696322514603777366221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11348928430019471703154961 8511696322514603777366221)
                    ·
                      refine ⟨3191886120942976416512333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8511696322514603777366221 3191886120942976416512333)
                      ·
                        rfl

theorem cell23_6216176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 3].length) (baseStart_6216176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216176 prefixEnd_6216176 := by exact prefixLift 6216176
  have htrace : WordTrace (prefixWord ++ tailWord_6216176) baseStart_6216176 baseEnd_6216176 := by
    simpa [prefixWord, tailWord_6216176, baseEnd_6216176] using wordTrace_append hprefix tailTrace_6216176
  have hstable : (prefixWord ++ tailWord_6216176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216176).length < 2 ^ (prefixWord ++ tailWord_6216176).sum := by decide
  have hdescent : baseEnd_6216176 < baseStart_6216176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216189 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 3, 3, 3]
def baseStart_6216189 : Nat := 118140960795 + 6216189 * 2 ^ 59
def prefixEnd_6216189 : Nat := 4983230072969 + 3 ^ 40 * 6216189 * 2
def baseEnd_6216189 : Nat := 3191892796191484865649773

theorem tailTrace_6216189 : CollatzResearch.WordTrace tailWord_6216189 prefixEnd_6216189 3191892796191484865649773 := by
  unfold tailWord_6216189
  simp only [CollatzResearch.WordTrace]
  refine ⟨226723038876816368404787621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151148692584544245603191747 226723038876816368404787621)
  ·
    refine ⟨42510569789403069075897679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226723038876816368404787621 42510569789403069075897679)
    ·
      refine ⟨63765854684104603613846519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42510569789403069075897679 63765854684104603613846519)
      ·
        refine ⟨95648782026156905420769779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63765854684104603613846519 95648782026156905420769779)
        ·
          refine ⟨143473173039235358131154669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95648782026156905420769779 143473173039235358131154669)
          ·
            refine ⟨53802439889713259299183001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143473173039235358131154669 53802439889713259299183001)
            ·
              refine ⟨40351829917284944474387251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53802439889713259299183001 40351829917284944474387251)
              ·
                refine ⟨60527744875927416711580877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40351829917284944474387251 60527744875927416711580877)
                ·
                  refine ⟨22697904328472781266842829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60527744875927416711580877 22697904328472781266842829)
                  ·
                    refine ⟨8511714123177292975066061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22697904328472781266842829 8511714123177292975066061)
                    ·
                      refine ⟨3191892796191484865649773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8511714123177292975066061 3191892796191484865649773)
                      ·
                        rfl

theorem cell23_6216189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_6216189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216189 prefixEnd_6216189 := by exact prefixLift 6216189
  have htrace : WordTrace (prefixWord ++ tailWord_6216189) baseStart_6216189 baseEnd_6216189 := by
    simpa [prefixWord, tailWord_6216189, baseEnd_6216189] using wordTrace_append hprefix tailTrace_6216189
  have hstable : (prefixWord ++ tailWord_6216189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216189).length < 2 ^ (prefixWord ++ tailWord_6216189).sum := by decide
  have hdescent : baseEnd_6216189 < baseStart_6216189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216249 : List Nat := [1, 2, 1, 5, 1, 1, 1, 3, 2, 1, 5]
def baseStart_6216249 : Nat := 118140960795 + 6216249 * 2 ^ 59
def prefixEnd_6216249 : Nat := 4983230072969 + 3 ^ 40 * 6216249 * 2
def baseEnd_6216249 : Nat := 3191923605030754630899497

theorem tailTrace_6216249 : CollatzResearch.WordTrace tailWord_6216249 prefixEnd_6216249 3191923605030754630899497 := by
  unfold tailWord_6216249
  simp only [CollatzResearch.WordTrace]
  refine ⟨226725227256598998651971801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151150151504399332434647867 226725227256598998651971801)
  ·
    refine ⟨170043920442449248988978851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226725227256598998651971801 170043920442449248988978851)
    ·
      refine ⟨255065880663673873483468277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170043920442449248988978851 255065880663673873483468277)
      ·
        refine ⟨23912426312219425639075151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 255065880663673873483468277 23912426312219425639075151)
        ·
          refine ⟨35868639468329138458612727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23912426312219425639075151 35868639468329138458612727)
          ·
            refine ⟨53802959202493707687919091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35868639468329138458612727 53802959202493707687919091)
            ·
              refine ⟨80704438803740561531878637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53802959202493707687919091 80704438803740561531878637)
              ·
                refine ⟨30264164551402710574454489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80704438803740561531878637 30264164551402710574454489)
                ·
                  refine ⟨22698123413552032930840867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30264164551402710574454489 22698123413552032930840867)
                  ·
                    refine ⟨34047185120328049396261301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22698123413552032930840867 34047185120328049396261301)
                    ·
                      refine ⟨3191923605030754630899497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34047185120328049396261301 3191923605030754630899497)
                      ·
                        rfl

theorem cell23_6216249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_6216249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216249 prefixEnd_6216249 := by exact prefixLift 6216249
  have htrace : WordTrace (prefixWord ++ tailWord_6216249) baseStart_6216249 baseEnd_6216249 := by
    simpa [prefixWord, tailWord_6216249, baseEnd_6216249] using wordTrace_append hprefix tailTrace_6216249
  have hstable : (prefixWord ++ tailWord_6216249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216249).length < 2 ^ (prefixWord ++ tailWord_6216249).sum := by decide
  have hdescent : baseEnd_6216249 < baseStart_6216249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216250 : List Nat := [3, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2]
def baseStart_6216250 : Nat := 118140960795 + 6216250 * 2 ^ 59
def prefixEnd_6216250 : Nat := 4983230072969 + 3 ^ 40 * 6216250 * 2
def baseEnd_6216250 : Nat := 3191924118511409126986993

theorem tailTrace_6216250 : CollatzResearch.WordTrace tailWord_6216250 prefixEnd_6216250 3191924118511409126986993 := by
  unfold tailWord_6216250
  simp only [CollatzResearch.WordTrace]
  refine ⟨56681315932398843955689551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151150175819730250548505469 56681315932398843955689551)
  ·
    refine ⟨85021973898598265933534327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56681315932398843955689551 85021973898598265933534327)
    ·
      refine ⟨127532960847897398900301491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85021973898598265933534327 127532960847897398900301491)
      ·
        refine ⟨191299441271846098350452237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127532960847897398900301491 191299441271846098350452237)
        ·
          refine ⟨71737290476942286881419589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191299441271846098350452237 71737290476942286881419589)
          ·
            refine ⟨13450741964426678790266173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71737290476942286881419589 13450741964426678790266173)
            ·
              refine ⟨5044028236660004546349815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13450741964426678790266173 5044028236660004546349815)
              ·
                refine ⟨7566042354990006819524723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5044028236660004546349815 7566042354990006819524723)
                ·
                  refine ⟨11349063532485010229287085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7566042354990006819524723 11349063532485010229287085)
                  ·
                    refine ⟨4255898824681878835982657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11349063532485010229287085 4255898824681878835982657)
                    ·
                      refine ⟨3191924118511409126986993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4255898824681878835982657 3191924118511409126986993)
                      ·
                        rfl

theorem cell23_6216250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2].length) (baseStart_6216250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216250 prefixEnd_6216250 := by exact prefixLift 6216250
  have htrace : WordTrace (prefixWord ++ tailWord_6216250) baseStart_6216250 baseEnd_6216250 := by
    simpa [prefixWord, tailWord_6216250, baseEnd_6216250] using wordTrace_append hprefix tailTrace_6216250
  have hstable : (prefixWord ++ tailWord_6216250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216250).length < 2 ^ (prefixWord ++ tailWord_6216250).sum := by decide
  have hdescent : baseEnd_6216250 < baseStart_6216250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216276 : List Nat := [2, 4, 1, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_6216276 : Nat := 118140960795 + 6216276 * 2 ^ 59
def prefixEnd_6216276 : Nat := 4983230072969 + 3 ^ 40 * 6216276 * 2
def baseEnd_6216276 : Nat := 3191937469008426025261873

theorem tailTrace_6216276 : CollatzResearch.WordTrace tailWord_6216276 prefixEnd_6216276 3191937469008426025261873 := by
  unfold tailWord_6216276
  simp only [CollatzResearch.WordTrace]
  refine ⟨113363106013750591131602341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151150808018334121508803121 113363106013750591131602341)
  ·
    refine ⟨21255582377578235837175439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113363106013750591131602341 21255582377578235837175439)
    ·
      refine ⟨31883373566367353755763159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21255582377578235837175439 31883373566367353755763159)
      ·
        refine ⟨47825060349551030633644739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31883373566367353755763159 47825060349551030633644739)
        ·
          refine ⟨71737590524326545950467109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47825060349551030633644739 71737590524326545950467109)
          ·
            refine ⟨13450798223311227365712583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71737590524326545950467109 13450798223311227365712583)
            ·
              refine ⟨20176197334966841048568875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13450798223311227365712583 20176197334966841048568875)
              ·
                refine ⟨30264296002450261572853313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20176197334966841048568875 30264296002450261572853313)
                ·
                  refine ⟨22698222001837696179639985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30264296002450261572853313 22698222001837696179639985)
                  ·
                    refine ⟨17023666501378272134729989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22698222001837696179639985 17023666501378272134729989)
                    ·
                      refine ⟨3191937469008426025261873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17023666501378272134729989 3191937469008426025261873)
                      ·
                        rfl

theorem cell23_6216276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_6216276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216276 prefixEnd_6216276 := by exact prefixLift 6216276
  have htrace : WordTrace (prefixWord ++ tailWord_6216276) baseStart_6216276 baseEnd_6216276 := by
    simpa [prefixWord, tailWord_6216276, baseEnd_6216276] using wordTrace_append hprefix tailTrace_6216276
  have hstable : (prefixWord ++ tailWord_6216276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216276).length < 2 ^ (prefixWord ++ tailWord_6216276).sum := by decide
  have hdescent : baseEnd_6216276 < baseStart_6216276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216299 : List Nat := [1, 1, 1, 1, 2, 2, 1, 7, 2, 5]
def baseStart_6216299 : Nat := 118140960795 + 6216299 * 2 ^ 59
def prefixEnd_6216299 : Nat := 4983230072969 + 3 ^ 40 * 6216299 * 2
def baseEnd_6216299 : Nat := 1063983093021159811758089

theorem tailTrace_6216299 : CollatzResearch.WordTrace tailWord_6216299 prefixEnd_6216299 1063983093021159811758089 := by
  unfold tailWord_6216299
  simp only [CollatzResearch.WordTrace]
  refine ⟨226727050906417857191291951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151151367270945238127527967 226727050906417857191291951)
  ·
    refine ⟨340090576359626785786937927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226727050906417857191291951 340090576359626785786937927)
    ·
      refine ⟨510135864539440178680406891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340090576359626785786937927 510135864539440178680406891)
      ·
        refine ⟨765203796809160268020610337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510135864539440178680406891 765203796809160268020610337)
        ·
          refine ⟨573902847606870201015457753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 765203796809160268020610337 573902847606870201015457753)
          ·
            refine ⟨430427135705152650761593315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 573902847606870201015457753 430427135705152650761593315)
            ·
              refine ⟨645640703557728976142389973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430427135705152650761593315 645640703557728976142389973)
              ·
                refine ⟨15132203989634272878337265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 645640703557728976142389973 15132203989634272878337265)
                ·
                  refine ⟨11349152992225704658752949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15132203989634272878337265 11349152992225704658752949)
                  ·
                    refine ⟨1063983093021159811758089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11349152992225704658752949 1063983093021159811758089)
                    ·
                      rfl

theorem cell23_6216299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 5].length) (baseStart_6216299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216299 prefixEnd_6216299 := by exact prefixLift 6216299
  have htrace : WordTrace (prefixWord ++ tailWord_6216299) baseStart_6216299 baseEnd_6216299 := by
    simpa [prefixWord, tailWord_6216299, baseEnd_6216299] using wordTrace_append hprefix tailTrace_6216299
  have hstable : (prefixWord ++ tailWord_6216299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216299).length < 2 ^ (prefixWord ++ tailWord_6216299).sum := by decide
  have hdescent : baseEnd_6216299 < baseStart_6216299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216356 : List Nat := [2, 3, 1, 2, 2, 1, 1, 3, 1, 4, 3]
def baseStart_6216356 : Nat := 118140960795 + 6216356 * 2 ^ 59
def prefixEnd_6216356 : Nat := 4983230072969 + 3 ^ 40 * 6216356 * 2
def baseEnd_6216356 : Nat := 3191978547460785712261505

theorem tailTrace_6216356 : CollatzResearch.WordTrace tailWord_6216356 prefixEnd_6216356 3191978547460785712261505 := by
  unfold tailWord_6216356
  simp only [CollatzResearch.WordTrace]
  refine ⟨113364564933605677963058461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151152753244807570617411281 113364564933605677963058461)
  ·
    refine ⟨42511711850102129236146923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113364564933605677963058461 42511711850102129236146923)
    ·
      refine ⟨63767567775153193854220385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42511711850102129236146923 63767567775153193854220385)
      ·
        refine ⟨47825675831364895390665289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63767567775153193854220385 47825675831364895390665289)
        ·
          refine ⟨35869256873523671542998967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47825675831364895390665289 35869256873523671542998967)
          ·
            refine ⟨53803885310285507314498451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35869256873523671542998967 53803885310285507314498451)
            ·
              refine ⟨80705827965428260971747677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53803885310285507314498451 80705827965428260971747677)
              ·
                refine ⟨30264685487035597864405379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80705827965428260971747677 30264685487035597864405379)
                ·
                  refine ⟨45397028230553396796608069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30264685487035597864405379 45397028230553396796608069)
                  ·
                    refine ⟨8511942793228761899364013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45397028230553396796608069 8511942793228761899364013)
                    ·
                      refine ⟨3191978547460785712261505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8511942793228761899364013 3191978547460785712261505)
                      ·
                        rfl

theorem cell23_6216356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_6216356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216356 prefixEnd_6216356 := by exact prefixLift 6216356
  have htrace : WordTrace (prefixWord ++ tailWord_6216356) baseStart_6216356 baseEnd_6216356 := by
    simpa [prefixWord, tailWord_6216356, baseEnd_6216356] using wordTrace_append hprefix tailTrace_6216356
  have hstable : (prefixWord ++ tailWord_6216356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216356).length < 2 ^ (prefixWord ++ tailWord_6216356).sum := by decide
  have hdescent : baseEnd_6216356 < baseStart_6216356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216373 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 4, 2, 3]
def baseStart_6216373 : Nat := 118140960795 + 6216373 * 2 ^ 59
def prefixEnd_6216373 : Nat := 4983230072969 + 3 ^ 40 * 6216373 * 2
def baseEnd_6216373 : Nat := 3191987276631912145748927

theorem tailTrace_6216373 : CollatzResearch.WordTrace tailWord_6216373 prefixEnd_6216373 3191987276631912145748927 := by
  unfold tailWord_6216373
  simp only [CollatzResearch.WordTrace]
  refine ⟨226729749908149767829485773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151153166605433178552990515 226729749908149767829485773)
  ·
    refine ⟨85023656215556162936057165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226729749908149767829485773 85023656215556162936057165)
    ·
      refine ⟨31883871080833561101021437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85023656215556162936057165 31883871080833561101021437)
      ·
        refine ⟨11956451655312585412883039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31883871080833561101021437 11956451655312585412883039)
        ·
          refine ⟨17934677482968878119324559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11956451655312585412883039 17934677482968878119324559)
          ·
            refine ⟨26902016224453317178986839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17934677482968878119324559 26902016224453317178986839)
            ·
              refine ⟨40353024336679975768480259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26902016224453317178986839 40353024336679975768480259)
              ·
                refine ⟨60529536505019963652720389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40353024336679975768480259 60529536505019963652720389)
                ·
                  refine ⟨11349288094691243184885073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60529536505019963652720389 11349288094691243184885073)
                  ·
                    refine ⟨8511966071018432388663805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11349288094691243184885073 8511966071018432388663805)
                    ·
                      refine ⟨3191987276631912145748927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8511966071018432388663805 3191987276631912145748927)
                      ·
                        rfl

theorem cell23_6216373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_6216373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216373 prefixEnd_6216373 := by exact prefixLift 6216373
  have htrace : WordTrace (prefixWord ++ tailWord_6216373) baseStart_6216373 baseEnd_6216373 := by
    simpa [prefixWord, tailWord_6216373, baseEnd_6216373] using wordTrace_append hprefix tailTrace_6216373
  have hstable : (prefixWord ++ tailWord_6216373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216373).length < 2 ^ (prefixWord ++ tailWord_6216373).sum := by decide
  have hdescent : baseEnd_6216373 < baseStart_6216373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216430 : List Nat := [4, 1, 2, 1, 1, 3, 2, 2, 2, 3, 2]
def baseStart_6216430 : Nat := 118140960795 + 6216430 * 2 ^ 59
def prefixEnd_6216430 : Nat := 4983230072969 + 3 ^ 40 * 6216430 * 2
def baseEnd_6216430 : Nat := 3192016545029218422736165

theorem tailTrace_6216430 : CollatzResearch.WordTrace tailWord_6216430 prefixEnd_6216430 3192016545029218422736165 := by
  unfold tailWord_6216430
  simp only [CollatzResearch.WordTrace]
  refine ⟨28341478608617908320538843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151154552579295511042873829 28341478608617908320538843)
  ·
    refine ⟨42512217912926862480808265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28341478608617908320538843 42512217912926862480808265)
    ·
      refine ⟨31884163434695146860606199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42512217912926862480808265 31884163434695146860606199)
      ·
        refine ⟨47826245152042720290909299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31884163434695146860606199 47826245152042720290909299)
        ·
          refine ⟨71739367728064080436363949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47826245152042720290909299 71739367728064080436363949)
          ·
            refine ⟨26902262898024030163636481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71739367728064080436363949 26902262898024030163636481)
            ·
              refine ⟨20176697173518022622727361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26902262898024030163636481 20176697173518022622727361)
              ·
                refine ⟨15132522880138516967045521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20176697173518022622727361 15132522880138516967045521)
                ·
                  refine ⟨11349392160103887725284141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15132522880138516967045521 11349392160103887725284141)
                  ·
                    refine ⟨4256022060038957896981553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11349392160103887725284141 4256022060038957896981553)
                    ·
                      refine ⟨3192016545029218422736165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4256022060038957896981553 3192016545029218422736165)
                      ·
                        rfl

theorem cell23_6216430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_6216430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216430 prefixEnd_6216430 := by exact prefixLift 6216430
  have htrace : WordTrace (prefixWord ++ tailWord_6216430) baseStart_6216430 baseEnd_6216430 := by
    simpa [prefixWord, tailWord_6216430, baseEnd_6216430] using wordTrace_append hprefix tailTrace_6216430
  have hstable : (prefixWord ++ tailWord_6216430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216430).length < 2 ^ (prefixWord ++ tailWord_6216430).sum := by decide
  have hdescent : baseEnd_6216430 < baseStart_6216430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216463 : List Nat := [1, 1, 2, 1, 1, 1, 6, 4, 1, 2, 3]
def baseStart_6216463 : Nat := 118140960795 + 6216463 * 2 ^ 59
def prefixEnd_6216463 : Nat := 4983230072969 + 3 ^ 40 * 6216463 * 2
def baseEnd_6216463 : Nat := 3192033489890816793623513

theorem tailTrace_6216463 : CollatzResearch.WordTrace tailWord_6216463 prefixEnd_6216463 3192033489890816793623513 := by
  unfold tailWord_6216463
  simp only [CollatzResearch.WordTrace]
  refine ⟨226733032477823713200262043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151155354985215808800174695 226733032477823713200262043)
  ·
    refine ⟨340099548716735569800393065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226733032477823713200262043 340099548716735569800393065)
    ·
      refine ⟨255074661537551677350294799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340099548716735569800393065 255074661537551677350294799)
      ·
        refine ⟨382611992306327516025442199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255074661537551677350294799 382611992306327516025442199)
        ·
          refine ⟨573917988459491274038163299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382611992306327516025442199 573917988459491274038163299)
          ·
            refine ⟨860876982689236911057244949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573917988459491274038163299 860876982689236911057244949)
            ·
              refine ⟨40353608563557980205808357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 860876982689236911057244949 40353608563557980205808357)
              ·
                refine ⟨7566301605667121288589067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40353608563557980205808357 7566301605667121288589067)
                ·
                  refine ⟨11349452408500681932883601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7566301605667121288589067 11349452408500681932883601)
                  ·
                    refine ⟨8512089306375511449662701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11349452408500681932883601 8512089306375511449662701)
                    ·
                      refine ⟨3192033489890816793623513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8512089306375511449662701 3192033489890816793623513)
                      ·
                        rfl

theorem cell23_6216463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 2, 3].length) (baseStart_6216463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216463 prefixEnd_6216463 := by exact prefixLift 6216463
  have htrace : WordTrace (prefixWord ++ tailWord_6216463) baseStart_6216463 baseEnd_6216463 := by
    simpa [prefixWord, tailWord_6216463, baseEnd_6216463] using wordTrace_append hprefix tailTrace_6216463
  have hstable : (prefixWord ++ tailWord_6216463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216463).length < 2 ^ (prefixWord ++ tailWord_6216463).sum := by decide
  have hdescent : baseEnd_6216463 < baseStart_6216463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216477 : List Nat := [1, 4, 2, 4, 1, 1, 1, 3, 1, 1, 4]
def baseStart_6216477 : Nat := 118140960795 + 6216477 * 2 ^ 59
def prefixEnd_6216477 : Nat := 4983230072969 + 3 ^ 40 * 6216477 * 2
def baseEnd_6216477 : Nat := 3192040678619979738848449

theorem tailTrace_6216477 : CollatzResearch.WordTrace tailWord_6216477 prefixEnd_6216477 3192040678619979738848449 := by
  unfold tailWord_6216477
  simp only [CollatzResearch.WordTrace]
  refine ⟨226733543099772993591271685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151155695399848662394181123 226733543099772993591271685)
  ·
    refine ⟨42512539331207436298363441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226733543099772993591271685 42512539331207436298363441)
    ·
      refine ⟨31884404498405577223772581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42512539331207436298363441 31884404498405577223772581)
      ·
        refine ⟨5978325843451045729457359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31884404498405577223772581 5978325843451045729457359)
        ·
          refine ⟨8967488765176568594186039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5978325843451045729457359 8967488765176568594186039)
          ·
            refine ⟨13451233147764852891279059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8967488765176568594186039 13451233147764852891279059)
            ·
              refine ⟨20176849721647279336918589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13451233147764852891279059 20176849721647279336918589)
              ·
                refine ⟨7566318645617729751344471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20176849721647279336918589 7566318645617729751344471)
                ·
                  refine ⟨11349477968426594627016707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7566318645617729751344471 11349477968426594627016707)
                  ·
                    refine ⟨17024216952639891940525061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11349477968426594627016707 17024216952639891940525061)
                    ·
                      refine ⟨3192040678619979738848449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17024216952639891940525061 3192040678619979738848449)
                      ·
                        rfl

theorem cell23_6216477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_6216477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216477 prefixEnd_6216477 := by exact prefixLift 6216477
  have htrace : WordTrace (prefixWord ++ tailWord_6216477) baseStart_6216477 baseEnd_6216477 := by
    simpa [prefixWord, tailWord_6216477, baseEnd_6216477] using wordTrace_append hprefix tailTrace_6216477
  have hstable : (prefixWord ++ tailWord_6216477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216477).length < 2 ^ (prefixWord ++ tailWord_6216477).sum := by decide
  have hdescent : baseEnd_6216477 < baseStart_6216477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216480 : List Nat := [2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 3]
def baseStart_6216480 : Nat := 118140960795 + 6216480 * 2 ^ 59
def prefixEnd_6216480 : Nat := 4983230072969 + 3 ^ 40 * 6216480 * 2
def baseEnd_6216480 : Nat := 3192042219061943227110935

theorem tailTrace_6216480 : CollatzResearch.WordTrace tailWord_6216480 prefixEnd_6216480 3192042219061943227110935 := by
  unfold tailWord_6216480
  simp only [CollatzResearch.WordTrace]
  refine ⟨113366826259381062551815447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151155768345841416735753929 113366826259381062551815447)
  ·
    refine ⟨170050239389071593827723171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113366826259381062551815447 170050239389071593827723171)
    ·
      refine ⟨255075359083607390741584757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170050239389071593827723171 255075359083607390741584757)
      ·
        refine ⟨23913314914088192882023571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 255075359083607390741584757 23913314914088192882023571)
        ·
          refine ⟨35869972371132289323035357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23913314914088192882023571 35869972371132289323035357)
          ·
            refine ⟨13451239639174608496138259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35869972371132289323035357 13451239639174608496138259)
            ·
              refine ⟨20176859458761912744207389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13451239639174608496138259 20176859458761912744207389)
              ·
                refine ⟨7566322297035717279077771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20176859458761912744207389 7566322297035717279077771)
                ·
                  refine ⟨11349483445553575918616657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7566322297035717279077771 11349483445553575918616657)
                  ·
                    refine ⟨8512112584165181938962493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11349483445553575918616657 8512112584165181938962493)
                    ·
                      refine ⟨3192042219061943227110935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8512112584165181938962493 3192042219061943227110935)
                      ·
                        rfl

theorem cell23_6216480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_6216480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216480 prefixEnd_6216480 := by exact prefixLift 6216480
  have htrace : WordTrace (prefixWord ++ tailWord_6216480) baseStart_6216480 baseEnd_6216480 := by
    simpa [prefixWord, tailWord_6216480, baseEnd_6216480] using wordTrace_append hprefix tailTrace_6216480
  have hstable : (prefixWord ++ tailWord_6216480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216480).length < 2 ^ (prefixWord ++ tailWord_6216480).sum := by decide
  have hdescent : baseEnd_6216480 < baseStart_6216480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216494 : List Nat := [4, 1, 3, 2, 1, 2, 2, 1, 3, 2, 2]
def baseStart_6216494 : Nat := 118140960795 + 6216494 * 2 ^ 59
def prefixEnd_6216494 : Nat := 4983230072969 + 3 ^ 40 * 6216494 * 2
def baseEnd_6216494 : Nat := 3192049407791106172335871

theorem tailTrace_6216494 : CollatzResearch.WordTrace tailWord_6216494 prefixEnd_6216494 3192049407791106172335871 := by
  unfold tailWord_6216494
  simp only [CollatzResearch.WordTrace]
  refine ⟨28341770392588925686830067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151156108760474270329760357 28341770392588925686830067)
  ·
    refine ⟨42512655588883388530245101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28341770392588925686830067 42512655588883388530245101)
    ·
      refine ⟨15942245845831270698841913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42512655588883388530245101 15942245845831270698841913)
      ·
        refine ⟨11956684384373453024131435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15942245845831270698841913 11956684384373453024131435)
        ·
          refine ⟨17935026576560179536197153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11956684384373453024131435 17935026576560179536197153)
          ·
            refine ⟨13451269932420134652147865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17935026576560179536197153 13451269932420134652147865)
            ·
              refine ⟨10088452449315100989110899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13451269932420134652147865 10088452449315100989110899)
              ·
                refine ⟨15132678673972651483666349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10088452449315100989110899 15132678673972651483666349)
                ·
                  refine ⟨5674754502739744306374881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15132678673972651483666349 5674754502739744306374881)
                  ·
                    refine ⟨4256065877054808229781161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5674754502739744306374881 4256065877054808229781161)
                    ·
                      refine ⟨3192049407791106172335871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4256065877054808229781161 3192049407791106172335871)
                      ·
                        rfl

theorem cell23_6216494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_6216494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216494 prefixEnd_6216494 := by exact prefixLift 6216494
  have htrace : WordTrace (prefixWord ++ tailWord_6216494) baseStart_6216494 baseEnd_6216494 := by
    simpa [prefixWord, tailWord_6216494, baseEnd_6216494] using wordTrace_append hprefix tailTrace_6216494
  have hstable : (prefixWord ++ tailWord_6216494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216494).length < 2 ^ (prefixWord ++ tailWord_6216494).sum := by decide
  have hdescent : baseEnd_6216494 < baseStart_6216494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216526 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 1, 8]
def baseStart_6216526 : Nat := 118140960795 + 6216526 * 2 ^ 59
def prefixEnd_6216526 : Nat := 4983230072969 + 3 ^ 40 * 6216526 * 2
def baseEnd_6216526 : Nat := 1064021946390683349045241

theorem tailTrace_6216526 : CollatzResearch.WordTrace tailWord_6216526 prefixEnd_6216526 1064021946390683349045241 := by
  unfold tailWord_6216526
  simp only [CollatzResearch.WordTrace]
  refine ⟨28341916284574434369975679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151156886851063649973203621 28341916284574434369975679)
  ·
    refine ⟨42512874426861651554963519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28341916284574434369975679 42512874426861651554963519)
    ·
      refine ⟨63769311640292477332445279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42512874426861651554963519 63769311640292477332445279)
      ·
        refine ⟨95653967460438715998667919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63769311640292477332445279 95653967460438715998667919)
        ·
          refine ⟨143480951190658073998001879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95653967460438715998667919 143480951190658073998001879)
          ·
            refine ⟨215221426785987110997002819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143480951190658073998001879 215221426785987110997002819)
            ·
              refine ⟨322832140178980666495504229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215221426785987110997002819 322832140178980666495504229)
              ·
                refine ⟨60531026283558874967907043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 322832140178980666495504229 60531026283558874967907043)
                ·
                  refine ⟨90796539425338312451860565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60531026283558874967907043 90796539425338312451860565)
                  ·
                    refine ⟨1064021946390683349045241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90796539425338312451860565 1064021946390683349045241)
                    ·
                      rfl

theorem cell23_6216526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_6216526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216526 prefixEnd_6216526 := by exact prefixLift 6216526
  have htrace : WordTrace (prefixWord ++ tailWord_6216526) baseStart_6216526 baseEnd_6216526 := by
    simpa [prefixWord, tailWord_6216526, baseEnd_6216526] using wordTrace_append hprefix tailTrace_6216526
  have hstable : (prefixWord ++ tailWord_6216526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216526).length < 2 ^ (prefixWord ++ tailWord_6216526).sum := by decide
  have hdescent : baseEnd_6216526 < baseStart_6216526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216607 : List Nat := [1, 1, 2, 5, 2, 1, 4, 2, 5]
def baseStart_6216607 : Nat := 118140960795 + 6216607 * 2 ^ 59
def prefixEnd_6216607 : Nat := 4983230072969 + 3 ^ 40 * 6216607 * 2
def baseEnd_6216607 : Nat := 354678603456118247802539

theorem tailTrace_6216607 : CollatzResearch.WordTrace tailWord_6216607 prefixEnd_6216607 354678603456118247802539 := by
  unfold tailWord_6216607
  simp only [CollatzResearch.WordTrace]
  refine ⟨226738284589302025793504075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151158856392868017195669383 226738284589302025793504075)
  ·
    refine ⟨340107426883953038690256113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226738284589302025793504075 340107426883953038690256113)
    ·
      refine ⟨255080570162964779017692085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340107426883953038690256113 255080570162964779017692085)
      ·
        refine ⟨23913803452777948032908633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 255080570162964779017692085 23913803452777948032908633)
        ·
          refine ⟨17935352589583461024681475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23913803452777948032908633 17935352589583461024681475)
          ·
            refine ⟨26903028884375191537022213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17935352589583461024681475 26903028884375191537022213)
            ·
              refine ⟨5044317915820348413191665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26903028884375191537022213 5044317915820348413191665)
              ·
                refine ⟨3783238436865261309893749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5044317915820348413191665 3783238436865261309893749)
                ·
                  refine ⟨354678603456118247802539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3783238436865261309893749 354678603456118247802539)
                  ·
                    rfl

theorem cell23_6216607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2, 5].length) (baseStart_6216607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216607 prefixEnd_6216607 := by exact prefixLift 6216607
  have htrace : WordTrace (prefixWord ++ tailWord_6216607) baseStart_6216607 baseEnd_6216607 := by
    simpa [prefixWord, tailWord_6216607, baseEnd_6216607] using wordTrace_append hprefix tailTrace_6216607
  have hstable : (prefixWord ++ tailWord_6216607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216607).length < 2 ^ (prefixWord ++ tailWord_6216607).sum := by decide
  have hdescent : baseEnd_6216607 < baseStart_6216607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216637 : List Nat := [1, 4, 1, 2, 4, 2, 1, 1, 2, 5]
def baseStart_6216637 : Nat := 118140960795 + 6216637 * 2 ^ 59
def prefixEnd_6216637 : Nat := 4983230072969 + 3 ^ 40 * 6216637 * 2
def baseEnd_6216637 : Nat := 1064040945174899704282571

theorem tailTrace_6216637 : CollatzResearch.WordTrace tailWord_6216637 prefixEnd_6216637 1064040945174899704282571 := by
  unfold tailWord_6216637
  simp only [CollatzResearch.WordTrace]
  refine ⟨226739378779193340917096165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151159585852795560611397443 226739378779193340917096165)
  ·
    refine ⟨42513633521098751421955531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226739378779193340917096165 42513633521098751421955531)
    ·
      refine ⟨63770450281648127132933297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42513633521098751421955531 63770450281648127132933297)
      ·
        refine ⟨47827837711236095349699973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63770450281648127132933297 47827837711236095349699973)
        ·
          refine ⟨8967719570856767878068745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47827837711236095349699973 8967719570856767878068745)
          ·
            refine ⟨6725789678142575908551559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8967719570856767878068745 6725789678142575908551559)
            ·
              refine ⟨10088684517213863862827339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6725789678142575908551559 10088684517213863862827339)
              ·
                refine ⟨15133026775820795794241009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10088684517213863862827339 15133026775820795794241009)
                ·
                  refine ⟨11349770081865596845680757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15133026775820795794241009 11349770081865596845680757)
                  ·
                    refine ⟨1064040945174899704282571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11349770081865596845680757 1064040945174899704282571)
                    ·
                      rfl

theorem cell23_6216637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_6216637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216637 prefixEnd_6216637 := by exact prefixLift 6216637
  have htrace : WordTrace (prefixWord ++ tailWord_6216637) baseStart_6216637 baseEnd_6216637 := by
    simpa [prefixWord, tailWord_6216637, baseEnd_6216637] using wordTrace_append hprefix tailTrace_6216637
  have hstable : (prefixWord ++ tailWord_6216637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216637).length < 2 ^ (prefixWord ++ tailWord_6216637).sum := by decide
  have hdescent : baseEnd_6216637 < baseStart_6216637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216640 : List Nat := [2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 4]
def baseStart_6216640 : Nat := 118140960795 + 6216640 * 2 ^ 59
def prefixEnd_6216640 : Nat := 4983230072969 + 3 ^ 40 * 6216640 * 2
def baseEnd_6216640 : Nat := 3192124375966662601110199

theorem tailTrace_6216640 : CollatzResearch.WordTrace tailWord_6216640 prefixEnd_6216640 3192124375966662601110199 := by
  unfold tailWord_6216640
  simp only [CollatzResearch.WordTrace]
  refine ⟨113369744099091236214727687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151159658798788314952970249 113369744099091236214727687)
  ·
    refine ⟨170054616148636854322091531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113369744099091236214727687 170054616148636854322091531)
    ·
      refine ⟨255081924222955281483137297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170054616148636854322091531 255081924222955281483137297)
      ·
        refine ⟨191311443167216461112352973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255081924222955281483137297 191311443167216461112352973)
        ·
          refine ⟨71741791187706172917132365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191311443167216461112352973 71741791187706172917132365)
          ·
            refine ⟨26903171695389814843924637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71741791187706172917132365 26903171695389814843924637)
            ·
              refine ⟨10088689385771180566471739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26903171695389814843924637 10088689385771180566471739)
              ·
                refine ⟨15133034078656770849707609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10088689385771180566471739 15133034078656770849707609)
                ·
                  refine ⟨11349775558992578137280707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15133034078656770849707609 11349775558992578137280707)
                  ·
                    refine ⟨17024663338488867205921061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11349775558992578137280707 17024663338488867205921061)
                    ·
                      refine ⟨3192124375966662601110199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17024663338488867205921061 3192124375966662601110199)
                      ·
                        rfl

theorem cell23_6216640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 4].length) (baseStart_6216640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216640 prefixEnd_6216640 := by exact prefixLift 6216640
  have htrace : WordTrace (prefixWord ++ tailWord_6216640) baseStart_6216640 baseEnd_6216640 := by
    simpa [prefixWord, tailWord_6216640, baseEnd_6216640] using wordTrace_append hprefix tailTrace_6216640
  have hstable : (prefixWord ++ tailWord_6216640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216640).length < 2 ^ (prefixWord ++ tailWord_6216640).sum := by decide
  have hdescent : baseEnd_6216640 < baseStart_6216640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216643 : List Nat := [1, 1, 1, 3, 1, 1, 2, 5, 1, 4, 3]
def baseStart_6216643 : Nat := 118140960795 + 6216643 * 2 ^ 59
def prefixEnd_6216643 : Nat := 4983230072969 + 3 ^ 40 * 6216643 * 2
def baseEnd_6216643 : Nat := 3192125916408626089372685

theorem tailTrace_6216643 : CollatzResearch.WordTrace tailWord_6216643 prefixEnd_6216643 3192125916408626089372685 := by
  unfold tailWord_6216643
  simp only [CollatzResearch.WordTrace]
  refine ⟨226739597617171603941814583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151159731744781069294543055 226739597617171603941814583)
  ·
    refine ⟨340109396425757405912721875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226739597617171603941814583 340109396425757405912721875)
    ·
      refine ⟨510164094638636108869082813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340109396425757405912721875 510164094638636108869082813)
      ·
        refine ⟨191311535489488540825906055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 510164094638636108869082813 191311535489488540825906055)
        ·
          refine ⟨286967303234232811238859083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191311535489488540825906055 286967303234232811238859083)
          ·
            refine ⟨430450954851349216858288625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286967303234232811238859083 430450954851349216858288625)
            ·
              refine ⟨322838216138511912643716469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 430450954851349216858288625 322838216138511912643716469)
              ·
                refine ⟨30266082762985491810348419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 322838216138511912643716469 30266082762985491810348419)
                ·
                  refine ⟨45399124144478237715522629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30266082762985491810348419 45399124144478237715522629)
                  ·
                    refine ⟨8512335777089669571660493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45399124144478237715522629 8512335777089669571660493)
                    ·
                      refine ⟨3192125916408626089372685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8512335777089669571660493 3192125916408626089372685)
                      ·
                        rfl

theorem cell23_6216643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4, 3].length) (baseStart_6216643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216643 prefixEnd_6216643 := by exact prefixLift 6216643
  have htrace : WordTrace (prefixWord ++ tailWord_6216643) baseStart_6216643 baseEnd_6216643 := by
    simpa [prefixWord, tailWord_6216643, baseEnd_6216643] using wordTrace_append hprefix tailTrace_6216643
  have hstable : (prefixWord ++ tailWord_6216643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216643).length < 2 ^ (prefixWord ++ tailWord_6216643).sum := by decide
  have hdescent : baseEnd_6216643 < baseStart_6216643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216663 : List Nat := [1, 1, 3, 2, 1, 1, 2, 6, 6]
def baseStart_6216663 : Nat := 118140960795 + 6216663 * 2 ^ 59
def prefixEnd_6216663 : Nat := 4983230072969 + 3 ^ 40 * 6216663 * 2
def baseEnd_6216663 : Nat := 354681798446857334569177

theorem tailTrace_6216663 : CollatzResearch.WordTrace tailWord_6216663 prefixEnd_6216663 354681798446857334569177 := by
  unfold tailWord_6216663
  simp only [CollatzResearch.WordTrace]
  refine ⟨226740327077099147357542643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151160218051399431571695095 226740327077099147357542643)
  ·
    refine ⟨340110490615648721036313965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226740327077099147357542643 340110490615648721036313965)
    ·
      refine ⟨127541433980868270388617737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340110490615648721036313965 127541433980868270388617737)
      ·
        refine ⟨95656075485651202791463303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127541433980868270388617737 95656075485651202791463303)
        ·
          refine ⟨143484113228476804187194955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95656075485651202791463303 143484113228476804187194955)
          ·
            refine ⟨215226169842715206280792433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143484113228476804187194955 215226169842715206280792433)
            ·
              refine ⟨161419627382036404710594325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215226169842715206280792433 161419627382036404710594325)
              ·
                refine ⟨7566545033532956470809109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 161419627382036404710594325 7566545033532956470809109)
                ·
                  refine ⟨354681798446857334569177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7566545033532956470809109 354681798446857334569177)
                  ·
                    rfl

theorem cell23_6216663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 6].length) (baseStart_6216663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216663 prefixEnd_6216663 := by exact prefixLift 6216663
  have htrace : WordTrace (prefixWord ++ tailWord_6216663) baseStart_6216663 baseEnd_6216663 := by
    simpa [prefixWord, tailWord_6216663, baseEnd_6216663] using wordTrace_append hprefix tailTrace_6216663
  have hstable : (prefixWord ++ tailWord_6216663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216663).length < 2 ^ (prefixWord ++ tailWord_6216663).sum := by decide
  have hdescent : baseEnd_6216663 < baseStart_6216663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216674 : List Nat := [3, 3, 3, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_6216674 : Nat := 118140960795 + 6216674 * 2 ^ 59
def prefixEnd_6216674 : Nat := 4983230072969 + 3 ^ 40 * 6216674 * 2
def baseEnd_6216674 : Nat := 3192141834308915468085043

theorem tailTrace_6216674 : CollatzResearch.WordTrace tailWord_6216674 prefixEnd_6216674 3192141834308915468085043 := by
  unfold tailWord_6216674
  simp only [CollatzResearch.WordTrace]
  refine ⟨56685182070014824059048269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151160485520039530824128717 56685182070014824059048269)
  ·
    refine ⟨21256943276255559022143101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56685182070014824059048269 21256943276255559022143101)
    ·
      refine ⟨7971353728595834633303663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21256943276255559022143101 7971353728595834633303663)
      ·
        refine ⟨11957030592893751949955495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7971353728595834633303663 11957030592893751949955495)
        ·
          refine ⟨17935545889340627924933243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11957030592893751949955495 17935545889340627924933243)
          ·
            refine ⟨26903318834010941887399865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17935545889340627924933243 26903318834010941887399865)
            ·
              refine ⟨20177489125508206415549899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26903318834010941887399865 20177489125508206415549899)
              ·
                refine ⟨30266233688262309623324849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20177489125508206415549899 30266233688262309623324849)
                ·
                  refine ⟨22699675266196732217493637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30266233688262309623324849 22699675266196732217493637)
                  ·
                    refine ⟨4256189112411887290780057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22699675266196732217493637 4256189112411887290780057)
                    ·
                      refine ⟨3192141834308915468085043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4256189112411887290780057 3192141834308915468085043)
                      ·
                        rfl

theorem cell23_6216674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_6216674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216674 prefixEnd_6216674 := by exact prefixLift 6216674
  have htrace : WordTrace (prefixWord ++ tailWord_6216674) baseStart_6216674 baseEnd_6216674 := by
    simpa [prefixWord, tailWord_6216674, baseEnd_6216674] using wordTrace_append hprefix tailTrace_6216674
  have hstable : (prefixWord ++ tailWord_6216674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216674).length < 2 ^ (prefixWord ++ tailWord_6216674).sum := by decide
  have hdescent : baseEnd_6216674 < baseStart_6216674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216730 : List Nat := [3, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4]
def baseStart_6216730 : Nat := 118140960795 + 6216730 * 2 ^ 59
def prefixEnd_6216730 : Nat := 4983230072969 + 3 ^ 40 * 6216730 * 2
def baseEnd_6216730 : Nat := 3192170589225567248984785

theorem tailTrace_6216730 : CollatzResearch.WordTrace tailWord_6216730 prefixEnd_6216730 3192170589225567248984785 := by
  unfold tailWord_6216730
  simp only [CollatzResearch.WordTrace]
  refine ⟨56685692691964104450057911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151161847178570945200154429 56685692691964104450057911)
  ·
    refine ⟨85028539037946156675086867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56685692691964104450057911 85028539037946156675086867)
    ·
      refine ⟨127542808556919235012630301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85028539037946156675086867 127542808556919235012630301)
      ·
        refine ⟨47828553208844713129736363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127542808556919235012630301 47828553208844713129736363)
        ·
          refine ⟨71742829813267069694604545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47828553208844713129736363 71742829813267069694604545)
          ·
            refine ⟨53807122359950302270953409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71742829813267069694604545 53807122359950302270953409)
            ·
              refine ⟨40355341769962726703215057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53807122359950302270953409 40355341769962726703215057)
              ·
                refine ⟨30266506327472045027411293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40355341769962726703215057 30266506327472045027411293)
                ·
                  refine ⟨11349939872802016885279235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30266506327472045027411293 11349939872802016885279235)
                  ·
                    refine ⟨17024909809203025327918853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11349939872802016885279235 17024909809203025327918853)
                    ·
                      refine ⟨3192170589225567248984785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17024909809203025327918853 3192170589225567248984785)
                      ·
                        rfl

theorem cell23_6216730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_6216730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216730 prefixEnd_6216730 := by exact prefixLift 6216730
  have htrace : WordTrace (prefixWord ++ tailWord_6216730) baseStart_6216730 baseEnd_6216730 := by
    simpa [prefixWord, tailWord_6216730, baseEnd_6216730] using wordTrace_append hprefix tailTrace_6216730
  have hstable : (prefixWord ++ tailWord_6216730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216730).length < 2 ^ (prefixWord ++ tailWord_6216730).sum := by decide
  have hdescent : baseEnd_6216730 < baseStart_6216730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216747 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 5, 2, 2]
def baseStart_6216747 : Nat := 118140960795 + 6216747 * 2 ^ 59
def prefixEnd_6216747 : Nat := 4983230072969 + 3 ^ 40 * 6216747 * 2
def baseEnd_6216747 : Nat := 3192179318396693682472207

theorem tailTrace_6216747 : CollatzResearch.WordTrace tailWord_6216747 prefixEnd_6216747 3192179318396693682472207 := by
  unfold tailWord_6216747
  simp only [CollatzResearch.WordTrace]
  refine ⟨226743390808794829703600495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151162260539196553135733663 226743390808794829703600495)
  ·
    refine ⟨340115086213192244555400743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226743390808794829703600495 340115086213192244555400743)
    ·
      refine ⟨510172629319788366833101115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340115086213192244555400743 510172629319788366833101115)
      ·
        refine ⟨765258943979682550249651673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510172629319788366833101115 765258943979682550249651673)
        ·
          refine ⟨573944207984761912687238755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 765258943979682550249651673 573944207984761912687238755)
          ·
            refine ⟨860916311977142869030858133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573944207984761912687238755 860916311977142869030858133)
            ·
              refine ⟨40355452123928571985821475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 860916311977142869030858133 40355452123928571985821475)
              ·
                refine ⟨60533178185892857978732213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40355452123928571985821475 60533178185892857978732213)
                ·
                  refine ⟨5674985454927455435506145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60533178185892857978732213 5674985454927455435506145)
                  ·
                    refine ⟨4256239091195591576629609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5674985454927455435506145 4256239091195591576629609)
                    ·
                      refine ⟨3192179318396693682472207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4256239091195591576629609 3192179318396693682472207)
                      ·
                        rfl

theorem cell23_6216747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5, 2, 2].length) (baseStart_6216747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216747 prefixEnd_6216747 := by exact prefixLift 6216747
  have htrace : WordTrace (prefixWord ++ tailWord_6216747) baseStart_6216747 baseEnd_6216747 := by
    simpa [prefixWord, tailWord_6216747, baseEnd_6216747] using wordTrace_append hprefix tailTrace_6216747
  have hstable : (prefixWord ++ tailWord_6216747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216747).length < 2 ^ (prefixWord ++ tailWord_6216747).sum := by decide
  have hdescent : baseEnd_6216747 < baseStart_6216747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216753 : List Nat := [1, 2, 2, 3, 1, 2, 1, 11]
def baseStart_6216753 : Nat := 118140960795 + 6216753 * 2 ^ 59
def prefixEnd_6216753 : Nat := 4983230072969 + 3 ^ 40 * 6216753 * 2
def baseEnd_6216753 : Nat := 118228977751134098481377

theorem tailTrace_6216753 : CollatzResearch.WordTrace tailWord_6216753 prefixEnd_6216753 118228977751134098481377 := by
  unfold tailWord_6216753
  simp only [CollatzResearch.WordTrace]
  refine ⟨226743609646773092728318913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151162406431182061818879275 226743609646773092728318913)
  ·
    refine ⟨170057707235079819546239185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226743609646773092728318913 170057707235079819546239185)
    ·
      refine ⟨127543280426309864659679389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170057707235079819546239185 127543280426309864659679389)
      ·
        refine ⟨47828730159866199247379771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127543280426309864659679389 47828730159866199247379771)
        ·
          refine ⟨71743095239799298871069657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47828730159866199247379771 71743095239799298871069657)
          ·
            refine ⟨53807321429849474153302243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71743095239799298871069657 53807321429849474153302243)
            ·
              refine ⟨80710982144774211229953365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53807321429849474153302243 80710982144774211229953365)
              ·
                refine ⟨118228977751134098481377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 80710982144774211229953365 118228977751134098481377)
                ·
                  rfl

theorem cell23_6216753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 11].length) (baseStart_6216753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216753 prefixEnd_6216753 := by exact prefixLift 6216753
  have htrace : WordTrace (prefixWord ++ tailWord_6216753) baseStart_6216753 baseEnd_6216753 := by
    simpa [prefixWord, tailWord_6216753, baseEnd_6216753] using wordTrace_append hprefix tailTrace_6216753
  have hstable : (prefixWord ++ tailWord_6216753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216753).length < 2 ^ (prefixWord ++ tailWord_6216753).sum := by decide
  have hdescent : baseEnd_6216753 < baseStart_6216753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216760 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 3, 2, 4]
def baseStart_6216760 : Nat := 118140960795 + 6216760 * 2 ^ 59
def prefixEnd_6216760 : Nat := 4983230072969 + 3 ^ 40 * 6216760 * 2
def baseEnd_6216760 : Nat := 3192185993645202131609647

theorem tailTrace_6216760 : CollatzResearch.WordTrace tailWord_6216760 prefixEnd_6216760 3192185993645202131609647 := by
  unfold tailWord_6216760
  simp only [CollatzResearch.WordTrace]
  refine ⟨113371932478873866461911867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151162576638498488615882489 113371932478873866461911867)
  ·
    refine ⟨170057898718310799692867801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113371932478873866461911867 170057898718310799692867801)
    ·
      refine ⟨127543424038733099769650851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170057898718310799692867801 127543424038733099769650851)
      ·
        refine ⟨191315136058099649654476277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127543424038733099769650851 191315136058099649654476277)
        ·
          refine ⟨17935794005446842155107151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 191315136058099649654476277 17935794005446842155107151)
          ·
            refine ⟨26903691008170263232660727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17935794005446842155107151 26903691008170263232660727)
            ·
              refine ⟨40355536512255394848991091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26903691008170263232660727 40355536512255394848991091)
              ·
                refine ⟨60533304768383092273486637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40355536512255394848991091 60533304768383092273486637)
                ·
                  refine ⟨22699989288143659602557489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60533304768383092273486637 22699989288143659602557489)
                  ·
                    refine ⟨17024991966107744701918117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22699989288143659602557489 17024991966107744701918117)
                    ·
                      refine ⟨3192185993645202131609647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17024991966107744701918117 3192185993645202131609647)
                      ·
                        rfl

theorem cell23_6216760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_6216760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216760 prefixEnd_6216760 := by exact prefixLift 6216760
  have htrace : WordTrace (prefixWord ++ tailWord_6216760) baseStart_6216760 baseEnd_6216760 := by
    simpa [prefixWord, tailWord_6216760, baseEnd_6216760] using wordTrace_append hprefix tailTrace_6216760
  have hstable : (prefixWord ++ tailWord_6216760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216760).length < 2 ^ (prefixWord ++ tailWord_6216760).sum := by decide
  have hdescent : baseEnd_6216760 < baseStart_6216760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216764 : List Nat := [2, 2, 2, 2, 2, 3, 3, 1, 1, 1, 4]
def baseStart_6216764 : Nat := 118140960795 + 6216764 * 2 ^ 59
def prefixEnd_6216764 : Nat := 4983230072969 + 3 ^ 40 * 6216764 * 2
def baseEnd_6216764 : Nat := 3192188047567820115959629

theorem tailTrace_6216764 : CollatzResearch.WordTrace tailWord_6216764 prefixEnd_6216764 3192188047567820115959629 := by
  unfold tailWord_6216764
  simp only [CollatzResearch.WordTrace]
  refine ⟨113372005424866620803484673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151162673899822161071312897 113372005424866620803484673)
  ·
    refine ⟨85029004068649965602613505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113372005424866620803484673 85029004068649965602613505)
    ·
      refine ⟨63771753051487474201960129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85029004068649965602613505 63771753051487474201960129)
      ·
        refine ⟨47828814788615605651470097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63771753051487474201960129 47828814788615605651470097)
        ·
          refine ⟨35871611091461704238602573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47828814788615605651470097 35871611091461704238602573)
          ·
            refine ⟨13451854159298139089475965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35871611091461704238602573 13451854159298139089475965)
            ·
              refine ⟨5044445309736802158553487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13451854159298139089475965 5044445309736802158553487)
              ·
                refine ⟨7566667964605203237830231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5044445309736802158553487 7566667964605203237830231)
                ·
                  refine ⟨11350001946907804856745347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7566667964605203237830231 11350001946907804856745347)
                  ·
                    refine ⟨17025002920361707285118021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11350001946907804856745347 17025002920361707285118021)
                    ·
                      refine ⟨3192188047567820115959629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17025002920361707285118021 3192188047567820115959629)
                      ·
                        rfl

theorem cell23_6216764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_6216764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216764 prefixEnd_6216764 := by exact prefixLift 6216764
  have htrace : WordTrace (prefixWord ++ tailWord_6216764) baseStart_6216764 baseEnd_6216764 := by
    simpa [prefixWord, tailWord_6216764, baseEnd_6216764] using wordTrace_append hprefix tailTrace_6216764
  have hstable : (prefixWord ++ tailWord_6216764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216764).length < 2 ^ (prefixWord ++ tailWord_6216764).sum := by decide
  have hdescent : baseEnd_6216764 < baseStart_6216764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216780 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 5, 3, 3]
def baseStart_6216780 : Nat := 118140960795 + 6216780 * 2 ^ 59
def prefixEnd_6216780 : Nat := 4983230072969 + 3 ^ 40 * 6216780 * 2
def baseEnd_6216780 : Nat := 3192196263258292053359555

theorem tailTrace_6216780 : CollatzResearch.WordTrace tailWord_6216780 prefixEnd_6216780 3192196263258292053359555 := by
  unfold tailWord_6216780
  simp only [CollatzResearch.WordTrace]
  refine ⟨113372297208837638169775897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151163062945116850893034529 113372297208837638169775897)
  ·
    refine ⟨85029222906628228627331923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113372297208837638169775897 85029222906628228627331923)
    ·
      refine ⟨127543834359942342940997885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85029222906628228627331923 127543834359942342940997885)
      ·
        refine ⟨47828937884978378602874207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127543834359942342940997885 47828937884978378602874207)
        ·
          refine ⟨71743406827467567904311311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47828937884978378602874207 71743406827467567904311311)
          ·
            refine ⟨107615110241201351856466967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71743406827467567904311311 107615110241201351856466967)
            ·
              refine ⟨161422665361802027784700451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107615110241201351856466967 161422665361802027784700451)
              ·
                refine ⟨242133998042703041677050677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161422665361802027784700451 242133998042703041677050677)
                ·
                  refine ⟨22700062316503410157223501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 242133998042703041677050677 22700062316503410157223501)
                  ·
                    refine ⟨8512523368688778808958813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22700062316503410157223501 8512523368688778808958813)
                    ·
                      refine ⟨3192196263258292053359555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8512523368688778808958813 3192196263258292053359555)
                      ·
                        rfl

theorem cell23_6216780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_6216780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216780 prefixEnd_6216780 := by exact prefixLift 6216780
  have htrace : WordTrace (prefixWord ++ tailWord_6216780) baseStart_6216780 baseEnd_6216780 := by
    simpa [prefixWord, tailWord_6216780, baseEnd_6216780] using wordTrace_append hprefix tailTrace_6216780
  have hstable : (prefixWord ++ tailWord_6216780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216780).length < 2 ^ (prefixWord ++ tailWord_6216780).sum := by decide
  have hdescent : baseEnd_6216780 < baseStart_6216780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216798 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_6216798 : Nat := 118140960795 + 6216798 * 2 ^ 59
def prefixEnd_6216798 : Nat := 4983230072969 + 3 ^ 40 * 6216798 * 2
def baseEnd_6216798 : Nat := 3192205505910072982934473

theorem tailTrace_6216798 : CollatzResearch.WordTrace tailWord_6216798 prefixEnd_6216798 3192205505910072982934473 := by
  unfold tailWord_6216798
  simp only [CollatzResearch.WordTrace]
  refine ⟨28343156366451258176713381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151163500621073376942471365 28343156366451258176713381)
  ·
    refine ⟨5314341818709610908133759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28343156366451258176713381 5314341818709610908133759)
    ·
      refine ⟨7971512728064416362200639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5314341818709610908133759 7971512728064416362200639)
      ·
        refine ⟨11957269092096624543300959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7971512728064416362200639 11957269092096624543300959)
        ·
          refine ⟨17935903638144936814951439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11957269092096624543300959 17935903638144936814951439)
          ·
            refine ⟨26903855457217405222427159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17935903638144936814951439 26903855457217405222427159)
            ·
              refine ⟨40355783185826107833640739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26903855457217405222427159 40355783185826107833640739)
              ·
                refine ⟨60533674778739161750461109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40355783185826107833640739 60533674778739161750461109)
                ·
                  refine ⟨5675032010506796414105729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60533674778739161750461109 5675032010506796414105729)
                  ·
                    refine ⟨4256274007880097310579297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5675032010506796414105729 4256274007880097310579297)
                    ·
                      refine ⟨3192205505910072982934473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4256274007880097310579297 3192205505910072982934473)
                      ·
                        rfl

theorem cell23_6216798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_6216798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216798 prefixEnd_6216798 := by exact prefixLift 6216798
  have htrace : WordTrace (prefixWord ++ tailWord_6216798) baseStart_6216798 baseEnd_6216798 := by
    simpa [prefixWord, tailWord_6216798, baseEnd_6216798] using wordTrace_append hprefix tailTrace_6216798
  have hstable : (prefixWord ++ tailWord_6216798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216798).length < 2 ^ (prefixWord ++ tailWord_6216798).sum := by decide
  have hdescent : baseEnd_6216798 < baseStart_6216798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216871 : List Nat := [1, 1, 6, 2, 1, 1, 1, 2, 4, 2, 2]
def baseStart_6216871 : Nat := 118140960795 + 6216871 * 2 ^ 59
def prefixEnd_6216871 : Nat := 4983230072969 + 3 ^ 40 * 6216871 * 2
def baseEnd_6216871 : Nat := 3192242989997851197321637

theorem tailTrace_6216871 : CollatzResearch.WordTrace tailWord_6216871 prefixEnd_6216871 3192242989997851197321637 := by
  unfold tailWord_6216871
  simp only [CollatzResearch.WordTrace]
  refine ⟨226747913460345598881114467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151165275640230399254076311 226747913460345598881114467)
  ·
    refine ⟨340121870190518398321671701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226747913460345598881114467 340121870190518398321671701)
    ·
      refine ⟨15943212665180549921328361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 340121870190518398321671701 15943212665180549921328361)
      ·
        refine ⟨11957409498885412440996271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15943212665180549921328361 11957409498885412440996271)
        ·
          refine ⟨17936114248328118661494407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11957409498885412440996271 17936114248328118661494407)
          ·
            refine ⟨26904171372492177992241611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17936114248328118661494407 26904171372492177992241611)
            ·
              refine ⟨40356257058738266988362417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26904171372492177992241611 40356257058738266988362417)
              ·
                refine ⟨30267192794053700241271813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40356257058738266988362417 30267192794053700241271813)
                ·
                  refine ⟨5675098648885068795238465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30267192794053700241271813 5675098648885068795238465)
                  ·
                    refine ⟨4256323986663801596428849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5675098648885068795238465 4256323986663801596428849)
                    ·
                      refine ⟨3192242989997851197321637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4256323986663801596428849 3192242989997851197321637)
                      ·
                        rfl

theorem cell23_6216871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_6216871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216871 prefixEnd_6216871 := by exact prefixLift 6216871
  have htrace : WordTrace (prefixWord ++ tailWord_6216871) baseStart_6216871 baseEnd_6216871 := by
    simpa [prefixWord, tailWord_6216871, baseEnd_6216871] using wordTrace_append hprefix tailTrace_6216871
  have hstable : (prefixWord ++ tailWord_6216871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216871).length < 2 ^ (prefixWord ++ tailWord_6216871).sum := by decide
  have hdescent : baseEnd_6216871 < baseStart_6216871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216874 : List Nat := [3, 1, 5, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_6216874 : Nat := 118140960795 + 6216874 * 2 ^ 59
def prefixEnd_6216874 : Nat := 4983230072969 + 3 ^ 40 * 6216874 * 2
def baseEnd_6216874 : Nat := 3192244530439814685584123

theorem tailTrace_6216874 : CollatzResearch.WordTrace tailWord_6216874 prefixEnd_6216874 3192244530439814685584123 := by
  unfold tailWord_6216874
  simp only [CollatzResearch.WordTrace]
  refine ⟨56687005719833682598368419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151165348586223153595649117 56687005719833682598368419)
  ·
    refine ⟨85030508579750523897552629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56687005719833682598368419 85030508579750523897552629)
    ·
      refine ⟨7971610179351611615395559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85030508579750523897552629 7971610179351611615395559)
      ·
        refine ⟨11957415269027417423093339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7971610179351611615395559 11957415269027417423093339)
        ·
          refine ⟨17936122903541126134640009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11957415269027417423093339 17936122903541126134640009)
          ·
            refine ⟨13452092177655844600980007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17936122903541126134640009 13452092177655844600980007)
            ·
              refine ⟨20178138266483766901470011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13452092177655844600980007 20178138266483766901470011)
              ·
                refine ⟨30267207399725650352205017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20178138266483766901470011 30267207399725650352205017)
                ·
                  refine ⟨22700405549794237764153763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30267207399725650352205017 22700405549794237764153763)
                  ·
                    refine ⟨34050608324691356646230645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22700405549794237764153763 34050608324691356646230645)
                    ·
                      refine ⟨3192244530439814685584123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34050608324691356646230645 3192244530439814685584123)
                      ·
                        rfl

theorem cell23_6216874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_6216874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216874 prefixEnd_6216874 := by exact prefixLift 6216874
  have htrace : WordTrace (prefixWord ++ tailWord_6216874) baseStart_6216874 baseEnd_6216874 := by
    simpa [prefixWord, tailWord_6216874, baseEnd_6216874] using wordTrace_append hprefix tailTrace_6216874
  have hstable : (prefixWord ++ tailWord_6216874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216874).length < 2 ^ (prefixWord ++ tailWord_6216874).sum := by decide
  have hdescent : baseEnd_6216874 < baseStart_6216874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216894 : List Nat := [4, 2, 1, 1, 3, 3, 1, 1, 7]
def baseStart_6216894 : Nat := 118140960795 + 6216894 * 2 ^ 59
def prefixEnd_6216894 : Nat := 4983230072969 + 3 ^ 40 * 6216894 * 2
def baseEnd_6216894 : Nat := 354694977783656067481559

theorem tailTrace_6216894 : CollatzResearch.WordTrace tailWord_6216894 prefixEnd_6216894 354694977783656067481559 := by
  unfold tailWord_6216894
  simp only [CollatzResearch.WordTrace]
  refine ⟨28343594042407784226150217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151165834892841515872801157 28343594042407784226150217)
  ·
    refine ⟨21257695531805838169612663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28343594042407784226150217 21257695531805838169612663)
    ·
      refine ⟨31886543297708757254418995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21257695531805838169612663 31886543297708757254418995)
      ·
        refine ⟨47829814946563135881628493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31886543297708757254418995 47829814946563135881628493)
        ·
          refine ⟨17936180604961175955610685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47829814946563135881628493 17936180604961175955610685)
          ·
            refine ⟨6726067726860440983354007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17936180604961175955610685 6726067726860440983354007)
            ·
              refine ⟨10089101590290661475031011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6726067726860440983354007 10089101590290661475031011)
              ·
                refine ⟨15133652385435992212546517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10089101590290661475031011 15133652385435992212546517)
                ·
                  refine ⟨354694977783656067481559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15133652385435992212546517 354694977783656067481559)
                  ·
                    rfl

theorem cell23_6216894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_6216894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216894 prefixEnd_6216894 := by exact prefixLift 6216894
  have htrace : WordTrace (prefixWord ++ tailWord_6216894) baseStart_6216894 baseEnd_6216894 := by
    simpa [prefixWord, tailWord_6216894, baseEnd_6216894] using wordTrace_append hprefix tailTrace_6216894
  have hstable : (prefixWord ++ tailWord_6216894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216894).length < 2 ^ (prefixWord ++ tailWord_6216894).sum := by decide
  have hdescent : baseEnd_6216894 < baseStart_6216894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6216927 : List Nat := [1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 4]
def baseStart_6216927 : Nat := 118140960795 + 6216927 * 2 ^ 59
def prefixEnd_6216927 : Nat := 4983230072969 + 3 ^ 40 * 6216927 * 2
def baseEnd_6216927 : Nat := 3192271744914502978221379

theorem tailTrace_6216927 : CollatzResearch.WordTrace tailWord_6216927 prefixEnd_6216927 3192271744914502978221379 := by
  unfold tailWord_6216927
  simp only [CollatzResearch.WordTrace]
  refine ⟨226749955948142720445153035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151166637298761813630102023 226749955948142720445153035)
  ·
    refine ⟨340124933922214080667729553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226749955948142720445153035 340124933922214080667729553)
    ·
      refine ⟨255093700441660560500797165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340124933922214080667729553 255093700441660560500797165)
      ·
        refine ⟨95660137665622710187798937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255093700441660560500797165 95660137665622710187798937)
        ·
          refine ⟨71745103249217032640849203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95660137665622710187798937 71745103249217032640849203)
          ·
            refine ⟨107617654873825548961273805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71745103249217032640849203 107617654873825548961273805)
            ·
              refine ⟨40356620577684580860477677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107617654873825548961273805 40356620577684580860477677)
              ·
                refine ⟨15133732716631717822679129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40356620577684580860477677 15133732716631717822679129)
                ·
                  refine ⟨11350299537473788367009347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15133732716631717822679129 11350299537473788367009347)
                  ·
                    refine ⟨17025449306210682550514021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11350299537473788367009347 17025449306210682550514021)
                    ·
                      refine ⟨3192271744914502978221379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17025449306210682550514021 3192271744914502978221379)
                      ·
                        rfl

theorem cell23_6216927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_6216927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6216927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6216927 prefixEnd_6216927 := by exact prefixLift 6216927
  have htrace : WordTrace (prefixWord ++ tailWord_6216927) baseStart_6216927 baseEnd_6216927 := by
    simpa [prefixWord, tailWord_6216927, baseEnd_6216927] using wordTrace_append hprefix tailTrace_6216927
  have hstable : (prefixWord ++ tailWord_6216927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6216927).length < 2 ^ (prefixWord ++ tailWord_6216927).sum := by decide
  have hdescent : baseEnd_6216927 < baseStart_6216927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6216927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
